Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep Linking.
Require Import Clight Ctypes Cop SimplLocalsproof.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SepCKLR.

(* Define a language interface with memory abstracted out *)
Record d_query :=
  dq {
      dq_vf: val;
      dq_sg: signature;
      dq_args: list val;
    }.
Record d_reply :=
  dr {
      dr_retval: val;
    }.
Canonical Structure li_d :=
  {|
  query := d_query;
  reply := d_reply;
  entry := dq_vf;
  |}.
Inductive q_rel: query li_d -> query li_c -> mem -> Prop:=
| q_rel_intro:
    forall vf sg args m,
      q_rel ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|})
            ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|}) m.
Inductive r_rel: reply li_d -> reply li_c -> mem -> Prop:=
  r_rel_intro:
    forall ret m,
      r_rel ({|dr_retval:=ret|})
            ({|cr_retval:=ret;cr_mem:=m|}) m.
Inductive qr_rel_list: list (query li_d * reply li_d) -> list (query li_c * reply li_c) -> Prop:=
| qr_rel_nil: qr_rel_list nil nil
| qr_rel_cons:
    forall dq dr cq cr ds cs m m',
      q_rel dq cq m ->
      r_rel dr cr m' ->
      qr_rel_list ds cs ->
      qr_rel_list ((dq, dr)::ds) ((cq, cr)::cs).
Inductive li_rel: (query li_d * reply li_d) -> (query li_c * reply li_c) -> Prop:=
| rel_intro:
    forall vf sg args ret m,
      li_rel ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|}, {|dr_retval:=ret|})
             ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|}, {|cr_retval:=ret;cr_mem:=m|}).

Program Definition li_dc: li_d --o li_c :=
  {|
  has '(d, c) := li_rel d c
  |}.
Next Obligation.
  destruct d1 as [dq1 dr1]. destruct d2 as [dq2 dr2].
  destruct c1 as [cq1 cr1]. destruct c2 as [cq2 cr2].
  intuition.
  - inv H. inv H0. f_equal. exploit H3. f_equal. inversion 1. auto.
  - inv H. inv H0. inv H1. auto.
Defined.

Inductive exec {liA liB: language_interface} (σ: !liA --o !liB): query liB -> list (token liA) -> reply liB -> Prop:=
| exec_intro: forall t q r,
    has σ (t, (q, r) :: nil) ->
    exec σ q t r.

Program Definition next {liA liB: language_interface} (σ : !liA --o !liB) w qx rx : !liA --o !liB :=
  {|
  has '(s, t) := has σ (w ++ s, (qx, rx)::t);
  |}.
Next Obligation.
  pose proof (has_coh _ _ _ _ H H0). cbn in H1. clear H H0.
  intros Ht. edestruct H1 as [Hr Hl].
  apply (@app_coh liA). apply Ht.
  split. inversion Hr. subst. apply H5. auto.
  intro. exploit Hl. f_equal. auto. apply app_inv_head.
Qed.

Module Abs.
  Section ABS_SEMANTICS.
    (* the linked system has type liA ->> liB *)
    Context {liA liB: language_interface} (Σ: Genv.symtbl -> !liA --o !liA) (C: semantics liB liB).
    Variable li_rel: (query liA * reply liA) -> (query liB * reply liB) -> Prop.
    Variable se: Genv.symtbl.

    Variant state : Type :=
    | st (s: Smallstep.state C) (σ: !liA --o !liA)
    (* s and σ constitute the state after the external call *)
    | ext (s: Smallstep.state C) (t: list (token liA)) (σ: !liA --o !liA).

    Inductive step: state -> trace -> state -> Prop :=
    | step_internal: forall s s' t σ,
        Step (C se) s t s' ->
        step (st s σ) t (st s' σ)
    | step_at_external: forall s s' qa ra qb rb σ w,
        Smallstep.at_external (C se) s qb ->
        Smallstep.after_external (C se) s rb s' ->
        (* (w, r) may not be the "right" execution. In other words, [next σ w q
           r] might be empty.  But that's fine because it's still related to s
           per correctness *)
        exec σ qa w ra ->
        (* drop the memory and make a query. take the reply and attach the same
        memory to it *)
        (* this can be further refined by giving the reply a new memory as long
        as it's larger than the old one *)
        li_rel (qa, ra) (qb, rb) ->
        step (st s σ) E0 (ext s' w (next σ w qa ra))
    | step_after_external: forall s σ,
        step (ext s nil σ) E0 (st s σ).

    Inductive initial_state: query liB -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (C se) q s ->
        initial_state q (st s (Σ se)).

    Inductive at_external: state -> query liA -> Prop :=
    | ext_at_external: forall s q r t σ,
        at_external (ext s ((q, r) :: t) σ) q.
    Inductive after_external: state -> reply liA -> state -> Prop :=
    | ext_after_external: forall s q r t σ,
        after_external (ext s ((q, r) :: t) σ) r (ext s t σ).

    Inductive final_state: state -> reply liB -> Prop :=
    | final_state_intro: forall s r σ,
        Smallstep.final_state (C se) s r ->
        final_state (st s σ) r.

    Definition lts : lts liA liB state :=
      {|
      Smallstep.step _ := step;
      Smallstep.valid_query := Smallstep.valid_query (C se);
      Smallstep.initial_state := initial_state;
      Smallstep.at_external := at_external;
      Smallstep.after_external := after_external;
      Smallstep.final_state := final_state;
      Smallstep.globalenv := Smallstep.globalenv (C se);
      |}.
  End ABS_SEMANTICS.
  Definition semantics {liA liB: language_interface} skel li_rel (Σ: Genv.symtbl -> !liA --o !liA) (C: Smallstep.semantics liB liB) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts Σ C li_rel se;
    |}.
  Definition c_semantics sk (C: Clight.program) (Σ: Genv.symtbl -> !li_d --o !li_d) : Smallstep.semantics li_d li_c :=
    semantics sk li_rel Σ (semantics1 C).
End Abs.

Module Impl.
  Section IMPL_SEMANTICS.
    Context {liA liB: language_interface} (σ: Genv.symtbl -> !liA --o liB) (C: semantics liB liB).
    Variable se: Genv.symtbl.

    Variant state :=
    | st (s: Smallstep.state C)
    | ext (s: Smallstep.state C) (t: list (token liA)).

    Inductive step: state -> trace -> state -> Prop :=
    | step_internal: forall s s' t,
        Step (C se) s t s' ->
        step (st s) t (st s')
    | step_at_external: forall s s' q r t,
        Smallstep.at_external (C se) s q ->
        Smallstep.after_external (C se) s r s' ->
        has (σ se) (t, (q, r)) ->
        step (st s) E0 (ext s' t)
    | step_after_external: forall s,
        step (ext s nil) E0 (st s).

    Inductive initial_state: query liB -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (C se) q s ->
        initial_state q (st s).

    Inductive at_external: state -> query liA -> Prop :=
    | ext_at_external: forall s q r t,
        at_external (ext s ((q, r) :: t)) q.
    Inductive after_external: state -> reply liA -> state -> Prop :=
    | ext_after_external: forall s q r t,
        after_external (ext s ((q, r) :: t)) r (ext s t).

    Inductive final_state: state -> reply liB -> Prop :=
    | final_state_intro: forall s r,
        Smallstep.final_state (C se) s r ->
        final_state (st s) r.

    Definition lts : lts liA liB state :=
      {|
      Smallstep.step _ := step;
      Smallstep.valid_query := Smallstep.valid_query (C se);
      Smallstep.initial_state := initial_state;
      Smallstep.at_external := at_external;
      Smallstep.after_external := after_external;
      Smallstep.final_state := final_state;
      Smallstep.globalenv := Smallstep.globalenv (C se);
      |}.
  End IMPL_SEMANTICS.
  Definition semantics {liA liB: language_interface} skel (σ: Genv.symtbl -> !liB --o liA) (C: Smallstep.semantics liA liA) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts σ C se;
    |}.
  Definition c_semantics sk (C: Clight.program) (p: Clight.program): Smallstep.semantics li_d li_c :=
    semantics sk (fun se => clight_bigstep p se @ !li_dc) (semantics1 C).
End Impl.

Inductive module_var (ge: genv) : block -> Z -> Prop :=
| module_var_intro id b (v : globvar type) (ty : type):
    Genv.find_symbol ge id = Some b ->
    Genv.find_def ge b = Some (Gvar v) ->
    ty = gvar_info v ->
    module_var ge b (sizeof ge ty).

Record prog_sim (p: Clight.program) (Σ: Genv.symtbl -> !li_d --o !li_d) :=
  {
  mspec_rel :> (!li_d --o !li_d) -> mem -> Prop;
  init_mem : mem -> Prop;

  mem_scope : forall m m' σ se,
      Genv.valid_for (AST.erase_program p) se ->
      Mem.unchanged_on (module_var (Clight.globalenv se p)) m m' ->
      mspec_rel σ m ->
      mspec_rel σ m';
  simulation: forall σ dq dr t m se,
      Genv.valid_for (AST.erase_program p) se ->
      mspec_rel σ m -> exec σ dq t dr ->
      exists cr cq m',
        q_rel dq cq m /\ r_rel dr cr m' /\
        has (clight_bigstep p se @ !li_dc) (t, (cq, cr)) /\
        Mem.unchanged_on (fun b ofs => ~ module_var (Clight.globalenv se p) b ofs) m m' /\
        mspec_rel (next σ t dq dr) m';
  correct_cond: forall m se,
      Genv.valid_for (AST.erase_program p) se ->
      init_mem m -> mspec_rel (Σ se) m;
  }.

Definition get_mem (s: state) : mem :=
  match s with
  | State _ _ _ _ _ m => m
  | Callstate _ _ _ m => m
  | Returnstate _ _ m => m
  end.

Section SepcCKLR.
  (* A CKLR dedicated to Clight programs *)
  Variable p: Clight.program.
  Variable se: Genv.symtbl.
  Let vars: block -> Z -> Prop := module_var (globalenv se p).
  (* the target memory and local variables that belong to the component
     constitute the klr index *)
  Inductive sepc_world :=
    sepcw (m: mem) (Hvb: forall b ofs, vars b ofs -> Mem.valid_block m b).
  Inductive sepc_acc: relation sepc_world :=
    acc_intro m1 m2 Hm1 Hm2:
      (* External call into the component only touches its own variables  *)
      Mem.unchanged_on (fun b ofs => ~ vars b ofs) m1 m2 ->
      sepc_acc (sepcw m1 Hm1) (sepcw m2 Hm2).

  Inductive sepc_mm: sepc_world -> mem -> mem -> Prop :=
    match_intro: forall m m1 m2 Hvb,
      (* source memory extends into target memory *)
      Mem.extends m1 m2 ->
      (* local variables of the component are only modified during external
         calls so they don't change in the course of internal steps*)
      Mem.unchanged_on vars m m2 ->
      (* m1 and locals don't have blocks in common *)
      (forall b ofs, vars b ofs -> ~ Mem.perm m1 b ofs Max Nonempty) ->
      sepc_mm (sepcw m Hvb) m1 m2.

  Instance sepc_acc_preo:
    PreOrder sepc_acc.
  Proof.
    split.
    - intros [m]. constructor.
      apply Mem.unchanged_on_refl.
    - intros [m1] [m2] [m3].
      inversion 1. subst.
      inversion 1. subst.
      constructor.
      eapply Mem.unchanged_on_trans; eauto.
  Qed.

  Program Definition sepc: cklr :=
    {|
    world := sepc_world;
    wacc := sepc_acc;
    mi w := inject_id;
    match_mem w := sepc_mm w;
    (* a cheap workaround *)
    match_stbls w se1 se2 := se1 = se2 /\ se = se1;
    |}.

  (* mi_acc *)
  Next Obligation.
    repeat rstep. apply inject_incr_refl.
  Qed.
  (* match_stbls_acc *)
  Next Obligation.
    rauto.
  Qed.
  (* match_stbls_proj *)
  Next Obligation.
    intros se1 se2 [<- <-]. apply Genv.match_stbls_id.
  Qed.
  (* match_stbls_nextblock *)
  Next Obligation.
    erewrite <- Mem.mext_next; eauto.
    inv H0. auto.
  Qed.
  (* cklr_alloc *)
  Next Obligation.
    intros [ ] m1 m2 Hm lo hi. inv Hm.
    destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn: Hm1.
    edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
    rewrite Hm2'.
    eexists (sepcw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
    - intros. specialize (Hvb _ _ H).
      specialize (H2 _ _ H). intros Hp. apply H2.
      eapply Mem.perm_alloc_4 in Hp; eauto.
      eapply Mem.alloc_result in Hm1. subst.
      exploit Mem.valid_block_unchanged_on; eauto.
      erewrite Mem.mext_next; eauto.
  Qed.
  (* cklr_free *)
  Next Obligation.
    intros [ ] m1 m2 Hm [[b lo] hi] r2 Hr. inv Hm.
    apply coreflexivity in Hr. subst. simpl. red.
    destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. constructor.
    eexists (sepcw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.free_unchanged_on; eauto.
      intros ofs Hofs Hv. specialize (H2 _ _ Hv). apply H2.
      exploit Mem.free_range_perm. apply Hm1'. eauto.
      intros Hp. eapply Mem.perm_cur_max.
      eapply Mem.perm_implies. apply Hp. constructor.
    - intros. specialize (H2 _ _ H).
      intros Hp. apply H2.
      eapply Mem.perm_free_3; eauto.
  Qed.
  Require Import Extends.
  (* cklr_load *)
  Next Obligation.
    intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp. inv Hm.
    apply coreflexivity in Hp; subst. simpl. red.
    destruct (Mem.load chunk m1 b ofs) as [v1|] eqn:Hv1; [|constructor].
    edestruct Mem.load_extends as (v2 & Hv2 & Hv); eauto.
    rewrite Hv2. rewrite val_inject_lessdef_eqrel. rauto.
  Qed.
  (* cklr_store *)
  Next Obligation.
    intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp v1 v2 Hv. inv Hm.
    apply coreflexivity in Hp; subst. simpl. red.
    destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
    apply val_inject_lessdef in Hv.
    edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. constructor.
    eexists (sepcw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.store_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H2 _ _ Hp). apply H2.
      exploit Mem.store_valid_access_3. apply Hm1'.
      unfold Mem.valid_access. intros [Hpr ?]. specialize (Hpr _ Hofs).
      eapply Mem.perm_cur_max. eapply Mem.perm_implies. apply Hpr. constructor.
    - intros. specialize (H2 _ _ H).
      intros Hp. apply H2.
      eapply Mem.perm_store_2; eauto.
  Qed.
  (* cklr_loadbytes *)
  Next Obligation.
    intros [ ] m1 m2 Hm [b ofs] p2 Hp sz. inv Hm.
    apply coreflexivity in Hp; subst. simpl. red.
    destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
    edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
    rewrite Hv2. rauto.
  Qed.
  (* cklr_storebytes *)
  Next Obligation.
    intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp vs1 vs2 Hv. inv Hm.
    apply coreflexivity in Hp. subst. simpl. red.
    destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
    eapply list_rel_forall2. apply Hv.
    rewrite Hm2'. constructor.
    eexists (sepcw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.storebytes_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H2 _ _ Hp). apply H2.
      exploit Mem.storebytes_range_perm. apply Hm1'.
      rewrite length_rel; eauto. intros.
      eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
    - intros. specialize (H2 _ _ H).
      intros Hp. apply H2.
      eapply Mem.perm_storebytes_2; eauto.
  Qed.
  (* cklr_perm *)
  Next Obligation.
    intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp p' k H. inv Hm.
    apply coreflexivity in Hp. subst. simpl in *.
    eapply Mem.perm_extends; eauto.
  Qed.
  (* cklr_valid_block *)
  Next Obligation.
    intros [ ] m1 m2 Hm b1 b2 Hb. inv Hm.
    apply coreflexivity in Hb. subst.
    apply Mem.valid_block_extends; eauto.
  Qed.
  (* cklr_no_overlap *)
  Next Obligation.
    intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 Hb Hb1' Hb2' Hp1 Hp2. inv H.
    inv Hb1'. inv Hb2'. eauto.
  Qed.
  (* cklr_representable *)
  Next Obligation.
    xomega.
  Qed.
  (* cklr_aligned_area_inject *)
  Next Obligation.
    rewrite Z.add_0_r. assumption.
  Qed.
  (* cklr_disjoint_or_equal_inject *)
  Next Obligation.
    intuition xomega.
  Qed.
End SepcCKLR.

Section SIM.
  Context {p: Clight.program} {Σ: Genv.symtbl -> !li_d --o !li_d} (ps: prog_sim p Σ).
  Variable C: Clight.program.
  Context {sk: AST.program unit unit} (Hlk: link (skel (semantics1 C)) (skel (semantics1 p)) = Some sk).
  Definition sem_abs: semantics li_d li_c := Abs.c_semantics sk C Σ.
  Definition sem_impl: semantics li_d li_c := Impl.c_semantics sk C p.

  (* It's not possible to infer the outgoing interface so we define the following notations *)
  Notation " 'st1' " := (@Abs.st li_d li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'st2' " := (@Impl.st li_d li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'ext1' " := (@Abs.ext li_d li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'ext2' " := (@Impl.ext li_d li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'state1' " := (@Abs.state li_d li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'state2' " := (@Impl.state li_d li_c (semantics1 C)) (at level 1) : sim_scope.
  Open Scope sim_scope.

  Inductive state_match {ind} (ms: ind -> state -> state -> Prop): state1 -> state2 -> Prop :=
  | st_match: forall (s1 s2: state) σ1 i,
      ms i s1 s2 ->  ps σ1 (get_mem s2)->
      state_match ms (st1 s1 σ1) (st2 s2)
  | ext_match: forall (s1 s2: state) σ1 t1 t2 i,
      ms i s1 s2 -> t1 = t2 ->
      ps σ1 (get_mem s2)->
      state_match ms (ext1 s1 t1 σ1) (ext2 s2 t2).

  Variable se: Genv.symtbl.
  (* Let vars := module_var (Clight.globalenv se p). *)
  Let sepv := sepc p se.
  Instance sepv_frame: KripkeFrame unit (sepc_world p se).
  Proof. exact (cklr_kf sepv). Qed.

  Theorem fsim_abs_impl:
    forward_simulation cc_id (cc_c sepv) sem_abs sem_impl.
  Proof.
    pose proof (semantics1_rel C sepv) as [[ind ord match_st _ H _]].
    constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. cbn -[sem_abs sem_impl semantics1] in *.
    eapply link_linkorder in Hlk as [HseC Hsep].
    eapply Genv.valid_for_linkorder in HseC; eauto.
    eapply Genv.valid_for_linkorder in Hsep; eauto.
    specialize (H se1 se2 w Hse HseC).
    destruct Hse as [<- <-].
    apply forward_simulation_step with (match_states := (state_match (match_st se se w))).
    - intros. exploit @fsim_match_valid_query; eauto.
    - cbn. intros q1 q2 s1 Hq Hs1. cbn in Hs1. inv Hs1.
      edestruct @fsim_match_initial_states as (i & s2 & Hiq & Hs); eauto.
      exists(st2 s2). split. constructor. auto.
      eapply st_match. apply Hs. eapply correct_cond. auto. admit.
    - admit.
    - admit.
    - intros s1 t s1' Hstep s2 Hs. inversion Hstep.
      + admit.
      + subst. cbn. inv Hs.
        edestruct @fsim_match_external as (w' & qtgt & Hext & mq & msenv & fsim_match_after_ext); eauto.
        edestruct (simulation _ _ ps) as (rb' & qtgt' & m' & qrel & rrel & impl & mem_unchange & Hs'); eauto.
        assert (cc_c_reply sepv w' rb rb').
        {
          unfold sepv. destruct rb as [vres_src m_src]. destruct rb' as [vres_tgt m_tgt].
          constructor.
          - inv H3. inv rrel.
            apply val_inject_refl.
          - cbn. destruct w'. econstructor.
            + admit.            (* memory extension might not hold after external calls *)
            + admit.
            + admit.
        }
        edestruct fsim_match_after_ext as (i' & s2' & Haft & Hs2); eauto. exists w'. split. admit.
        eauto.
        exists(ext2 s2' w0). split.
        * econstructor. apply Hext. apply Haft.
          assert (qtgt = qtgt').
          {
            destruct qtgt as [vf0 sg0 args0 m0].
            destruct qtgt' as [vf1 sg1 args1 m1].
            inv qrel. inv Hext. inv H3. inv mq. f_equal.
            cbn in H12. SearchAbout Val.inject inject_id.
            rewrite val_inject_id in H12. inv H12. auto.
            congruence.
            admit.              (* Vundef args *)
          }
          rewrite H5. apply impl.
        * econstructor. apply Hs2. auto.
          assert (m' = get_mem s2').
          {
            inv Haft. inv rrel. auto.
          }
          rewrite <- H5. apply Hs'.
      + admit.
          - admit.
  Admitted.

  Close Scope sim_scope.
End SIM.
