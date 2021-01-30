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
    (* the linked system has type liA ->> liD *)
    Context {liA liB liC liD: language_interface} (Σ: Genv.symtbl -> !liA --o !liB) (C: semantics liC liD).
    Variable li_rel: (query liB * reply liB) -> (query liC * reply liC) -> Prop.
    Variable se: Genv.symtbl.

    Variant state : Type :=
    | st (s: Smallstep.state C) (σ: !liA --o !liB)
    (* s and σ constitute the state after the external call *)
    | ext (s: Smallstep.state C) (t: list (token liA)) (σ: !liA --o !liB).

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

    Inductive initial_state: query liD -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (C se) q s ->
        initial_state q (st s (Σ se)).

    Inductive at_external: state -> query liA -> Prop :=
    | ext_at_external: forall s q r t σ,
        at_external (ext s ((q, r) :: t) σ) q.
    Inductive after_external: state -> reply liA -> state -> Prop :=
    | ext_after_external: forall s q r t σ,
        after_external (ext s ((q, r) :: t) σ) r (ext s t σ).

    Inductive final_state: state -> reply liD -> Prop :=
    | final_state_intro: forall s r σ,
        Smallstep.final_state (C se) s r ->
        final_state (st s σ) r.

    Definition lts : lts liA liD state :=
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
  Definition semantics {liA liB liC liD: language_interface}
             skel li_rel (Σ: Genv.symtbl -> !liA --o !liB) (C: Smallstep.semantics liC liD) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts Σ C li_rel se;
    |}.
  Definition c_semantics sk (C: Clight.program) (Σ: Genv.symtbl -> !li_d --o !li_d) : Smallstep.semantics li_d li_c :=
    semantics sk li_rel Σ (semantics1 C).
End Abs.

Module Impl.
  Section IMPL_SEMANTICS.
    Context {liA liB liC: language_interface} (σ: Genv.symtbl -> !liA --o liB) (C: semantics liB liC).
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

    Inductive initial_state: query liC -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (C se) q s ->
        initial_state q (st s).

    Inductive at_external: state -> query liA -> Prop :=
    | ext_at_external: forall s q r t,
        at_external (ext s ((q, r) :: t)) q.
    Inductive after_external: state -> reply liA -> state -> Prop :=
    | ext_after_external: forall s q r t,
        after_external (ext s ((q, r) :: t)) r (ext s t).

    Inductive final_state: state -> reply liC -> Prop :=
    | final_state_intro: forall s r,
        Smallstep.final_state (C se) s r ->
        final_state (st s) r.

    Definition lts : lts liA liC state :=
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
  Definition semantics {liA liB liC: language_interface}
             skel (σ: Genv.symtbl -> !liA --o liB) (C: Smallstep.semantics liB liC) :=
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

Inductive q_rel': query li_d -> query li_c -> mem -> Prop:=
| q_rel'_intro:
    forall vf sg args args' m,
      list_rel Val.lessdef args args' ->
      q_rel' ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|})
             ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args';cq_mem:=m|}) m.

Definition r_with_mem (r: reply li_d) m: reply li_c :=
  match r with
    {|dr_retval:=ret|} => ({|cr_retval:=ret;cr_mem:=m|})
  end.

Record prog_sim (p: Clight.program) (Σ: Genv.symtbl -> !li_d --o !li_d) :=
  {
  mspec_rel :> (!li_d --o !li_d) -> mem -> Prop;
  init_mem : mem -> Prop;

  mem_scope : forall m m' σ se,
      Genv.valid_for (AST.erase_program p) se ->
      Mem.unchanged_on (module_var (Clight.globalenv se p)) m m' ->
      mspec_rel σ m ->
      mspec_rel σ m';
  simulation: forall σ dq dr t m se cq,
      Genv.valid_for (AST.erase_program p) se ->
      mspec_rel σ m -> exec σ dq t dr ->
      q_rel' dq cq m ->
      exists m',
        has (clight_bigstep p se @ !li_dc) (t, (cq, r_with_mem dr m')) /\
        Mem.unchanged_on (fun b ofs => ~ module_var (Clight.globalenv se p) b ofs) m m' /\
        (* Mem.unchanged_on allowed non-local variables to grow and we forbid it
        by adding constraints on Mem.nextblock *)
        Mem.nextblock m = Mem.nextblock m' /\
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
  Let vars: Genv.symtbl -> block -> Z -> Prop := fun se => module_var (globalenv se p).
  (* the target memory and local variables that belong to the component
     constitute the klr index *)
  Inductive sepc_world :=
    sepcw (se: Genv.symtbl) (m: mem) (Hvb: forall b ofs, vars se b ofs -> Mem.valid_block m b).
  Inductive sepc_acc: relation sepc_world :=
    acc_intro se m Hm1 Hm2:
      sepc_acc (sepcw se m Hm1) (sepcw se m Hm2).

  Inductive sepc_mm: sepc_world -> mem -> mem -> Prop :=
    match_intro: forall se m m1 m2 Hvb,
      (* source memory extends into target memory *)
      Mem.extends m1 m2 ->
      (* local variables of the component are only modified during external
         calls so they don't change in the course of internal steps*)
      Mem.unchanged_on (vars se) m m2 ->
      (* m1 and locals don't have blocks in common *)
      (forall b ofs, vars se b ofs -> ~ Mem.perm m1 b ofs Max Nonempty) ->
      sepc_mm (sepcw se m Hvb) m1 m2.

  Instance sepc_acc_preo:
    PreOrder sepc_acc.
  Proof.
    split.
    - intros [m]. constructor.
    - intros [m1] [m2] [m3].
      inversion 1. subst.
      inversion 1. subst.
      constructor.
  Qed.
  Inductive sepc_stbls: sepc_world -> Genv.symtbl -> Genv.symtbl -> Prop :=
    sepc_stbls_intro: forall se m Hm,
      sepc_stbls (sepcw se m Hm) se se.

  Program Definition sepc: cklr :=
    {|
    world := sepc_world;
    wacc := sepc_acc;
    mi w := inject_id;
    match_mem := sepc_mm;
    (* a cheap workaround *)
    match_stbls := sepc_stbls;
    |}.

  (* mi_acc *)
  Next Obligation.
    repeat rstep. apply inject_incr_refl.
  Qed.
  (* match_stbls_acc *)
  Next Obligation.
    repeat rstep. inv H. intros ? ? ?. inv H. constructor.
  Qed.
  (* match_stbls_proj *)
  Next Obligation.
    intros se1 se2 Hse. inv Hse. apply Genv.match_stbls_id.
  Qed.
  (* match_stbls_nextblock *)
  Next Obligation.
    inv H.
    erewrite <- Mem.mext_next; eauto.
    inv H0. auto.
  Qed.
  (* cklr_alloc *)
  Next Obligation.
    intros [ ] m1 m2 Hm lo hi. inv Hm.
    destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn: Hm1.
    edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
    rewrite Hm2'.
    eexists (sepcw _ m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
    - intros. specialize (Hvb _ _ H).
      specialize (H5 _ _ H). intros Hp. apply H5.
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
    eexists (sepcw _ m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.free_unchanged_on; eauto.
      intros ofs Hofs Hv. specialize (H5 _ _ Hv). apply H5.
      exploit Mem.free_range_perm. apply Hm1'. eauto.
      intros Hp. eapply Mem.perm_cur_max.
      eapply Mem.perm_implies. apply Hp. constructor.
    - intros. specialize (H5 _ _ H).
      intros Hp. apply H5.
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
    eexists (sepcw _ m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.store_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H5 _ _ Hp). apply H5.
      exploit Mem.store_valid_access_3. apply Hm1'.
      unfold Mem.valid_access. intros [Hpr ?]. specialize (Hpr _ Hofs).
      eapply Mem.perm_cur_max. eapply Mem.perm_implies. apply Hpr. constructor.
    - intros. specialize (H5 _ _ H).
      intros Hp. apply H5.
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
    eexists (sepcw _ m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.storebytes_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H5 _ _ Hp). apply H5.
      exploit Mem.storebytes_range_perm. apply Hm1'.
      rewrite length_rel; eauto. intros.
      eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
    - intros. specialize (H5 _ _ H).
      intros Hp. apply H5.
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

Lemma perm_imp m b ofs k p:
  Mem.perm m b ofs k p ->
  Mem.perm m b ofs Max Nonempty.
Proof.
  intros Hp.
  destruct k.
  - eapply Mem.perm_implies; eauto. constructor.
  - eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
Qed.

Hypothesis module_var_dec: forall se p b ofs,
    {module_var (globalenv se p) b ofs} + {~module_var (globalenv se p) b ofs}.

Lemma mem_match_sim p m1 m2 m2' mx se Hvbx Hvb:
  Mem.unchanged_on (fun (b : block) (ofs : Z) => ~ module_var (globalenv se p) b ofs) m2 m2' ->
  Mem.nextblock m2 = Mem.nextblock m2' ->
  sepc_mm p (sepcw p se mx Hvbx) m1 m2 ->
  sepc_mm p (sepcw p se m2' Hvb) m1 m2'.
Proof.
  intros H Hnext Hm. inversion Hm as [? ? ? ? ? Hext Hinv Hx]. subst. clear Hm.
  constructor.
  - constructor.
    (* nextblock m1 = nextblock m2' *)
    + destruct Hext. congruence.
    (* memory injection *)
    + constructor.
      * inversion 1. subst. intros Hp.
        exploit Mem.mi_perm. apply Mem.mext_inj; apply Hext. eauto. eauto.
        replace (ofs + 0) with ofs in * by omega. intros Hp'.
        destruct (module_var_dec se p b2 ofs) as [Hmv | Hmv].
        (* zero permission blocks inject into any block *)
        -- eapply Hx in Hmv. exfalso. apply Hmv.
           eapply perm_imp. eauto.
        (* unchanged vars perserve injections *)
        -- rewrite <- Mem.unchanged_on_perm. apply Hp'. apply H. apply Hmv.
           eapply Mem.perm_valid_block. eauto.
      * inversion 1. subst. intros.
        exploit Mem.mi_align; eauto. apply Hext.
      * inversion 1. subst. intros Hp.
        exploit Mem.mi_memval; [ apply Hext | eauto | eauto | ]. intros Hv.
        replace (ofs + 0) with ofs in * by omega.
        destruct (module_var_dec se p b2 ofs) as [Hmv | Hmv].
        -- eapply Hx in Hmv. exfalso.
           apply Hmv. eapply perm_imp. eauto.
        -- exploit Mem.unchanged_on_contents. apply H. apply Hmv.
           exploit Mem.mi_perm; [ apply Hext | eauto | eauto | ].
           replace (ofs + 0) with ofs in * by omega. auto.
           intros ->. auto.
    (* permission *)
    + intros b ofs k perm Hp.
      destruct (module_var_dec se p b ofs) as [Hmv | Hmv].
      * right. apply Hx. auto.
      * exploit Mem.unchanged_on_perm. apply H. apply Hmv.
        unfold Mem.valid_block. rewrite Hnext.
        eapply Mem.perm_valid_block. apply Hp.
        intros Hp'. rewrite <- Hp' in Hp.
        eapply Mem.mext_perm_inv; eauto.
  - eapply Mem.unchanged_on_refl.
  - auto.
Qed.

Lemma list_inj f xs ys:
  list_rel (Val.inject f) xs ys ->
  Val.inject_list f xs ys.
Proof.
  induction 1; try constructor; auto.
Qed.

Lemma sepc_cont_match_le p w w' k1 k2:
  cont_match (sepc p) w k1 k2 ->
  cont_match (sepc p) w' k1 k2.
Proof.
  induction 1; try constructor; auto.
Qed.

Lemma state_match_mem_unchanged p se m Hvb s1 s2:
  state_match (sepc p) (sepcw p se m Hvb) s1 s2 ->
  Mem.unchanged_on (module_var (globalenv se p)) m (get_mem s2).
Proof.
  inversion 1; subst; cbn in *.
  - inv H3. auto.
  - inv H3. auto.
  - inv H2. auto.
Qed.

Lemma state_match_mem_nextblock p w s1 s2:
  state_match (sepc p) w s1 s2 ->
  Mem.nextblock (get_mem s1) = Mem.nextblock (get_mem s2).
Proof.
  inversion 1; subst; cbn in *.
  - inv H3. apply H4.
  - inv H3. apply H4.
  - inv H2. apply H3.
Qed.

Lemma unchanged_on_sym P m1 m2:
  Mem.unchanged_on P m1 m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  Mem.unchanged_on P m2 m1.
Proof.
  intros Hinv Hnxt. constructor.
  - destruct Hinv. congruence.
  - intros. symmetry. apply Hinv; auto.
    unfold Mem.valid_block in *. congruence.
  - intros. symmetry. apply Hinv; auto.
    rewrite Mem.unchanged_on_perm; eauto.
    unfold Mem.valid_block. rewrite Hnxt.
    eapply Mem.perm_valid_block. eauto.
Qed.

Section SIM.
  Context {p: Clight.program} {Σ: Genv.symtbl -> !li_d --o !li_d} (ps: prog_sim p Σ).
  Variable C: Clight.program.
  Context {sk: AST.program unit unit} (Hlk: link (skel (semantics1 C)) (skel (semantics1 p)) = Some sk).
  Definition sem_abs: semantics li_d li_c := Abs.c_semantics sk C Σ.
  Definition sem_impl: semantics li_d li_c := Impl.c_semantics sk C p.

  (* It's not possible to infer the outgoing interface so we define the following notations *)
  Notation " 'st1' " := (@Abs.st li_d li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'st2' " := (@Impl.st li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'ext1' " := (@Abs.ext li_d li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'ext2' " := (@Impl.ext li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'state1' " := (@Abs.state li_d li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'state2' " := (@Impl.state li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Open Scope sim_scope.

  Variable se: Genv.symtbl.
  Let sepv := sepc p.

  Inductive comp_state_match:  world sepv -> state1 -> state2 -> Prop :=
  | st_match: forall (s1 s2: state) σ1 se m Hvb,
      state_match sepv (sepcw p se m Hvb) s1 s2 ->  ps σ1 m ->
      comp_state_match (sepcw p se m Hvb) (st1 s1 σ1) (st2 s2)
  | ext_match: forall (s1 s2: state) σ1 t1 t2 se m Hvb,
      state_match sepv (sepcw p se m Hvb) s1 s2 ->
      t1 = t2 -> ps σ1 m ->
      comp_state_match (sepcw p se m Hvb) (ext1 s1 t1 σ1) (ext2 s2 t2).

  Inductive cc_query: (world sepv) -> query li_c -> query li_c -> Prop :=
  | cc_query_intro: forall se m Hvb q1 q2,
      match_query (cc_c sepv) (sepcw p se m Hvb) q1 q2 ->
      (init_mem _ _  ps) m ->
      cc_query (sepcw p se m Hvb) q1 q2.

  Program Definition sepcc :=
    {|
    ccworld := ccworld (cc_c sepv);
    match_senv := match_senv (cc_c sepv);
    match_query := cc_query;
    match_reply _ r1 r2 := exists w, (cc_c_reply sepv) w r1 r2;
    |}.
  Next Obligation.
    inv H. auto.
  Qed.
  Next Obligation.
    inv H. auto.
  Qed.

  Theorem fsim_abs_impl:
    forward_simulation cc_id sepcc sem_abs sem_impl.
  Proof.
    constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. cbn -[sem_abs sem_impl semantics1] in *.
    inv Hse. clear se. rename se2 into se.
    eapply link_linkorder in Hlk as [HseC Hsep].
    eapply Genv.valid_for_linkorder in HseC; eauto.
    eapply Genv.valid_for_linkorder in Hsep; eauto.
    pose (ms := fun s1 s2 => exists w, comp_state_match w s1 s2 /\ match_stbls sepv w se se).
    apply forward_simulation_step with (match_states := ms).
    - intros ? ? Hq. inv Hq. inv H1.
      cbn. eapply Genv.is_internal_match; eauto.
      + instantiate (1 := p).
        repeat apply conj; auto.
        induction (AST.prog_defs (_ C)) as [ | [id [f|v]] defs IHdefs];
          repeat (econstructor; eauto).
        * apply incl_refl.
        * apply linkorder_refl.
        * instantiate (1 := fun _ => eq). reflexivity.
        * instantiate (1 := eq). destruct v; constructor; auto.
      + eapply match_stbls_proj; eauto. constructor.
      + cbn. congruence.
    - intros q1 q2 s1 Hq Hs1. inv Hq. inv H1. inv Hs1. inv H1.
      set (w := sepcw p se m Hvb0).
      assert (Hge: genv_match C sepv w (globalenv se C) (globalenv se C)).
      {
        eapply (rel_push_rintro (fun se=> globalenv se C) (fun se=> globalenv se C)).
        constructor.
      }
      transport_hyps.
      exists (st2 (Callstate vf2 vargs2 Kstop m2)). split.
      + constructor. econstructor; eauto.
        * revert vargs2 H0. clear -H12.
          induction H12; inversion 1; subst; constructor; eauto.
          eapply val_casted_inject; eauto.
        * eapply match_stbls_nextblock; eauto.
          constructor.
      + exists w. split; try constructor.
        * constructor; eauto.
          -- clear -H0. induction H0; constructor; eauto.
          -- constructor.
        * apply correct_cond; eauto.
    - intros s1 s2 r1 (w & Hs & Hge) H. inv H. inv Hs. inv H0. inv H3.
      eexists. split.
      + constructor. inv H6.
        constructor.
      + eexists. constructor; eauto.
    - intros s1 s2 qx1 (w & Hs & Hge) Hq1.
      inv Hq1. inv Hs. eexists tt, _.
      repeat apply conj; try constructor.
      intros r1 r2 s1' Hr1 Hs1'. inv Hr1. inv Hs1'.
      eexists. split.
      + constructor.
      + econstructor. split; try econstructor; eauto. constructor; eauto.
    - intros s1 t s1' Hstep s2 (w & Hs & Hge). inv Hstep.
      + inv Hs. inv Hge. set (w := sepcw p se m0 Hvb) in *.
        assert (Hge': genv_match C sepv w (globalenv se C) (globalenv se C)).
        {
          eapply (rel_push_rintro (fun se=> globalenv se C) (fun se=> globalenv se C)).
          subst w. constructor.
        }
        eapply step_rel in H; eauto.
        2: { repeat rstep. }
        destruct H as (s2' & Hstep' & Hs2').
        exists (st2 s2'). split.
        * constructor. apply Hstep'.
        * destruct Hs2' as (w' & Hw' & Hs2').
          inv Hw'. eexists (sepcw  _ _ _ _). split; constructor; eauto.
      + cbn in *. inv Hs. rename s' into s1. rename s0 into s'.
        inv Hge. set (w := sepcw p se m0 Hvb) in *.
        assert (Hsim: exists q', at_external (globalenv se C) s' q' /\ match_query (cc_c sepv) w qb q').
        {
          inv H. inv H6.
          assert (vf <> Vundef). destruct vf; cbn in *; try congruence.
          assert (genv_match C sepv w (globalenv se C) (globalenv se C)).
          eapply (rel_push_rintro (fun se=> globalenv se C) (fun se=> globalenv se C)).
          subst w; constructor.
          transport_hyps.
          eexists. split.
          - econstructor. eauto.
          - inv H2. constructor; auto.
            clear -H12. induction H12; constructor; auto.
        }
        destruct Hsim as (q' & Hsim & Hq). inversion Hq.
        assert (q_rel' qa q' m2).
        {
          inv H2. inv H15.
          replace vf1 with vf2.
          2: { cbn in H3. rewrite val_inject_id in H3. inv H3; try congruence. }
          constructor. clear -H4. induction H4; constructor; auto.
          cbn in H. rewrite val_inject_id in H. auto.
        }
        eapply mem_scope with (m' := m2) in H8; eauto.
        2: { inv H5. auto. }
        edestruct simulation as (m' & impl & Hmem & Hnext & Hs'); eauto.
        assert (Hvb': forall b ofs, module_var (globalenv se p) b ofs -> Mem.valid_block m' b).
        {
          intros b ofs Hb. eapply Hm2 in Hb. inv H5.
          eapply Mem.valid_block_unchanged_on; eauto.
          eapply Mem.valid_block_unchanged_on; eauto.
        }
        assert (Hsim': exists s1', after_external s' (r_with_mem ra m') s1' /\ state_match sepv (sepcw p se m' Hvb') s1 s1').
        {
          inv H2. unfold r_with_mem. inv H16. inv Hsim. inv H0. inv H6.
          eexists _. split.
          - econstructor.
          - econstructor. apply val_inject_refl.
            eapply sepc_cont_match_le. eauto. cbn in *.
            eapply mem_match_sim; eauto.
        }
        destruct Hsim' as (s1' & H' & Hs1').
        exists (ext2 s1' w0). split.
        * eapply Impl.step_at_external; eauto.
        * eexists. split. constructor; eauto.
          constructor.
      + inv Hs.
        exists (st2 s0). split.
        * constructor.
        * eexists. split; eauto. constructor; auto.
    - apply well_founded_ltof.
  Qed.
  Close Scope sim_scope.
End SIM.

Module Comp.
  Section UNSEM_COMP.
    Context {liA liB liC : language_interface}.
    Context (Σ1 : Genv.symtbl -> !liB --o liC) (Σ2 : Genv.symtbl -> !liA --o !liB).
    Let Σ : Genv.symtbl -> !liA --o liC := fun se => (Σ1 se) @ (Σ2 se).
    Variable sk : AST.program unit unit.
    Variable vq : Genv.symtbl -> query liC -> bool.
    Let L1 : semantics liA liC := UnSem.semantics sk Σ vq.
    Let L2 : semantics liA liC := Abs.semantics sk eq Σ2 (UnSem.semantics sk Σ1 vq).

    Notation " 'st' " := (@Abs.st liA liB liB liC (UnSem.semantics sk Σ1 vq)) (at level 1) : sim_scope.
    Notation " 'ext' " := (@Abs.ext liA liB liB liC (UnSem.semantics sk Σ1 vq)) (at level 1) : sim_scope.
    Notation " 'state' " := (@Abs.state liA liB liB liC (UnSem.semantics sk Σ1 vq)) (at level 1) : sim_scope.
    Open Scope sim_scope.

    (* The flag in L2 should always be true *)
    Inductive state_match : nat -> Smallstep.state L1 -> state -> Prop :=
    | match_st: forall b ts ts' σ,
        (forall r tr tr', has )
          has σ (ts, ts') ->
        state_match (true, ts) (st (true, ts') σ)
    | match_ext: forall b ts ts' σ t,
        state_match (b, ts) (ext (true, ts') t σ).

    Lemma fsim_unsem_comp:
      forward_simulation 1 1 L1 L2.
    Proof.
      constructor.

  End UNSEM_COMP.
End Comp.
