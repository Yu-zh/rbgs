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
Local Obligation Tactic := idtac.
Program Definition li_dc: li_d --o li_c :=
  {|
  has '(d, c) := li_rel d c
  |}.
Next Obligation.
  intros [[dq1 dr1] [cq1 cr1]] [[dq2 dr2] [cq2 cr2]]. simpl.
  intros rel1 rel2. intuition.
  - destruct cq1. destruct cq2. inversion H. clear H. subst.
    inversion rel1. subst. inversion rel2. subst.
    f_equal. exploit H1. auto. congruence.
  - injection H. destruct cr1. destruct cr2. destruct cq1. destruct cq2.
    inversion rel1. inversion rel2. subst. intros.
    f_equal. congruence. congruence.
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
  intros liA liB sig w q r [s1 t1] [s2 t2] H1 H2 Ht.
  pose proof (has_coh _ _ _ _ H1 H2). cbn in H. clear H1 H2.
  edestruct H as [Hr Hl].
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
        (* (w, r) may not be the "right" execution. In other words, (next σ w q r) might be empty.
           But that's fine because it's still related to s per correctness *)
        exec σ qa w ra ->
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

  Section MATCH.
    Inductive state_match {ind} (ms: ind -> state -> state -> Prop): state1 -> state2 -> Prop :=
    | st_match: forall (s1 s2: state) σ1 i,
        ms i s1 s2 ->  ps σ1 (get_mem s2)->
        state_match ms (st1 s1 σ1) (st2 s2)
    | ext_match: forall (s1 s2: state) σ1 t1 t2 i,
        ms i s1 s2 -> t1 = t2 ->
        ps σ1 (get_mem s2)->
        state_match ms (ext1 s1 t1 σ1) (ext2 s2 t2).
  End MATCH.
  Variable se: Genv.symtbl.
  Let vars := module_var (Clight.globalenv se p).
  Let sepv := sep vars.
  Instance sepv_frame: KripkeFrame unit (sep_world vars).
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
    assert (se = se1). admit. subst se2. subst se1.
    (* apply forward_simulation_step with *)
    (*     (match_states := fun s1 s2 => klr_diam tt (state_match (match_st se se)) w s1 s2). *)
    apply forward_simulation_step with (match_states := (state_match (match_st se se w))).
    - intros. exploit @fsim_match_valid_query; eauto.
    - cbn. intros q1 q2 s1 Hq Hs1.
      cbn in Hs1. inv Hs1.
      edestruct @fsim_match_initial_states as (i & s2 & Hiq & Hs); eauto.
      exists(st2 s2). split. constructor. auto.
      eapply st_match. apply Hs. eapply correct_cond. auto. admit.
    (* initial query has to satisfy init_mem. Maybe we have to parametrize the
       semantics over some proposition on memory *)
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
