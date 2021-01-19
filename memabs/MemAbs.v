Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep.
Require Import Clight Ctypes Cop.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.

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

Section TRACE_STATE.
  (* Since σ is not guaranteed to be a regular function, there is no way to "guess" the underlying
     behavior w that corresponds to (qx, rx) *)
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
End TRACE_STATE.

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
    | step_at_external: forall s s' qa ra qb rb σ w t,
        Smallstep.at_external (C se) s qb ->
        Smallstep.after_external (C se) s rb s' ->
        has (next σ w qa ra) t ->
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
  Definition c_semantics (C: Clight.program) (Σ: Genv.symtbl -> !li_d --o !li_d) : Smallstep.semantics li_d li_c :=
    semantics (AST.erase_program C) li_rel Σ (semantics1 C).
End Abs.

Module Impl.
  Section IMPL_SEMANTICS.
    Context {liA liB: language_interface} (σ: Genv.symtbl -> !liB --o liA) (C: semantics liA liA).
    Variable se: Genv.symtbl.

    Variant state :=
    | st (s: Smallstep.state C)
    | ext (s: Smallstep.state C) (t: list (token liB)).

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

    Inductive initial_state: query liA -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (C se) q s ->
        initial_state q (st s).

    Inductive at_external: state -> query liB -> Prop :=
    | ext_at_external: forall s q r t,
        at_external (ext s ((q, r) :: t)) q.
    Inductive after_external: state -> reply liB -> state -> Prop :=
    | ext_after_external: forall s q r t,
        after_external (ext s ((q, r) :: t)) r (ext s t).

    Inductive final_state: state -> reply liA -> Prop :=
    | final_state_intro: forall s r,
        Smallstep.final_state (C se) s r ->
        final_state (st s) r.

    Definition lts : lts liB liA state :=
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
  Definition c_semantics (C: Clight.program) (p: Clight.program): Smallstep.semantics li_d li_c :=
    semantics (AST.erase_program C) (fun se => clight_bigstep p se @ !li_dc) (semantics1 C).
End Impl.

Section CORRECT.
  Inductive module_var (ge: genv) : block -> Z -> Prop :=
  | module_var_intro id b (v : globvar type) (ty : type):
      Genv.find_symbol ge id = Some b ->
      Genv.find_def ge b = Some (Gvar v) ->
      ty = gvar_info v ->
      module_var ge b (sizeof ge ty).
  Definition non_module_var ge b ofs := ~ module_var ge b ofs.
  Variable p: Clight.program.
  Variable se: Genv.symtbl.
  Let clight_p: !li_c --o li_c := clight_bigstep p se. (* the semantics of the clight program *)
  (* the semantics of the clight program on top of a deepsea underlay *)
  Let d_p : !li_d --o li_c := clight_p @ !li_dc.
  (* the coherent space where specification lives in *)
  Let spec_space : space := !li_d --o !li_d.
  (* the specification *)
  Variable spec : !li_d --o !li_d.

  Record correctness :=
    {
    (* rel : the relation that relates specifications and the memory *)
    rel :> token spec_space -> mem -> Prop;
    (* the condition that the memory has to satisfy *)
    init_mem : mem -> Prop;
    mem_scope : forall m m' t, Mem.unchanged_on (module_var (Clight.globalenv se p)) m m' -> rel t m -> rel t m';
    simulation:
      forall s dq dr t m,
        rel (s, (dq, dr)::t) m ->
        exists u v cr cq m',
          s = u ++ v /\
          (* Clight implementation simulates deepsea event e *)
          q_rel dq cq m /\
          has d_p (u, (cq, cr)) /\
          r_rel dr cr m' /\
          Mem.unchanged_on (non_module_var (Clight.globalenv se p)) m m' /\
          (* behavior of the remaning trace *)
          rel (v, t) m';
    correct_cond: forall m t, has spec t -> init_mem m -> rel t m;
    }.
End CORRECT.

Section SIM.
  Context {p: Clight.program} {se: Genv.symtbl} {Σ: Genv.symtbl -> !li_d --o !li_d}
          (correct: correctness p se (Σ se)).
  Variable C: Clight.program.
  Definition sem_abs: semantics li_d li_c := Abs.c_semantics C Σ.
  Definition sem_impl: semantics li_d li_c := Impl.c_semantics C p.

  Inductive state_match: Smallstep.state sem_abs -> Smallstep.state sem_impl -> Prop := .

  Variable R: cklr.             (* this will be instantiated to the cklr defined below *)
  Theorem fsim_abs_impl:
    forward_simulation cc_id (cc_c R) sem_abs sem_impl.
  Admitted.
End SIM.

Require Import Extends.

Section SEP_CKLR.
  (* the target memory and local variables that belong to the component
     constitute the klr index *)
  Inductive sep_world :=
    sepw (m: mem) (vars: block -> Z -> Prop) (Hm: forall b ofs, vars b ofs -> Mem.valid_block m b).
  Inductive sep_acc: relation sep_world :=
    acc_intro m1 m2 vars1 vars2 Hm1 Hm2:
      (* External call into the component only touches its own variables  *)
      Mem.unchanged_on (fun b ofs => ~ vars1 b ofs) m1 m2 ->
      (* and it may allocate new variables during the external call *)
      subrel vars1 vars2 ->
      sep_acc (sepw m1 vars1 Hm1) (sepw m2 vars2 Hm2).

  Inductive sep_mm: sep_world -> mem -> mem -> Prop :=
    match_intro: forall m m1 m2 vars Hm,
      (* source memory extends into target memory *)
      Mem.extends m1 m2 ->
      (* local variables of the component are only modified during external
         calls so they don't change in the course of internal steps*)
      Mem.unchanged_on vars m m2 ->
      (* m1 and locals don't have blocks in common *)
      (forall b ofs, vars b ofs -> ~ Mem.perm m1 b ofs Max Nonempty) ->
      sep_mm (sepw m vars Hm) m1 m2.

  Instance sep_acc_preo:
    PreOrder sep_acc.
  Proof.
    split.
    - intros [m]. constructor.
      apply Mem.unchanged_on_refl.
      rauto.
    - intros [m1] [m2] [m3].
      inversion 1. subst.
      inversion 1. subst.
      constructor.
      eapply Mem.unchanged_on_trans; eauto.
  Qed.

  Program Definition sep: cklr :=
    {|
    world := sep_world;
    wacc := sep_acc;
    mi w := inject_id;
    match_mem w := sep_mm w;
    match_stbls w := eq;
    |}.

  Next Obligation.
    repeat rstep. apply inject_incr_refl.
  Qed.

  Next Obligation.
    rauto.
  Qed.

  Next Obligation.
    intros [m] ? ? ->. apply Genv.match_stbls_id.
  Qed.

  Next Obligation.
    intros w ? ? m1 m2 <- Hm. inv Hm.
    erewrite -> Mem.mext_next; eauto.
  Qed.
  (* cklr_alloc *)
  Next Obligation.
    intros [m] m1 m2 Hm lo hi. inv Hm.
    destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn: Hm1.
    edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
    rewrite Hm2'.
    exists (absw m); split; repeat rstep.
    constructor; auto.
    eapply Mem.unchanged_on_trans; eauto.
    eapply Mem.alloc_unchanged_on; eauto.
    intros. eapply H2 in H. intros Hp. apply H.
    eapply Mem.perm_alloc_4 in Hp; eauto.
    SearchAbout Mem.alloc Mem.nextblock.
    eapply Mem.alloc_result in Hm1. subst.
    SearchAbout Mem.valid_block Mem.perm.
    eapply Mem.perm_valid_block in H.
  Qed.
  (* cklr_free *)
  Next Obligation.
    intros [m] m1 m2 Hm [[b lo] hi] r2 Hr. inv Hm.
    apply coreflexivity in Hr. subst. simpl. red.
    destruct (Mem.free m1 b lo hi) as [m1' | ] eqn: Hm1'; [ | constructor].
    edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. constructor.
    exists (absw m); split; repeat rstep.
    constructor; auto.
    eapply Mem.unchanged_on_trans; eauto.
    eapply Mem.free_unchanged_on; eauto.
    SearchAbout Mem.unchanged_on Mem.free.

End ABS_CKLR.
