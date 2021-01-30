Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep.
Require Import Clight Ctypes Cop.
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
