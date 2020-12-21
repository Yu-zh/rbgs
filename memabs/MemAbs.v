Require Import Relations RelationClasses.
Require Import List.
Require Import compcert.common.LanguageInterface.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import models.Coherence.
Require Import examples.CompCertSem.
Require Import examples.Bigstep.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Memory. (* mem *)
Require Import compcert.common.AST.    (* Gvar *)
Require Import compcert.cfrontend.Ctypes. (* type *)
Require Import compcert.common.Values.    (* block *)
Require Import compcert.lib.Integers.     (* ptrofs *)
Require Import compcert.lib.Coqlib.       (* Z *)
Require Import compcert.lib.Maps.         (* PTree.get *)
Require Import compcert.common.Errors.    (* res *)
Require Import compcert.common.Memory.    (* unchanged_on *)
Require Import compcert.cfrontend.Cop.    (* val_casted_list *)
Require Import compcert.common.Smallstep.

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

Module Sem1.
  Section ABS_SEMANTICS.
    Context {liA liB: language_interface} (Σ: !liA --o !liA) (C: Smallstep.semantics liB liB).
    Variable li_rel: (query liA * reply liA) -> (query liB * reply liB) -> Prop.
    Variable se: Genv.symtbl.

    Variant state : Type := st (s: Smallstep.state C) (σ: !liA --o !liA).
    
    Inductive step: state -> trace -> state -> Prop :=
    | step_internal: forall s s' t σ,
        Step (C se) s t s' ->
        step (st s σ) t (st s' σ)
    | step_external: forall s s' qa ra qb rb σ w t,
        Smallstep.at_external (C se) s qb ->
        Smallstep.after_external (C se) s rb s' ->
        has (next σ w qa ra) t ->
        li_rel (qa, ra) (qb, rb) ->
        step (st s σ) E0 (st s' (next σ w qa ra)).

    Inductive initial_state: query liB -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (C se) q s ->
        initial_state q (st s Σ).
    (* We require Σ to account for all external calls of C *)
    Inductive at_external: state -> query li_null -> Prop := .
    Inductive after_external: state -> reply li_null -> state -> Prop := .
    
    Inductive final_state: state -> reply liB -> Prop :=
    | final_state_intro: forall s r σ,
        Smallstep.final_state (C se) s r ->
        final_state (st s σ) r.

    Definition lts : lts li_null liB state :=
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
  Definition semantics_spec {liA liB: language_interface} skel li_rel (Σ: !liA --o !liA) (C: Smallstep.semantics liB liB) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts Σ C li_rel se;
    |}.
  Definition c_semantics_spec (Σ: !li_d --o !li_d) (p: Clight.program): Smallstep.semantics li_null li_c :=
    semantics_spec (AST.erase_program p) li_rel Σ (semantics1 p).
End Sem1.

Module Sem2.
  Section IMPL_SEMANTICS.
    Context {liA: language_interface} (σ: !liA --o liA) (C: Smallstep.semantics liA liA).
    Variable se: Genv.symtbl.

    Notation state := (Smallstep.state C).
    
    Inductive step: state -> trace -> state -> Prop :=
    | step_internal: forall s s' t,
        Step (C se) s t s' ->
        step s t s'
    | step_external: forall s s' q r t,
        Smallstep.at_external (C se) s q ->
        Smallstep.after_external (C se) s r s' ->
        has σ (t, (q, r)) ->
        step s E0 s'.
    Inductive initial_state: query liA -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (C se) q s ->
        initial_state q s.
    Inductive at_external: state -> query li_null -> Prop := .
    Inductive after_external: state -> reply li_null -> state -> Prop := .
    
    Inductive final_state: state -> reply liA -> Prop :=
    | final_state_intro: forall s r,
        Smallstep.final_state (C se) s r ->
        final_state s r.

    Definition lts : lts li_null liA state :=
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
  Definition semantics_impl {liA: language_interface} skel (σ: !liA --o liA) (C: Smallstep.semantics liA liA) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts σ C se;
    |}.
  Definition c_semantics_impl (σ: !li_c --o li_c) (p: Clight.program): Smallstep.semantics li_null li_c :=
    semantics_impl (AST.erase_program p) σ (semantics1 p).
End Sem2.

Section ABS_CKLR.
  Variable ge: genv.
  
  Inductive module_var: ident -> type -> block -> ptrofs -> Prop :=
  | module_var_intro id b (v : globvar type) (ty : type):
      Genv.find_symbol ge id = Some b ->
      Genv.find_def ge b = Some (Gvar v) ->
      ty = gvar_info v ->
      module_var id ty b Ptrofs.zero.

  Inductive abs_world :=
    absw (vals: PTree.t val).

  Inductive value_match (ty: type) (m: mem) (b: block) (ofs: ptrofs): option val -> Prop :=
  | value_match_some v:
      deref_loc ty m b ofs v ->
      value_match ty m b ofs (Some v).
  Inductive abs_match_mem: abs_world -> relation mem :=
    abs_match_mem_intro m1 m2 vs:
      Mem.extends m1 m2 ->
      (forall id ty b ofs,
          module_var id ty b ofs ->
          (forall k p, ~Mem.perm m1 b (Ptrofs.unsigned ofs) k p) /\
          value_match ty m2 b ofs (vs ! id)) ->
      abs_match_mem (absw vs) m1 m2.
  
End ABS_CKLR.
