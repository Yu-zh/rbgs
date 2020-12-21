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
Require Import compcert.cklr.CKLR.
Require Import compcert.cklr.Clightrel.

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
  Definition semantics {liA liB: language_interface} skel li_rel (Σ: !liA --o !liA) (C: Smallstep.semantics liB liB) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts Σ C li_rel se;
    |}.
  Definition c_semantics (Σ: !li_d --o !li_d) (p: Clight.program): Smallstep.semantics li_null li_c :=
    semantics (AST.erase_program p) li_rel Σ (semantics1 p).
End Abs.

Module Impl.
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
  Definition semantics {liA: language_interface} skel (σ: !liA --o liA) (C: Smallstep.semantics liA liA) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts σ C se;
    |}.
  Definition c_semantics (σ: !li_c --o li_c) (p: Clight.program): Smallstep.semantics li_null li_c :=
    semantics (AST.erase_program p) σ (semantics1 p).
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
  Context {p: Clight.program} {se: Genv.symtbl} {Σ: !li_d --o !li_d} (correct: correctness p se Σ).
  Variable C: Clight.program.
  Definition sem_abs: semantics li_null li_c := Abs.c_semantics Σ C.
  Definition sem_impl: semantics li_null li_c := Impl.c_semantics (clight_bigstep p se) C.
  Notation st := (Abs.st (semantics1 C)).
  Definition mem_from_state (s: Clight.state): mem :=
    match s with
    | State _ _ _ _ _ m => m
    | Callstate _ _ _ m => m
    | Returnstate _ _ m => m
    end.
  Inductive state_match R w: state sem_abs -> state sem_impl -> Prop :=
    ms_intro s1 s2 σ:
      Clightrel.state_match R w s1 s2 ->
      (forall t, has σ t -> correct t (mem_from_state s2)) ->
      state_match R w (st s1 σ) s2.

  Variable R: cklr.             (* this will be instantiated to the cklr defined below *)
  Theorem fsim_abs_impl:
    forward_simulation cc_id (cc_c R) sem_abs sem_impl.
  Admitted.
End SIM.

Section ABS_CKLR.

  Variable locals: (block -> Z -> Prop).
  Inductive abs_world :=
    absw (m: mem).
  Inductive abs_acc: relation abs_world :=
    acc_intro m1 m2:
      Mem.unchanged_on locals m1 m2 ->
      abs_acc (absw m1) (absw m2).

  Inductive abs_mm: abs_world -> mem -> mem -> Prop :=
    match_intro m1 m2:
      Mem.extends m1 m2 ->
      abs_mm (absw m2) m1 m2.
  Program Definition abs: cklr :=
    {|
    world := abs_world;
    wacc := abs_acc;
    mi w := inject_id;
    match_mem w := abs_mm w;
    match_stbls w := eq;
    |}.
  
End ABS_CKLR.
