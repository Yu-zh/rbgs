Require Import Relations RelationClasses.
Require Import List.
Require Import compcert.common.LanguageInterface.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import models.Coherence.
Require Import deepsea.xObjSem.
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
Require Import DSCC.                      (* objsig2lic *)
Require Import compcert.common.Memory.    (* unchanged_on *)

Section MODULE_VAR.
  Variable se : Genv.symtbl.
  Variable p : Clight.program.
  Let ge : genv := globalenv se p.

  Inductive module_var : block -> Z -> Prop :=
  | module_var_intro id b (v : globvar type) (ty : type):
      Genv.find_symbol ge id = Some b ->
      Genv.find_def ge b = Some (Gvar v) ->
      ty = gvar_info v ->
      module_var b (sizeof ge ty).
  Inductive non_module_var : block -> Z -> Prop :=
  | non_module_var_intro b ofs b' ofs':
      module_var b ofs ->
      b' <> b \/ ofs <> ofs' ->
      non_module_var b' ofs'.
End MODULE_VAR.

(* The general case for a clight program to be correct w.r.t its specification *)
Section CORRECTNESS.
  Variable p : Clight.program.
  Variable se : Genv.symtbl.
  Let clight_p : !li_c --o li_c := clight_bigstep p se. (* the semantics of the clight program *)
  Variable underlay_obj: ObjSig.
  Variable overlay_obj: ObjSig.
  (* the semantics of the clight program on top of a deepsea underlay *)
  Let deepsea_p : !underlay_obj --o li_c := clight_p @ !(objsig2lic underlay_obj).
  (* the coherent space where specification lives in *)
  Let spec_space : space := !underlay_obj --o !overlay_obj.
  (* the specification *)
  Variable spec : !underlay_obj --o !overlay_obj.

  Record correctness :=
    {
      (* rel : the relation that relates specifications and the memory *)
      rel : token spec_space -> mem -> Prop;
      (* the condition that the memory has to satisfy *)
      init_mem : mem -> Prop;
      mem_scope : forall m m' t, Mem.unchanged_on (module_var se p) m m' -> rel t m -> rel t m';
      simulation:
        forall s e t m,
          rel (s, e::t) m ->
          exists u v cq cr,
            s = u ++ v /\
            (* Clight query/reply matches the deepsea event e *)
            has (objsig2lic overlay_obj) (e, (cq, cr)) /\
            (* Clight implementation simulates deepsea event e *)
            has deepsea_p (u, (cq, cr)) /\ 
            (* behavior of the remaning trace *)
            rel (v, t) (cr_mem cr) /\
            (* mem change only happened to module variables *)
            Mem.unchanged_on (non_module_var se p) (cq_mem cq) (cr_mem cr);
      (* the codition that p faithfully implements the spec *)
      correct_cond: forall m t, has spec t -> init_mem m -> rel t m;
    }.
End CORRECTNESS.

Local Obligation Tactic := idtac.
Program Definition empty_obj : ObjSig :=
  {|
    event := Empty_set
  |}.
Next Obligation.
  esplit; intros; try contradiction.
  refine None.
  Unshelve.
  intros; try contradiction.
  intros; try contradiction.
Defined.
Next Obligation.
  esplit; intros; try contradiction.
Defined.
Program Definition unit_trace : clique (!empty_obj) :=
  {|
    has s := s = nil
  |}.
Next Obligation.
  simpl. intros. subst. constructor.
Defined.
Program Definition unit_trace_extend {s : space} (c : clique s) : !empty_obj --o s :=
  {|
    has '(u, t) := u = nil /\ has c t
  |}.
Next Obligation.
  intros s c [u1 s1] [u2 s2]. simpl.
  intros [-> has1] [-> has2] coh.
  split.
  - exploit (has_coh _ c s1 s2); auto.
  - auto.
Defined.

Section GS_CORRECT.
  Variable p : Clight.program.  (* a getter/setter program *)
  Variable se : Genv.symtbl.
  Let clight_p : !li_c --o li_c := clight_bigstep p se.
  Variable gs_obj: ObjSig.
  (* the getter/setter program represented as 1 --o li_c *)
  Program Definition deepsea_p : !empty_obj --o li_c :=
    {|
      has '(s, c) := s = nil /\ has clight_p (nil, c)
    |}.
  Next Obligation.
    intros [s1 qr1] [s2 qr2]. simpl.
    intros [-> lmaps1] [-> lmaps2] H.
    split; intuition.
    exploit (has_coh _ (c_bigstep_lmaps se p) (nil, qr1) (nil, qr2)).
    apply lmaps1. apply lmaps2. constructor.
    intuition.
  Defined.
  (* Since the getter/setter objects do not interact with the environment,
     their specifications are just a clique within the space of !obj *)
  Variable spec : clique (!gs_obj).

  (* The witness relation *)
  Variable gs_rel : token (!gs_obj) -> mem -> Prop.
  (* The condition on the initial memory *)
  Variable gs_init_mem : mem -> Prop.
  (* Proof obligation 1 *)
  Hypothesis gs_mem_scope :
    forall m m' t, Mem.unchanged_on (module_var se p) m m' -> gs_rel t m -> gs_rel t m'.
  (* Proof obligation 2 *)
  Hypothesis gs_simulation :
    forall e t m,
      gs_rel (e :: t) m ->
      exists cq cr,
        has (objsig2lic gs_obj) (e, (cq, cr)) /\
        has clight_p (nil, (cq, cr)) /\
        gs_rel t (cr_mem cr) /\
        Mem.unchanged_on (non_module_var se p) (cq_mem cq) (cr_mem cr).
  (* Proof obligation 3 *)
  Hypothesis gs_init_rel : forall m t, has spec t -> gs_init_mem m -> gs_rel t m.

  (* Adapt the correctness of a getter/setter object into the general form *)
  Program Definition gs_correct : correctness p se empty_obj gs_obj (unit_trace_extend spec) :=
    {|
      rel '(u, o) m := gs_rel o m /\ u = nil;
      init_mem := gs_init_mem
    |}.
  Next Obligation.
    intros m m' [s t] unchanged. simpl.
    intros [rel <-]. intuition.
    eapply gs_mem_scope. apply unchanged. auto.
  Defined.
  Next Obligation.
    intros s e t m. simpl.
    intros [rel ->]. exists nil, nil.
    specialize (gs_simulation e t m rel) as [cq [cr [ev_match [ev_impl [rest unchanged]]]]].
    exists cq, cr. split. auto.
    split. apply ev_match.
    split. exists nil.
    split. constructor. apply ev_impl.
    split; intuition.
  Defined.
  Next Obligation.
    intros m [s t]. simpl.
    intros [-> H] H1. split; auto.
  Defined.
End GS_CORRECT.

Section ABSFUN_CORRECT.
  Variable p : Clight.program.  (* an absfun program *)
  Variable se : Genv.symtbl.
  Let clight_p : !li_c --o li_c := clight_bigstep p se.
  Variable underlay_obj : ObjSig.
  Variable overlay_obj : ObjSig.
  (* the clight program on top of a deepsea underlay *)
  Let deepsea_p : !underlay_obj --o li_c := clight_p @ !(objsig2lic underlay_obj).
  (* Since the absfun objects are linear, we can use their linear pattern as spec
     Regular externsion extends the linear paatern to the general form *)
  Variable spec : !underlay_obj --o overlay_obj.
  (* The proof obligation for absfun objects *)
  Hypothesis absfun_sim:
    forall s e,
      has spec (s, e) ->
      exists cq cr,
        has (objsig2lic overlay_obj) (e, (cq, cr)) /\
        has deepsea_p (s, (cq, cr)) /\
        (cq_mem cq) = (cr_mem cr).
  (* Adapt the correctness of the absfun objects into the genral form *)
  Program Definition absfun_correct : correctness p se underlay_obj overlay_obj (dag_ext spec) :=
    {|
      rel '(s, t) _ := has (dag_ext spec) (s, t);
      init_mem _ := True;
    |}.
  Next Obligation.
    intros m m' [s t] unchanged. simpl.
    auto.
  Defined.
  Next Obligation.
    intros s e t m. simpl.
    intros [ss [comul lmap]].
    inversion comul.
    - inversion lmap. subst. inversion H3.
    - exists s0, a.
      specialize (absfun_sim s0 e).
      subst ss. subst s.
      inversion lmap. subst.
      specialize (absfun_sim H3) as [cq [cr [e_match [e_impl unchanged]]]].
      exists cq, cr. split. auto.
      split. apply e_match. split.
      apply e_impl.
      split. exists aa. split. auto. auto.
      rewrite unchanged. apply Mem.unchanged_on_refl.
  Defined.
  Next Obligation.
    intros m [s t]. auto.
  Defined.
End ABSFUN_CORRECT.
