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
  Definition non_module_var (b : block) (ofs : Z) : Prop :=
    ~ module_var b ofs.
End MODULE_VAR.

Section MEM_ABSTRACTION.
  Variable inj: meminj_thr.
  Variable obj: ObjSig.
  Variable p_abs: !obj --o li_c.
  Variable p_con: !obj --o li_c.

  Definition mem_refine : Prop :=
    forall s q r q',
      has p_abs (s, (q, r)) ->
      cc_inj_query inj q q' ->
      exists r',
        has p_con (s, (q', r')) /\
        cc_inj_reply inj r r'.
End MEM_ABSTRACTION.

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
          exists u v cr cq m',
            s = u ++ v /\
            (* Clight implementation simulates deepsea event e *)
            m = cq_mem cq /\
            event_C_args overlay_obj e = cq_args cq /\
            has deepsea_p (u, (cq, cr)) /\
            m' = cr_mem cr /\
            event_C_res overlay_obj e = cr_retval cr /\
            Mem.unchanged_on (module_var se p) m m' /\
            (* behavior of the remaning trace *)
            rel (v, t) m';
      correct_cond: forall m t, has spec t -> init_mem m -> rel t m;
    }.
  Inductive init_mem_match: token (!li_c) -> mem -> Prop :=
  | nil_match m:
      init_mem_match nil m
  | cons_match q r s m:
      cq_mem q = m ->
      init_mem_match ((q,r) :: s) m.
  Inductive final_mem_match: token (!li_c) -> mem -> Prop :=
  | f_nil_match m:
      final_mem_match nil m
  | f_last_match q r m:
      cr_mem r = m ->
      final_mem_match ((q, r) :: nil) m
  | f_cons_match q s m:
      final_mem_match s m ->
      final_mem_match (q :: s) m.
  Definition final_state (co: correctness):
    forall us es m,
      rel co (us, es) m ->
      exists ces m',
        init_mem_match ces m /\
        has (dag_ext deepsea_p) (us, ces) /\
        final_mem_match ces m' /\
        Mem.unchanged_on (module_var se p) m m'.
  Proof.
    destruct co as [rel init_mem scope sim init_state]. simpl.
    intros us es.
    revert us.
    induction es.
    - intros. assert (us = nil). admit.
      subst. exists nil, m. admit.
    - intros. specialize (sim _ _ _ _ H) as [vs [ws [r0 [q0 [m0 [useq [q0m [q0arg [impl [r0m [r0ret [m0_unchanged rest]]]]]]]]]]]].
      specialize (IHes _ _ rest). Admitted.
  
  Section SOUND.
    Context {correct: correctness}.
    Variable c: Clight.program.
    Variable c_se: Genv.symtbl.
    Let inj: meminj_thr :=
      {|
        mit_meminj :=
          fun b =>
            match Genv.find_def (globalenv se p) b with
            | Some (Gvar _) => Some(b, 0)
            | _ => None
            end;
        mit_l := 1%positive;
        mit_r := 1%positive
      |}.
    Let p_abs: !underlay_obj --o li_c :=
      (clight_bigstep c c_se) @ !(objsig2lic overlay_obj) @ spec.
    Let p_con: !underlay_obj --o li_c :=
      (clight_bigstep c c_se) @ (dag_ext deepsea_p).
    Theorem mem_abs_sound: mem_refine inj underlay_obj p_abs p_con.
    Proof.
      intros s q r q' abs_map injq.
      simpl in abs_map. destruct abs_map as [p_es [[spec_es [has_spec p_rel]] c_qr]].
      
  End SOUND.
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
      exists cq cr m',
        m = cq_mem cq /\
        event_C_args gs_obj e = cq_args cq /\
        has clight_p (nil, (cq, cr)) /\
        m' = cr_mem cr /\
        event_C_res gs_obj e = cr_retval cr /\
        gs_rel t m'.
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
    specialize (gs_simulation e t m rel) as [cq [cr [m' [meq [arg [impl [res [m'eq rest]]]]]]]].
    exists cq, cr, m'.
    intuition.
    exists nil. split; intuition. constructor.
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
        event_C_args overlay_obj e = cq_args cq /\
        event_C_res overlay_obj e = cr_retval cr /\
        cq_mem cq = cr_mem cr /\
        has deepsea_p (s, (cq, cr)) .

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
      specialize (absfun_sim H3) as [q [r [arg [res [meq impl]]]]].
      exists ({|cq_vf:=(cq_vf q); cq_sg:=(cq_sg q); cq_args:=(cq_args q); cq_mem:=m|}).
      exists r, m.
      intuition. unfold cq_mem. reflexivity.
      Focus 3. exists aa. intuition.
      Admitted.
  Next Obligation.
    intros m [s t]. auto.
  Defined.
End ABSFUN_CORRECT.
