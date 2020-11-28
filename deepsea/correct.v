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

Section UNCHANGED_MEM.
  Variable se : Genv.symtbl.
  Variable p : Clight.program.
  Let ge : genv := globalenv se p.

  Inductive deref_same (ty: type) (b: block) (ofs: ptrofs) (m1: mem) (m2: mem) : Prop :=
  | deref_same_value chunk v:
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m1 (Vptr b ofs) = Some v ->
      Mem.loadv chunk m2 (Vptr b ofs) = Some v ->
      deref_same ty b ofs m1 m2
  | deref_same_array elem_ty sz a:
      ty = Tarray elem_ty sz a ->
      (forall (i : Z), 
          0 <= i < sz ->
          deref_same elem_ty b (Ptrofs.add ofs (Ptrofs.repr (i * sizeof ge elem_ty))) m1 m2) ->
      deref_same ty b ofs m1 m2
  | deref_same_struct id a co:
      ty = Tstruct id a ->
      (genv_cenv ge) ! id = Some co ->
      (forall id ty_fld delta,
          In (id, ty_fld) (co_members co) ->
          field_offset ge id (co_members co) = OK delta ->
          deref_same ty_fld b (Ptrofs.add ofs (Ptrofs.repr delta)) m1 m2) ->
      deref_same ty b ofs m1 m2
  | deref_same_union id a co ty_fld:
      ty = Tunion id a ->
      (genv_cenv ge) ! id = Some co ->
      In (id, ty_fld) (co_members co) ->
      deref_same ty_fld b ofs m1 m2 ->
      deref_same ty b ofs m1 m2.
      
  Inductive unchanged_on (m1: mem)(m2: mem) : Prop :=
  | unchanged_on_cond id l (v : globvar type) (ty : type):
      Genv.find_symbol ge id = Some l ->
      Genv.find_def ge l = Some (Gvar v) ->
      ty = gvar_info v ->
      deref_same ty l Ptrofs.zero m1 m2 ->
      unchanged_on m1 m2.                  
End UNCHANGED_MEM.

Section CORRECTNESS.
  Variable p : Clight.program.
  Variable se : Genv.symtbl.
  Let clight_p : !li_c --o li_c := clight_bigstep p se.
  Variable underlay_obj: ObjSig.
  Variable overlay_obj: ObjSig. 
  Let deepsea_p : !underlay_obj --o li_c := clight_p @ !(objsig2lic underlay_obj).

  Let spec_space : space := !underlay_obj --o !overlay_obj.
  Variable spec : !underlay_obj --o !overlay_obj.

  Record correctness :=
    {
      rel : token spec_space -> mem -> Prop;
      init_mem : mem -> Prop;
      module_var : forall m m' t, unchanged_on se p m m' -> rel t m -> rel t m';
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
            rel (v, t) (cr_mem cr);
            (* TODO: mem change only happened to module variables *)
      init_rel: forall m t, has spec t -> init_mem m -> rel t m;
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
  Variable spec : clique (!gs_obj).

  Variable gs_rel : token (!gs_obj) -> mem -> Prop.
  Variable gs_init_mem : mem -> Prop.
  Hypothesis gs_module_var : forall m m' t, unchanged_on se p m m' -> gs_rel t m -> gs_rel t m'.
  Hypothesis gs_simulation :
    forall e t m,
      gs_rel (e :: t) m ->
      exists cq cr,
        has (objsig2lic gs_obj) (e, (cq, cr)) /\
        has clight_p (nil, (cq, cr)) /\
        gs_rel t (cr_mem cr).
  Hypothesis gs_init_rel : forall m t, has spec t -> gs_init_mem m -> gs_rel t m.
                  
  Program Definition gs_correct : correctness p se empty_obj gs_obj (unit_trace_extend spec) :=
    {|
      rel '(u, o) m := gs_rel o m /\ u = nil;
      init_mem := gs_init_mem
    |}.
  Next Obligation.
    intros m m' [s t] unchanged. simpl.
    intros [rel <-]. intuition.
    eapply gs_module_var. apply unchanged. auto.
  Defined.
  Next Obligation.
    intros s e t m. simpl.
    intros [rel ->]. exists nil, nil.
    specialize (gs_simulation e t m rel) as [cq [cr [ev_match [ev_impl rest]]]].
    exists cq, cr. split. auto.
    split. apply ev_match.
    split. exists nil.
    split. constructor. apply ev_impl.
    split. apply rest. auto.
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

  Let deepsea_p : !underlay_obj --o li_c := clight_p @ !(objsig2lic underlay_obj).
  Variable spec : !underlay_obj --o overlay_obj.

  Hypothesis absfun_sim:
    forall s e,
      has spec (s, e) ->
      exists cq cr,
        has (objsig2lic overlay_obj) (e, (cq, cr)) /\
        has deepsea_p (s, (cq, cr)).

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
      specialize (absfun_sim H3) as [cq [cr [e_match e_impl]]].
      exists cq, cr. split. auto.
      split. apply e_match. split.
      apply e_impl.
      exists aa. split. auto. auto.
  Defined.
  Next Obligation.
    intros m [s t]. auto.
  Defined.
  
End ABSFUN_CORRECT.
