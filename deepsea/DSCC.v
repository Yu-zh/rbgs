Require Import Relations RelationClasses.
Require Import List.
Require Import compcert.common.LanguageInterface.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import models.Coherence.
Require Import deepsea.xObjSem.
Require Import examples.CompCertSem.
Require Import deepsea.HyperTypeDef.
Require Import deepsea.HyperType.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Ctypes.
(* Require Import deepsea.Utils. *)

Definition event_AST_sig {event : Set} {objsig_impl : ObjSigImpl event} (e : event) : signature :=
  {|
  sig_args := map (fun htp => typ_of_type (tp_ty htp)) (event_htp_args e);
  sig_res := opttyp_of_type (tp_ty (event_htp_res e));
  sig_cc := cc_default
  |}.

Lemma id_eq_imply_AST_sig_eq {event : Set} {objsig_impl : ObjSigImpl event} {objsig_prop : ObjSigProp event}:
  forall e1 e2 : event,
    event_id e1 = event_id e2 ->
    event_AST_sig e1 = event_AST_sig e2.
Proof.
  intros e1 e2 eq_id.
  unfold event_AST_sig.
  rewrite (id_htp_args_eq e1 e2 eq_id).
  rewrite (id_htp_res_eq e1 e2 eq_id).
  reflexivity.
Qed.

Section DS_CC.
  Variable objsig : ObjSig.
  Existing Instance objsig_impl.
  Existing Instance objsig_prop.

  Definition concrete_event (e: event objsig) : Prop :=
    ht_list_ft_cond (event_args e) /\ ht_list_valid_ft_cond (event_args e).

  Definition event_C_res (e: event objsig) : Values.val :=
    ht_cval (event_res e).

  Definition event_C_args (e: event objsig) : list Values.val :=
    HList_map_nodep (fun htp (arg: tp_ft htp) => ht_cval arg) (event_args e).

  Variant ev_cp_rel : event objsig -> c_query * c_reply -> Prop :=
  | ev_cp_rel_intro ev cp:
      forall id vf sg vargs vres m,
      concrete_event ev ->
      id = event_id ev ->
      vf = Values.Vptr id Integers.Ptrofs.zero -> (* TODO: relate with event_id *)
      sg = event_AST_sig ev ->
      vargs = event_C_args ev ->
      vres = event_C_res ev ->
      cp = (pair (cq vf sg vargs m) (cr vres m)) -> (* TODO: may need to restrict permission *)
      ev_cp_rel ev cp.

  Lemma ev_cp_rel_coh:
    forall (ev1 ev2: event objsig) (cq1 cq2: c_query) (cr1 cr2: c_reply),
      ev_cp_rel ev1 (cq1, cr1) ->
      ev_cp_rel ev2 (cq2, cr2) ->
      det_event_coh objsig ev1 ev2 ->
      (True /\ (cq1 = cq2 -> cr1 = cr2)) /\
      ((cq1, cr1) = (cq2, cr2) -> ev1 = ev2).
  Proof.
    intros ev1 ev2 cq1 cq2 cr1 cr2 rel1 rel2 coh_ev.
    inversion rel1 as [ev1' cp1 id1 vf1 sg1 vargs1 vres1 m1].
    subst. clear rel1.
    inversion rel2 as [ev2' cp2 id2 vf2 sg2 vargs2 vres2 m2].
    subst. clear rel2.
    injection H5. clear H5. intros.
    injection H7. clear H7. intros.
    unfold det_event_coh in coh_ev.
    subst.
    repeat split.
    - intros eq_cp.
      injection eq_cp. clear eq_cp.
      intros eq_m eq_args eq_tres eq_targs eq_id.
      rewrite eq_m.
      admit. (* TODO: need injection between ArgRet and Values.val *)
    - intros eq_cp.
      injection eq_cp. clear eq_cp.
      intros eq_m eq_res _ eq_args eq_tres eq_targs eq_id.
      admit. (* TODO: need restriction on ObjSigImpl stating that id, args & res determintes unique event *)
  Admitted.

  Program Definition objsig2lic : objsig --o li_c :=
    {|
    has := fun '(ev, cp) => ev_cp_rel ev cp
    |}.
  Next Obligation.
    apply ev_cp_rel_coh; auto.
  Qed.

End DS_CC.
