Require Import compcert.common.AST. (* ident *)
Require Import List. (* :: *)
Require Import Coq.Classes.RelationClasses. (* relation *)
Require Import Coq.Relations.Relation_Definitions. (* Reflexive, Symmetric *)
Require Import models.Coherence.
Require Import deepsea.HyperTypeDef.
Require Import deepsea.HyperType.
Require Import deepsea.HyperTypeInst.

(* Definition ft_to_AR {htp:hyper_type_pair} (v : tp_ft htp) : ArgRet. *)

Definition function_return_dec (returns: hyper_type_pair) : bool :=
  match tp_ty returns with
  | Ctypes.Tvoid => false
  | _ => true
  end.

Fixpoint to_typelist argt :=
  match argt with
  | nil => Ctypes.Tnil
  | cons x xs => Ctypes.Tcons (tp_ty x) (to_typelist xs) 
  end.

Section OBJSIG.
  Class ObjSigImpl (event: Set) : Type :=
    {
    event_id : event -> ident;
    event_is_return : event -> bool;
    event_htp_res (e : event) : hyper_type_pair;
    event_htp_args (e : event) : list hyper_type_pair;
    event_res (e : event) : tp_ft (event_htp_res e);
    event_args (e : event): HList tp_ft (event_htp_args e);
    build_event (id: ident) (targs: list hyper_type_pair) (tres: hyper_type_pair): HList tp_ft targs -> tp_ft tres -> option event
    }.
(*
  Definition event_ty_res {event: Set} {objsig_impl: ObjSigImpl event} (e: event) : Values.val :=
    ht_cval (event_res e).

  Definition event_ty_args {event: Set} {objsig_impl: ObjSigImpl event} (e: event) : list Values.val :=
    HList_map_nodep (fun htp (v:tp_ft htp) => ht_cval v) (event_args e).
*)
  Definition event_AR_res {event: Set} {objsig_impl: ObjSigImpl event} (e: event) : ArgRet :=
    ht_AR (event_res e).

  Definition event_AR_args {event: Set} {objsig_impl: ObjSigImpl event} (e: event) : list ArgRet :=
    HList_map_nodep (fun htp (v:tp_ft htp) => ht_AR v) (event_args e).

  Class ObjSigProp (event : Set) {objsig_impl: ObjSigImpl event} : Prop :=
    {
    id_htp_res_eq e1 e2:
      event_id e1 = event_id e2 -> event_htp_res e1 = event_htp_res e2;
    id_htp_args_eq e1 e2:
      event_id e1 = event_id e2 -> event_htp_args e1 = event_htp_args e2;
    ARres e:
      if (event_is_return e)
      then HyperArgRet (tp_type_pair (event_htp_res e))
      else True;
    ARargs e:
      HList (fun htp => HyperArgRet (tp_type_pair htp)) (event_htp_args e)
    (* TODO: add more *)
    }.

  Record ObjSig : Type :=
    {
    event : Set;
    objsig_impl : ObjSigImpl event;
    objsig_prop : ObjSigProp event
    }.

End OBJSIG.
(*
Section Example.
  Require Import PArith.
  Inductive EvVar : Set :=
  | ev_get : Z -> EvVar
  | ev_set : Z -> EvVar
  .

  Instance evar_sig_impl: ObjSigImpl EvVar :=
    {
    event_id e := match e with
                  | ev_get _ => 1%positive
                  | ev_set _ => 2%positive
                  end;
    event_is_return e := match e with
                         | ev_get _ => true
                         | ev_set _ => false
                         end;
    event_htp_res e := match e with
                       | ev_get _ => int_Z32_pair
                       | ev_set _ => void_unit_pair
                       end;
    event_htp_args e := match e with
                        | ev_get _ => nil
                        | ev_set _ => int_Z32_pair :: nil
                        end;
    event_res e := match e with
                   | ev_get n => n
                   | ev_set _ => tt
                   end;
    event_args e := match e with
                    | ev_get _ => HNil
                    | ev_set n => HCons int_Z32_pair nil n HNil
                    end
    }.
  Admitted.

  Instance evar_sig_prop: ObjSigProp EvVar.
  Proof.
    split.
    - (* id_htp_res_eq *)
      intros e1 e2 Hid.
      destruct e1, e2; simpl in Hid; try discriminate; reflexivity.
    - (* id_htp_args_eq *)
      intros e1 e2 Hid.
      destruct e1, e2; simpl in Hid; try discriminate; reflexivity.
    - (* ARres *)
      intros e.
      destruct e; simpl.
      + typeclasses eauto.
      + exact I.
    - (* ARargs *)
      intros e.
      destruct e; simpl.
      + constructor.
      + constructor; simpl. typeclasses eauto.
        constructor.
  Qed.
End Example.
*)
Section COHERENT.
  Variable objsig : ObjSig.
  Existing Instance objsig_impl.
  Existing Instance objsig_prop.

  Definition det_event_coh: relation (event objsig) :=
    fun ev1 ev2 =>
      event_id ev1 = event_id ev2 ->
      event_AR_args ev1 = event_AR_args ev2 ->
      event_AR_res ev1 = event_AR_res ev2.

  Lemma det_event_coh_Reflexive:
    Reflexive det_event_coh.
  Proof.
    intros ev. unfold det_event_coh.
    reflexivity.
  Qed.

  Lemma det_event_coh_Symmetric:
    Symmetric det_event_coh.
  Proof.
    intros ev1 ev2. unfold det_event_coh.
    intros.
    symmetry.
    firstorder.
  Qed.
End COHERENT.

Coercion det_event_space (objsig : ObjSig) : space :=
  {|
  coh := det_event_coh objsig;
  coh_refl := det_event_coh_Reflexive _;
  coh_symm := det_event_coh_Symmetric _
  |}.

Definition det_trace_space (objsig: ObjSig) : space := !objsig.

Section ACTIVE.
  Definition active_element {A} (P: list A -> Prop) : Prop :=
    forall x xs, P (x::xs) -> P xs.

  Lemma active_element_is_prefix_closed {A} {P: list A -> Prop}:
    active_element P ->
    forall pfx xs, P (pfx++xs) -> P xs.
  Proof.
    intros activeP pfx xs.
    induction pfx; firstorder.
  Qed.

End ACTIVE.

Section DS_OBJECT.
  Record DSObject (objsig: ObjSig) : Type :=
    {
    trace_inv  : token (!objsig) -> Prop;
    obj_active : active_element trace_inv;
    obj_coh    : forall tr1 tr2, trace_inv tr1 -> trace_inv tr2 -> coh tr1 tr2
    }.
  Arguments trace_inv {_}.
  Arguments obj_active {_}.
  Arguments obj_coh {_}.

  Coercion DSObject_clique {objsig: ObjSig} (dsobj: DSObject objsig)
    : clique (!objsig) :=
    {|
      has := trace_inv dsobj;
      has_coh := obj_coh dsobj
    |}.
End DS_OBJECT.
