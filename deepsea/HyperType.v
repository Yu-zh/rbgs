(* *********************************************************************)
(*    DeepSpec, the language of certified softwares                    *)
(*                                                                     *)
(*      Shu-Chun Weng, Yale University                                 *)
(*                                                                     *)
(*  Copyright (c) 2013-2015 Shu-Chun Weng <shu-chun.weng@yale.edu>.    *)
(*                                                                     *)
(*  This program is free software; you can redistribute it and/or      *)
(*  modify it under the terms of the GNU General Public License        *)
(*  version 2 as published by the Free Software Foundation.  Note that *)
(*  the only valid version of the GPL for this work is version 2, not  *)
(*  v2.2 or v3.x or whatever.                                          *)
(*                                                                     *)
(*  This program is distributed in the hope that it will be useful,    *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(*  GNU General Public License for more details.                       *)
(*                                                                     *)
(*  You should have received a copy of the GNU General Public License  *)
(*  along with this program; if not, write to the Free Software        *)
(*  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,         *)
(*  MA 02110-1301 USA.                                                 *)
(* *********************************************************************)

(** CompCert Clight [type] expressions bundled with Coq [Type]s and
    type class declarations describing properties of the bundles.  *)

(* Standard library modules *)
Require Import BinInt.  (* Z_scope, (_ | _) *)

(* CompCert modules *)
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Coqlib. (* list related *)

(* DeepSpec modules *)
Require Import deepsea.Cval.
Require Import deepsea.OProp.
Require Export deepsea.HyperTypeDef.

Section HYPER_TYPE.
  (* never used. TODO: delete it *)
  (*
  Definition ContOpt_correct `{HyperTypeImpl}(m : ContOpt (unpair_ft tp)) v' :=
    forall B k b, m B k = Some b ->
      exists a, ht_ft_cond a /\ v' = Some (ht_cval a) /\
        forall B' k', m B' k' = k' a.
   *)
  Class HyperByValueType (tp : type_pair)`{hti : HyperTypeImpl tp}(ch : memory_chunk) : Prop := {
    (* [Tlong] alignment misbehaves *)
    ht_by_value_not_64bits : ch <> Mint64;

    (* Access by value: by loading from memory using the memory chunk [ch] *)
    ht_by_value_access_mode : access_mode (unpair_ty tp) = By_value ch;
    ht_by_value_naturally_aligned : naturally_aligned (unpair_ty tp);
    (* Storing C value by chunk [c], no BS happens *)
    ht_by_value_load_result :
      forall f v,
        ht_valid_ft_cond f ->
        ht_rel f v ->
        Val.load_result ch v = v;
    (* Type-casting from [ty] to [ty], no BS happens *)
    ht_by_value_sem_cast :
      forall f v,
        ht_valid_ft_cond f ->
        ht_rel f v ->
        sem_cast v (unpair_ty tp) (unpair_ty tp) Mem.empty = Some v
  }.
  (* Requirements for a type to be function parameter or return value. *)
  Class HyperArgRet (tp : type_pair)`{hti : HyperTypeImpl tp} : Prop := {
    (* This is a basic type, i.e., int, long or float *)
    ht_basic : forall f, ht_ft_cond f -> ht_valid_ft_cond f ->
      cval_basic (ht_cval f);
    (* Type-casting from [ty] to [ty], no BS happens *)
    ht_cast_ident : forall v, @ht_valid_ty_cond tp _ v ->
      cval_cast v (unpair_ty tp) (unpair_ty tp) = Some v;
    (* [cval]s equal, then coq values equal *)
    ht_injective : forall f f',
      ht_ft_cond f -> ht_ft_cond f' ->
      ht_valid_ft_cond f -> ht_valid_ft_cond f' ->
      ht_cval f = ht_cval f' -> f = f';
    (* [val] is of [typ] *)
    ht_has_type : forall v f,
      ht_ft_cond f -> ht_valid_ft_cond f -> ht_rel f v ->
      Val.has_type v (typ_of_type (unpair_ty tp))
  }.

  (** * Operations *)
  (** This part encodes the interface of [Cop] in type classes.  All
      operations equip with:
      - extra preconditions,
      - the computation itself in Coq functions,
      - lemma requiring the result of the computation stays in the domain,
        and
      - lemmas stating that the computation agrees with their counterparts
        in [Cop]:
        [_fcorrect] means the computation correctly casts a functional
        value w.r.t. Clight semantics, and [_ccorrect] means that when the
        Clight semantics exist, the function computation reproduces them.
  *)
  (** [HyperCast] encodes [sem_cast].  *)
  Class HyperCastImpl (from to : type_pair) : Type := {
    Hcast_cond : unpair_ft from -> Prop;
    Hcast_ocond : OProp1 (unpair_ft from);
    Hcast : unpair_ft from -> unpair_ft to
  }.
  Class HyperCast (from to : type_pair)
     `{HyperTypeImpl from, HyperTypeImpl to, !HyperCastImpl from to} : Prop := {
    Hcast_ocond_same : forall f, Hcast_cond f <-> oProp1 Hcast_ocond f;
    Hcast_returns : forall f, ht_ft_cond f -> Hcast_cond f ->
                              ht_ft_cond (Hcast f);
    Hcast_correct : forall f v, ht_ft_cond f -> Hcast_cond f -> ht_cval f = v ->
      ht_cval_some (Hcast f) (cval_cast v (unpair_ty from) (unpair_ty to))

  }.
  Class HyperCastPassthrough (from to : type_pair)
     `{HyperTypeImpl from, HyperTypeImpl to, !HyperCastImpl from to} : Prop := {
  }.

  (** [HyperUnaryOp] encodes [sem_unary_operation].  However, unlike
      [sem_unary_operation] which only takes _one_ [type], these
      type classes takes _two_ [type_pair]s since in some situations,
      although the C type remains the same, the meaning changes and
      a different functional type would fit better.  For example,
      when taking the boolean negation ([!]) on a [tint] associated
      with [Z], the resulting C type is still [tint] but it only
      makes sense to interprete the functional result in [bool].  *)
  Class HyperUnaryImpl (op : unary_operation)(tp tpo : type_pair) : Type := {
    (* operator pre-condition *)
    Hunary_cond : unpair_ft tp -> Prop;
    Hunary_ocond : OProp1 (unpair_ft tp);

    (* operator body *)
    Hunary : unpair_ft tp -> unpair_ft tpo
  }.
  Class HyperUnaryOp (op : unary_operation)(tp tpo : type_pair)
     `{hti : HyperTypeImpl tp, htio : HyperTypeImpl tpo, !HyperUnaryImpl op tp tpo}
      : Prop := {
    Hunary_ocond_same : forall f, Hunary_cond f <-> oProp1 Hunary_ocond f;
    (* operator post-condition *)
    Hunary_returns : forall f, ht_ft_cond f -> Hunary_cond f ->
      ht_ft_cond (Hunary f);

    (* f ----Hunary----> _
       |                 |
    ht_cval          ht_cval_some
       |                 |
       v --cval_unary--> _ *)
    Hunary_correct : forall f v, ht_ft_cond f -> Hunary_cond f -> ht_cval f = v ->
      ht_cval_some (Hunary f) (cval_unary_operation op v (unpair_ty tp))
  }.
  Class HyperUnaryPassthrough op (tp tpo : type_pair)
     `{hti : HyperTypeImpl tp, htio : HyperTypeImpl tpo, !HyperUnaryImpl op tp tpo}
     : Prop := {
  }.

  (** Finally, [HyperBinaryOp] encodes [sem_binary_operation].  Every thing
      is standard except for [Hbinary_mem_irr], memory irrelevance, requiring
      that the defined binary computation does not depend on the memory
      (not even the "shape" of the memory, hence possibly two different
      abstract data.  *)
  Class HyperBinaryImpl (op : binary_operation)(tpl tpr tpo : type_pair)
      : Type := {
    (* pre-condition and body *)
    Hbinary_cond : unpair_ft tpl -> unpair_ft tpr -> Prop;
    Hbinary_ocond : OProp2 (unpair_ft tpl) (unpair_ft tpr);
    Hbinary : unpair_ft tpl -> unpair_ft tpr -> unpair_ft tpo
  }.
  Class HyperBinaryOp (op : binary_operation)(tpl tpr tpo : type_pair)
     `{htil : HyperTypeImpl tpl, htir : HyperTypeImpl tpr,
       htio : HyperTypeImpl tpo, !HyperBinaryImpl op tpl tpr tpo} : Prop := {
    Hbinary_ocond_same : forall f f', Hbinary_cond f f' <->
                                      oProp2 Hbinary_ocond f f';
    (* HyperBinaryOp's user also requires op to not look at the memory. *)
    Hbinary_mem_irr (* {mem mem'}`{Mem.MemoryModelOps mem, Mem.MemoryModelOps mem'} : *):
      forall (m : mem)(m' : mem) v v',
      sem_binary_operation (PTree.empty _) op v (unpair_ty tpl) v' (unpair_ty tpr) m =
      sem_binary_operation (PTree.empty _) op v (unpair_ty tpl) v' (unpair_ty tpr) m';

    (* post-condition *)
    Hbinary_returns : forall f f', ht_ft_cond f -> ht_ft_cond f' ->
      Hbinary_cond f f' -> ht_ft_cond (Hbinary f f');

    Hbinary_correct (* `{Mem.MemoryModelOps} *) : forall f f' v v',
      ht_ft_cond f -> ht_ft_cond f' -> Hbinary_cond f f' ->
      ht_cval f = v -> ht_cval f' = v' ->
      ht_cval_some (Hbinary f f') (cval_binary_operation op v (unpair_ty tpl)
                                                            v' (unpair_ty tpr))
  }.
  Class HyperBinaryPassthrough op (tpl tpr tpo : type_pair)
     `{htil : HyperTypeImpl tpl, htir : HyperTypeImpl tpr,
       htio : HyperTypeImpl tpo, !HyperBinaryImpl op tpl tpr tpo} : Prop := {
  }.

End HYPER_TYPE.

Section HLIST_PROPS.
  (* Context`{LayerSpecClass}. *)

  Inductive ht_list_rel : forall ls, HList tp_ft ls -> list val -> Prop :=
  | ht_nil_rel : ht_list_rel nil HNil nil
  | ht_cons_rel : forall htp ls f fs v vs,
    ht_rel f v -> ht_list_rel ls fs vs ->
    ht_list_rel (cons htp ls) (HCons htp ls f fs) (cons v vs).

  Inductive ht_list_ft_cond :
      forall {ls}(es1 : HList tp_ft ls), Prop :=
  | ht_nil_ft_cond : ht_list_ft_cond HNil
  | ht_cons_ft_cond : forall htp ls e es,
    ht_ft_cond e -> ht_list_ft_cond es ->
    ht_list_ft_cond (HCons htp ls e es).
  
  Inductive ht_list_valid_ft_cond:
    forall {ls} (es1 : HList tp_ft ls), Prop :=
  | ht_nil_valid_ft_cond: ht_list_valid_ft_cond HNil
  | ht_cons_valid_ft_cond: forall htp ls e es,
      ht_valid_ft_cond e -> ht_list_valid_ft_cond es ->
      ht_list_valid_ft_cond (HCons htp ls e es).

End HLIST_PROPS.

(* This is "legacy code": this definition turned out to not be quite right, but a lot of things were implemented using it,
   so we provide wrappers to convert to the newer version above. *)

Section ISO_TYPE.
  Class HyperTypeIsoImpl (tp : type_pair) : Type := {
    ht_iso_ft_cond : unpair_ft tp -> Prop;
    ht_iso_ty_cond : val -> Prop;

    ht_iso_default : unpair_ft tp;
    ht_iso_AR : unpair_ft tp -> ArgRet;

    ht_implement : unpair_ft tp -> val;
    ht_spec : val -> unpair_ft tp
  }.
  Class HyperTypeIso (tp : type_pair)`{hti : HyperTypeIsoImpl tp} : Prop := {
    ht_implement_returns : forall f, ht_iso_ft_cond f -> ht_iso_ty_cond (ht_implement f);
    ht_spec_returns : forall v, ht_iso_ty_cond v -> ht_iso_ft_cond (ht_spec v);

    ht_iso_default_ft_cond : ht_iso_ft_cond ht_iso_default;
    ht_iso_has_type : forall v, ht_iso_ty_cond v ->
      Val.has_type v (typ_of_type (unpair_ty tp));

    ht_proof_left : forall f, ht_iso_ft_cond f -> ht_spec (ht_implement f) = f;
    ht_proof_right : forall v, ht_iso_ty_cond v -> ht_implement (ht_spec v) = v
  }.
  Global Arguments ht_iso_ty_cond tp {_} v.

  Context`{HyperTypeIso}.

  Global Instance hyper_type_iso_impl : HyperTypeImpl tp := {
    ht_cval f := ht_implement f;
    ht_ft_cond := ht_iso_ft_cond;
    ht_default := ht_iso_default;
    ht_AR := ht_iso_AR;
    ht_valid_ft_cond f := True;
    ht_valid_ft_ocond := otrue1
  }.
  Global Instance hyper_type_iso : HyperType tp.
  Proof. esplit.
    - (* ht_ft_rel_core *)
      intros f fc.
      eexists; reflexivity.
    - (* ht_default_ft_cond *)
      simpl.
      apply ht_iso_default_ft_cond.
    - (* ht_valid_ft_ocond_same *)
      simpl; split; trivial.
  Qed.
End ISO_TYPE.

