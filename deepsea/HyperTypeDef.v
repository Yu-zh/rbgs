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
Require Import List. (* :: *)

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

(* DeepSpec modules *)
Require Import deepsea.CvalDef.
Require Import deepsea.OProp.
(* Require Import DeepSpec.lib.Monad.ContOptionMonad. *)

Inductive type_marker {T} (t : T) := create_type_marker : type_marker t.

Section HYPER_TYPE.
  (** * Basic Clight-Coq type linking *)

  (** A [type_pair] encapsulates [ty : type], a Clight type from [Ctypes],
      and [ft : Type], the functional correspondence.  *)
  Inductive type_pair : Type :=
    Tpair : Type -> type -> type_pair.

  Definition unpair_ty tp := match tp with Tpair _ ty => ty end.
  Definition unpair_ft tp := match tp with Tpair ft _ => ft end.


  (** [HyperType] and its implementation counterpart [HyperTypeImpl] describes
      the minimum requirement for a pair of types to be bundled together.
      Since [HyperTypeImpl] is a super class of [HyperType] that provides no
      reasoning capacity, you always want to use [HyperType] with the
      generalizing binders.

      [HyperTypeImpl] contains the following four fields.

      - [ht_ty_cond] identifies C values that are valid for this [type_pair],
      - [ht_ft_cond] identifies Coq values that are valid for this [type_pair],

      - [ht_implement] converts the functional value to C value, and
      - [ht_spec] converts the C value to it's functional meaning
        (specification).

      For example, we may bundle [tint] as defined above (which is actually
      [unsigned int]) with [bool] type.  We can define [ht_ty_cond] to accept
      only [Vtrue] and [Vfalse], and [ht_ft_cond] accepts all possible values
      of [bool] type: [true] and [false].  Naturally, [ht_implement] can be
      defined ot turn [true] into [Vtrue] and [false] into [Vfalse], and
      [ht_spec] does the inverse.

      To ensure that the conditions and conversions are well behaved,
      [HyperType] enforces six lemmas.

      - FIXME: ht_val_has_type, ht_sem_cast_ident
      - [ht_implement_returns] says that [ht_implement] always brings valid
        functional value to valid C value,
      - [ht_spec_returns] ensures the same for [ht_spec],
      - [ht_proof_left] and [ht_proof_right] mean that [ht_spec] is
        [ht_implement]'s left and right inverse, respectively.

      For the [tint] and [bool] bundle, these four trivially hold.  However,
      if we accidentally swapped the mapping in, say, [ht_spec], the two
      [_returns] lemmas still hold, but not the two [ht_proof].  *)
  (* Provides some operators on this type_pair *)
  Variant ArgRet : Set :=
  | ARZ : Z -> ArgRet
  | ARbool : bool -> ArgRet
  | ARunit : ArgRet
  .

  Class HyperTypeImpl (tp : type_pair) : Type := {
    (* Coq value to [cval] *)
    ht_cval : unpair_ft tp -> val;
    (* Default coq value *)
    ht_default : unpair_ft tp;

    (* to uniform *)
    ht_AR : unpair_ft tp -> ArgRet;

    (* Defines what are valid coq values *)
    ht_ft_cond : unpair_ft tp -> Prop;
    (* defines what are valid cval *)
    ht_ty_cond : val -> Prop
               := fun cv => exists f, ht_ft_cond f /\ ht_cval f = cv;

    (* Defines what can be represented by a meaningful C value. Sometimes, 
     * satisfying ht_ft_cond does not necessary implies ht_valid_ft_cond. take 
     * ATInfo from memory management as an example: ATValid corresponds to a valid
     * struct data, while ATUndef means this memory region is not initialized.
     * Both branches are valid coq value, but ATUndef can not be represented by
     * a meaningful C value, and ht_cval usually converts it into CVany.
     * This property is only required for: function args and ret, data to be stored,
     * and struct to be accessed.
     *)
    ht_valid_ft_cond : unpair_ft tp -> Prop;
    ht_valid_ty_cond : val -> Prop
      := fun cv => exists f, ht_valid_ft_cond f /\ ht_ft_cond f /\ ht_cval f = cv;

    (* Almost the same as [ht_valid_ft_cond], but uses [oprop] *)
    ht_valid_ft_ocond : OProp1 (unpair_ft tp)
  }.
  (* Properties of [HyperTypeImpl]'s operators *)
  Class HyperType (tp : type_pair)`{hti : HyperTypeImpl tp} : Prop := {
    (* Valid coq value can be converted into [cval] *)
    (* This is trivial since ht_cval is total, it is just a utility to help prove ht_ft_rel. *)
    ht_ft_rel_core : forall f, ht_ft_cond f -> exists cv, ht_cval f = cv;

    (* The above converted [cval] is valid *)
    ht_ft_rel : forall f, ht_ft_cond f -> exists cv, ht_ty_cond cv /\ ht_cval f = cv
      := fun f fc => match ht_ft_rel_core f fc with ex_intro cv r =>
           ex_intro _ cv (conj (ex_intro _ f (conj fc r)) r) end;
    (* Valid [cval] has valid preimage coq value *)
    ht_ty_rel : forall cv, ht_ty_cond cv -> exists f, ht_ft_cond f /\ ht_cval f = cv
      := fun cv vc => vc;

    (* Default coq value is valid *)
    ht_default_ft_cond : ht_ft_cond ht_default;

    (* [ht_valid_ft_cond] is equivalent to [ht_valid_ft_ocond] *)
    ht_valid_ft_ocond_same :
      forall f, ht_valid_ft_cond f <-> oProp1 ht_valid_ft_ocond f
  }.

  (* [ht_cval] on option types *)
  Inductive ht_option_cval `{HyperTypeImpl} :
      option (unpair_ft tp) -> option val -> Prop :=
  | ht_none_cval : ht_option_cval None None
  | ht_some_cval : forall f v, ht_cval f = v -> ht_option_cval (Some f) (Some v).
  Definition ht_cval_some `{HyperTypeImpl} f vo := ht_option_cval (Some f) vo.

  (* Connect Coq value with val. *)
  (* Coq value --[ht_cval]--> cval --[cval_match]--> val *)
  Definition ht_rel `{HyperTypeImpl} f v :=
    cval_match v (ht_cval f).
  Inductive ht_option_rel `{HyperTypeImpl} :
      option (unpair_ft tp) -> option val -> Prop :=
  | ht_none_rel : ht_option_rel None None
  | ht_some_rel : forall f v, ht_rel f v -> ht_option_rel (Some f) (Some v).
  Definition ht_rel_some `{HyperTypeImpl} f vo :=
    ht_option_rel (Some f) vo.

  (** By default, [ht_ty_cond], which is a class member, only takes a [val]
      explicit argument, everything else is searched by [eauto] using the
      typeclass instance hint database.  This results in problems when multiple
      [HyperType]s are defined in the environment, so we force the type-pair
      argument [tp] be explicit. *)
  Global Arguments ht_ty_cond tp {_} v.
  Global Arguments ht_valid_ty_cond tp {_} cv.

  (** Bundling the [HyperType] instances with the [type_pair] for places
      where generalizing binders are not available (in positive positions,
      for example).  *)
  Class hyper_type_pair : Type := mk_hyper_type_pair {
    _tp_type_pair      : type_pair;
    _tp_ty             := unpair_ty _tp_type_pair;
    _tp_ft             := unpair_ft _tp_type_pair;
    tp_hyper_type_impl :> HyperTypeImpl _tp_type_pair
  }.
  Definition tp_type_pair := @_tp_type_pair.
  Definition tp_ty        := @_tp_ty.
  Definition tp_ft        := @_tp_ft.
  (* begin hide *)
  Global Arguments mk_hyper_type_pair _ {_}.
  (* end hide *)

End HYPER_TYPE.

Add Printing Constructor hyper_type_pair.

(* Heterogeneous List *)
Section HLIST.
  Inductive HList (F : hyper_type_pair -> Type) :
      list hyper_type_pair -> Type :=
  | HNil  : HList F nil
  | HCons : forall (x : hyper_type_pair)(ls : list hyper_type_pair),
              F x -> HList F ls -> HList F (x :: ls).
  Global Arguments HNil {_}.
  Global Arguments HCons {_} _ _ _ _.
  
  Definition hlist_hd {a b F} (hlist : HList F (a :: b)) : F a :=
    match hlist in HList _ x return match x with
                                    | nil => unit
                                    | cons a _ => F a
                                    end with
    | HNil => tt
    | HCons _ _ x _ => x
    end.

  Definition hlist_tl {a b F} (hlist : HList F (a :: b)) : HList F b :=
    match hlist in HList _ x return match x with
                                    | nil => unit
                                    | cons _ ls => HList F ls
                                    end with
    | HNil => tt
    | HCons _ _ _ x => x
    end.

  Fixpoint HList_map_nodep {a F A}
    (f : forall htp : hyper_type_pair, F htp -> A)(hlist : HList F a) :
      list A :=
    match hlist with
    | HNil => nil
    | HCons x _ y hl => cons (f x y) (HList_map_nodep f hl)
    end.

  Fixpoint HList_map {a F G}
    (f : forall htp : hyper_type_pair, F htp -> G htp)(hlist : HList F a) :
      HList G a :=
    match hlist with
    | HNil => HNil
    | HCons x _ y hl => HCons _ _ (f x y) (HList_map f hl)
    end.

  Fixpoint HList_fold_right_nodep {a F A}
      (f : forall htp : hyper_type_pair, F htp -> A -> A)(a0 : A)
      (hlist : HList F a) : A :=
    match hlist with
    | HNil => a0
    | HCons x _ y hl => f x y (HList_fold_right_nodep f a0 hl)
    end.

  Fixpoint list_curried_type (params : list hyper_type_pair) T : Type :=
    match params with
    | nil => T
    | htp :: l => tp_ft htp -> list_curried_type l T
    end.

  Fixpoint apply_curried_func {params T} :
      list_curried_type params T -> HList tp_ft params -> T :=
    match params with
    | nil => fun t _ => t
    | htp :: l => fun f hlist => @apply_curried_func l T
                                   (f (hlist_hd hlist)) (hlist_tl hlist)
    end.
End HLIST.
