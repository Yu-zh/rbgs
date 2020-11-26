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

(** Primitive type pairing and operators on them. *)

(* Standard library modules *)
Require Import ZArith.
Require Import Znumtheory.
Require Import Bool.

(* CompCert modules *)
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Coqlib. (* zlt *)

(* XXX: mCertiKOS module to allow reusing operations on [globalpointer]s *)
(* Require        mcertikos.layerlib.AuxStateGlobalPointer. *)

(* DeepSpec modules *)

Require Import deepsea.Cval.
Require Import deepsea.HyperType.
Require Import deepsea.OProp.

(** * [unit] corresponds to [void] *)
Notation tvoid_unit := (Tpair unit Tvoid).

Section HYPER_TYPE_UNIT.
  Global Instance void_unit_impl : HyperTypeImpl tvoid_unit := {
    ht_cval := fun _ => Vundef;
    ht_ft_cond := fun _ => True;
    ht_default := tt;
    ht_AR := fun _ => ARunit;
    ht_valid_ft_cond := fun _ => False;
    ht_valid_ft_ocond := ofalse1
  }.
  Global Instance void_unit : HyperType tvoid_unit.
  Proof. esplit.
    - (* ht_ft_rel_core *)
      intros.
      eexists.
      reflexivity.

    - (* ht_default_ft_cond *)
      exact I.

    - (* ht_valid_ft_ocond_same *)
      simpl; split; trivial.
  Qed.

  Definition void_unit_pair := mk_hyper_type_pair tvoid_unit.

(* Needed in  semof_nil_ft_pure_props *)
  Global Instance void_unit_arg_ret : HyperArgRet tvoid_unit.
  Proof.
    esplit; simpl; try tauto.
  Qed.

End HYPER_TYPE_UNIT.
(*
Notation globalpointer := AuxStateGlobalPointer.globalpointer.
Notation GLOBP := AuxStateGlobalPointer.GLOBP.
Notation GLOBUndef := AuxStateGlobalPointer.GLOBUndef.
Notation tchar_pointer_globalpointer := (Tpair globalpointer (Tpointer tchar noattr)).

Section HYPER_TYPE_GLOBALPOINTER.
  Global Instance tchar_pointer_globalpointer_hyper_type_impl
      : HyperTypeImpl tchar_pointer_globalpointer := {
    ht_cval f := match f with
      | GLOBP i ofs => CVval (Vptr i ofs)
      | GLOBUndef => CVval Vundef
      end;
    ht_ft_cond := fun _ => True;
    ht_default := GLOBUndef;
    ht_valid_ft_cond f := match f with
      | GLOBP _ _ => True
      | GLOBUndef => False
      end;
    ht_valid_ft_ocond := oprop1 (fun f => match f with
      | GLOBP _ _ => True
      | GLOBUndef => False
      end)
  }.
  Global Instance tchar_pointer_globalpointer_hyper_type : HyperType tchar_pointer_globalpointer.
  Proof. esplit.
    - (* ht_ft_rel_core *)
      intros [ i ofs |] _.
      + exists (CVval (Vptr i ofs)); reflexivity.
      + exists (CVval Vundef); constructor.

    - (* ht_default_ft_cond *)
      exact I.

    - (* ht_valid_ft_ocond_same *)
      simpl; split; trivial.
  Qed.

  Definition char_pointer_globalpointer_pair :=
    mk_hyper_type_pair tchar_pointer_globalpointer.
End HYPER_TYPE_GLOBALPOINTER.
*)
(** * Integers as booleans *)
(*Notation tint := (Tint I32 Unsigned noattr).*)
Notation tint_bool := (Tpair bool tint).

Section IntegerExtra.
Lemma modulus_gt_zero : Int.modulus > 0.
Proof.
  unfold Z.gt, Z.compare, Int.modulus, two_power_nat;
  reflexivity.
Qed.

Theorem sub_sub : forall x y z,
    Int.sub (Int.sub x y) z = Int.sub x (Int.add y z).
Proof.
    intros x y z.
    rewrite (Int.sub_add_opp x), Int.sub_add_l.
    symmetry; apply Int.sub_add_r.
Qed.

Theorem Int_eqmod_mod x:
  Int.eqm x (x mod Int.modulus).
Proof.
  intros. red. apply Zbits.eqmod_mod.
  apply Int.modulus_pos.
Qed.

Theorem add_repr : forall x y,
    Int.add (Int.repr x) (Int.repr y) = Int.repr (x + y).
Proof.
  intros x y.
  rewrite Int.add_unsigned.
  apply Int.eqm_samerepr, Int.eqm_add;
    rewrite Int.unsigned_repr_eq;
  apply Int.eqm_sym, Int_eqmod_mod.
Qed.

Theorem sub_repr : forall x y,
    Int.sub (Int.repr x) (Int.repr y) = Int.repr (x - y).
Proof.
  intros x y.
  unfold Int.sub.
  apply Int.eqm_samerepr, Int.eqm_sub;
    rewrite Int.unsigned_repr_eq;
    apply Int.eqm_sym, Int_eqmod_mod.
Qed.

Theorem mul_repr : forall x y,
    Int.mul (Int.repr x) (Int.repr y) = Int.repr (x * y).
Proof.
  intros x y.
  unfold Int.mul.
  apply Int.eqm_samerepr, Int.eqm_mult;
    rewrite Int.unsigned_repr_eq;
    apply Int.eqm_sym, Int_eqmod_mod.
Qed.

Theorem add_shifted : forall x y z,
    Int.add (Int.sub x z) (Int.add y z) = Int.add x y.
Proof.
  intros x y z.
  rewrite Int.add_permut, Int.sub_add_opp, Int.add_assoc,
         (Int.add_commut (Int.neg z)), Int.add_neg_zero, Int.add_zero.
  apply Int.add_commut.
Qed.
End IntegerExtra.

Section HYPER_TYPE_BOOL.
  Local Open Scope Z_scope.

  Lemma small_modulo : 0 mod Int.modulus = 0 /\ 1 mod Int.modulus = 1.
  Proof.
    split; apply Zmod_small; split;
      try solve
        [ apply Zle_refl |
          unfold Int.modulus, two_power_nat, Z.lt, Z.compare; trivial ].

    apply Zlt_le_weak.
    assert (1 = Z.succ 0).
      unfold Z.succ, Z.add; reflexivity.
    rewrite H; apply Zle_lt_succ.
    apply Zle_refl.
  Qed.
  Definition zero_mod_modulus := proj1 small_modulo.
  Definition one_mod_modulus := proj2 small_modulo.
  Ltac rewrite_unsigned_repr :=
    try unfold Int.zero, Int.one;
    rewrite Int.unsigned_repr_eq;
    try rewrite zero_mod_modulus;
    try rewrite one_mod_modulus.
(*
  Global Instance int_bool_impl : HyperTypeImpl tint_bool :=
    {
    ht_cval f := Vint (if f then Int.one else Int.zero);
    ht_default := false;
    ht_AR f := ARbool f;
    ht_ft_cond f := True;
    ht_valid_ft_cond f := True;
    ht_valid_ft_ocond := otrue1
    }.
*)

  Local Instance int_bool_iso_impl : HyperTypeIsoImpl tint_bool := {
    ht_iso_ty_cond v := match v with
      | Vint i => Int.unsigned i = 0 \/ Int.unsigned i = 1
      | _ => False
      end;
    ht_iso_ft_cond f := True;

    ht_iso_default := false;
    ht_iso_AR f := ARbool f;

    ht_implement f := Vint (if f then Int.one else Int.zero);
    ht_spec v := match v with
      | Vint i => Int.unsigned i =? 1
      | _ => false
      end
  }.

(*
  Global Instance int_bool : HyperType tint_bool.
  Proof.
    esplit.
    - (* ht_ft_rel_core *)
      intros f.
    - (* ht_default_ft_cond *)
    - (* ht_valid_ft_ocond_same *)
*)

  Local Instance int_bool_iso : HyperTypeIso tint_bool.
  Proof. esplit.
    - (* ht_implement_returns *)
      intros; simpl.
      destruct f; simpl; rewrite_unsigned_repr; [ right | left ]; reflexivity.

    - (* ht_spec_returns *)
      intros; simpl.
      trivial.

    - (* ht_iso_default_ft_cond *)
      exact I.

    - (* ht_iso_has_type *)
      intros [] vc; try contradiction vc.
      simpl; trivial.

    - (* ht_proof_left *)
      intros; simpl.
      destruct f; simpl; rewrite_unsigned_repr; reflexivity.

    - (* ht_proof_right *)
      intros v vc; simpl in vc |- *.
      destruct v; try contradiction.
      destruct vc as [ H | H ]; rewrite H; simpl;
        unfold Vtrue, Vfalse, Int.zero, Int.one;
        rewrite <- H; rewrite (Int.repr_unsigned i); reflexivity.
  Qed.
  Global Instance int_bool_impl : HyperTypeImpl tint_bool := _.
  Global Instance int_bool : HyperType tint_bool := _.
  Global Instance int_bool_by_value : HyperByValueType tint_bool _ := {
    ht_by_value_access_mode := eq_refl
  }.
  Proof.
    - discriminate.
    - simpl. tauto.
    - inversion 2; subst; clear H0.
      injection H1 as <-; reflexivity.
    - inversion 2; subst; clear H0.
      injection H1 as <-; reflexivity.
  Qed.
  Global Instance int_bool_arg_ret : HyperArgRet tint_bool.
  Proof. esplit.
    - (* ht_basic *)
      intros f valid.
      simpl; destruct f; constructor.
    - (* ht_sem_cast_ident *)
      intros v (f & fvc & fc & rel); simpl in rel |- *.
      rewrite <- rel.
      destruct f; reflexivity.
    - (* ht_injective *)
      intros [] [] _ _; solve [ reflexivity | discriminate ].
    - (* ht_has_type *)
      destruct f; simpl; inversion 3;
        injection H2 as <-; exact I.
  Qed.

  Definition int_bool_pair :=
    @mk_hyper_type_pair tint_bool int_bool_impl.

  Lemma ht_ty_cond_0_1 :
      ht_ty_cond tint_bool (Vint (Int.repr 0)) /\
      ht_ty_cond tint_bool (Vint (Int.repr 1)).
  Proof.
    split; [ exists false | exists true ]; split;
      solve [ exact I | reflexivity ].
  Qed.
  Definition int_bool_zero := proj1 ht_ty_cond_0_1.
  Definition int_bool_one  := proj2 ht_ty_cond_0_1.

  Global Instance int_bool_notbool_impl
      : HyperUnaryImpl Onotbool tint_bool tint_bool := {
    Hunary_cond ft := True;
    Hunary_ocond := otrue1;
    Hunary := negb
  }.
  Global Instance int_bool_notbool : HyperUnaryOp Onotbool tint_bool tint_bool.
  Proof. esplit.
    - (* Hunary_ocond_same *)
      reflexivity.

    - (* Hunary_returns *)
      simpl; trivial.

    - (* Hunary_correct *)
      intros f v fc oc rel.
      simpl in rel; rewrite <- rel.
      destruct f; constructor; reflexivity.
  Qed.
  Global Instance int_bool_notbool_passthrough
      : HyperUnaryPassthrough Onotbool tint_bool tint_bool.

  Global Instance int_bool_or_impl
      : HyperBinaryImpl Oor tint_bool tint_bool tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := orb
  }.
  Global Instance int_bool_or
    : HyperBinaryOp Oor tint_bool tint_bool tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; simpl; tauto.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel'; rewrite <- rel, <- rel'.
      destruct f; destruct f';
        constructor; reflexivity.
  Qed.
  Global Instance int_bool_or_passthrough
      : HyperBinaryPassthrough Oor tint_bool tint_bool tint_bool.

  Global Instance int_bool_xor_impl
      : HyperBinaryImpl Oxor tint_bool tint_bool tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := xorb
  }.
  Global Instance int_bool_xor
      : HyperBinaryOp Oxor tint_bool tint_bool tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; simpl; tauto.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel'; rewrite <- rel, <- rel'.
      destruct f; destruct f';
        constructor; reflexivity.
  Qed.
  Global Instance int_bool_xor_passthrough
      : HyperBinaryPassthrough Oxor tint_bool tint_bool tint_bool.

  Global Instance int_bool_and_impl
      : HyperBinaryImpl Oand tint_bool tint_bool tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := andb
  }.
  Global Instance int_bool_and
      : HyperBinaryOp Oand tint_bool tint_bool tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; simpl; tauto.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel'; rewrite <- rel, <- rel'.
      destruct f; destruct f';
        constructor; reflexivity.
  Qed.
  Global Instance int_bool_and_passthrough
      : HyperBinaryPassthrough Oand tint_bool tint_bool tint_bool.

  Global Instance int_bool_eq_impl
      : HyperBinaryImpl Oeq tint_bool tint_bool tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary f f' := negb (xorb f f')
  }.
  Global Instance int_bool_eq
      : HyperBinaryOp Oeq tint_bool tint_bool tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; simpl; tauto.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel'; rewrite <- rel, <- rel'.
      destruct f; destruct f';
        constructor; reflexivity.
  Qed.
  Global Instance int_bool_eq_passthrough
      : HyperBinaryPassthrough Oeq tint_bool tint_bool tint_bool.

  Global Instance int_bool_ne_impl
      : HyperBinaryImpl One tint_bool tint_bool tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := xorb
  }.
  Global Instance int_bool_ne
      : HyperBinaryOp One tint_bool tint_bool tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; simpl; tauto.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel'; rewrite <- rel, <- rel'.
      destruct f; destruct f';
        constructor; reflexivity.
  Qed.
  Global Instance int_bool_ne_passthrough
      : HyperBinaryPassthrough One tint_bool tint_bool tint_bool.

  (* Other operations, e.g. addition, are not defined on tint_bool so
     there are no other instances, as demonstrated by the lacking of
     ``HyperBinaryOp Oadd tint_bool ...'' *)
End HYPER_TYPE_BOOL.

(** * Integers as Z *)
Section HYPER_TYPE_INT.
  Local Open Scope Z_scope.

  Class IntegerBound (bound : Z) : Prop := {
    integer_bound_within_modulus : Int.modulus >= bound;
    integer_bound_positive : 0 < bound
  }.

  Definition Z_bounded (bound : Z){_ : IntegerBound bound} := Z.

  Typeclasses Opaque Z_bounded.

Section BOUNDED.
  (* All the definitions will need these from here on. *)
  Variable bound : Z.
  Context `{bound_cond : IntegerBound bound}.

  Definition tint_Z_bounded
    := Tpair (Z_bounded bound) tint.

  Lemma unsigned_repr_eq (f : Z_bounded bound)(cond : -1 < f /\ bound > f)
      : Int.unsigned (Int.repr f) = f.
  Proof.
    rewrite Int.unsigned_repr_eq.
    apply Zmod_small.
    destruct cond as [ m1_lt_f bound_gt_f ].
    split.
    - assert (0 = Z.succ (-1)).
        reflexivity.
      rewrite H; apply Zlt_le_succ; assumption.
    - apply Zgt_lt.
      eapply Zle_gt_trans;
       [ apply Zge_le; apply integer_bound_within_modulus | exact bound_gt_f ].
  Qed.

  Instance int_Z_iso_impl : HyperTypeIsoImpl tint_Z_bounded := {
    ht_iso_ty_cond v := match v with
      | Vint i => bound > Int.unsigned i
      | _ => False
      end;
    ht_iso_ft_cond f := -1 < f /\ bound > f;

    ht_iso_default := 0;
    ht_iso_AR f := ARZ f;

    ht_implement f := (Vint (Int.repr f));
    ht_spec v := match v with
      | Vint i => Int.unsigned i
      | _ => 0
      end
  }.
  Instance int_Z_iso : HyperTypeIso tint_Z_bounded.
  Proof. esplit.
    - (* ht_implement_returns *)
      intros f fc; simpl in fc |- *.
      rewrite unsigned_repr_eq;
      apply fc.

    - (* ht_spec_returns *)
      intros v vc; simpl in vc |- *.
      destruct v; try contradiction.
      split; try assumption.
      destruct i.
      unfold Int.unsigned, Int.intval.
      apply intrange.

    - (* ht_iso_default_ft_cond *)
      split; [ reflexivity |].
      apply Z.lt_gt, integer_bound_positive.

    - (* ht_iso_has_type *)
      intros [] vc; try contradiction vc.
      simpl; trivial.

    - (* ht_proof_left *)
      intros f fc; simpl in fc |- *; unfold Z_bounded.
      apply unsigned_repr_eq, fc.

    - (* ht_proof_right *)
      intros v vc; simpl in vc |- *.
      destruct v; try contradiction.
      rewrite (Int.repr_unsigned i).
      reflexivity.
  Qed.
  Instance int_Z_impl : HyperTypeImpl tint_Z_bounded := _.
  Instance int_Z : HyperType tint_Z_bounded := _.
  Global Instance int_Z_by_value : HyperByValueType tint_Z_bounded _ := {
    ht_by_value_access_mode := eq_refl
  }.
  Proof.
    - discriminate.
    - simpl. tauto.
    - inversion 2; subst; clear H0.
      injection H1 as <-; reflexivity.
    - inversion 2; subst; clear H0.
      injection H1 as <-; reflexivity.
  Qed.
  Global Instance int_Z_arg_ret : HyperArgRet tint_Z_bounded.
  Proof. esplit.
    - (* ht_basic *)
      intros f valid.
      simpl; constructor.
    - (* ht_sem_cast_ident *)
      intros v (f & fvc & fc & rel); simpl in rel |- *.
      rewrite <- rel; reflexivity.
    - (* ht_injective *)
      simpl.
      intros ? ? fc fc' _ _ cv_eq.
      remember (Int.repr f) as i; remember (Int.repr f') as i'.
      injection cv_eq; subst; intros f_eq.
      apply (f_equal Int.unsigned) in f_eq.
      (*
      rewrite 2 Int.unsigned_repr_eq, 2 Z_bounded_mod_eq  in f_eq; assumption.
      *)
      rewrite 2 unsigned_repr_eq in f_eq; assumption.
    - (* ht_has_type *)
      simpl; inversion 3.
      injection H2 as <-; exact I.
  Qed.

  (* Notbool is not defined on tint_Z_bounded so the instance is not
     defined.  Even if it is defined as shown in the comment, the
     never satisfied pre-condition renders it useless in practice. *)
  (*
  Instance int_Z_notbool bound bound_cond
      : HyperUnaryOp Onotbool (tint_Z_bounded bound bound_cond) := {
    Hunary_cond ft := False
  }.
    intros; contradict oc.
    intros; contradict oc.

    Grab Existential Variables.
    intros; contradict oc.
    intros; contradict H0.
  Defined.
  *)

  (* auto modulo version
  Global Instance int_Z32_add_impl
      : HyperBinaryImpl Oadd tint_Z32 tint_Z32 tint_Z32 := {
    Hbinary_cond f f' := True;
    Hbinary f f' fc fc' oc := (f + f') mod Int.modulus
  }.

  Lemma Int_modulus_gt_zero : Int.modulus > 0.
  Proof.
    unfold Z.gt, Z.compare, Int.modulus, two_power_nat;
    reflexivity.
  Qed.

  Global Instance int_Z32_add
      : HyperBinaryOp Oadd tint_Z32 tint_Z32 tint_Z32 := {
    Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
  }.
  Proof.
    (* Hbinary_fcorrect *)
    - intros; simpl.
      unfold sem_binary_operation, sem_add, classify_add, typeconv,
             unpair_ty, tint_Z_bounded, unpair_ty.
      case_eq (ht_implement f fc); intros;
        try (generalize (ht_implement_returns f fc); intro H0;
             rewrite H in H0; unfold ht_ty_cond, int_Z_impl in H0;
             contradiction).
      case_eq (ht_implement f' fc'); intros;
        try (generalize (ht_implement_returns f' fc'); intro H1;
             rewrite H0 in H1; unfold ht_ty_cond, int_Z_impl in H1;
             contradiction).
      unfold ht_implement, int_Z_impl in H, H0 |- *.
      inversion H; inversion H0.
      rewrite Int.add_unsigned, Int.unsigned_repr_eq.
      rewrite Int.unsigned_repr_eq.
      rewrite Zplus_mod.
      assert (forall z, 0 <= z -> Int.repr (z mod Int.modulus) = Int.repr z).
      + intros.
        apply Int.eqm_samerepr.
        unfold Int.eqm, Int.eqmod.
        exists (- (z / Int.modulus)).
        rewrite Z.mul_opp_l;
        rewrite (Z.div_mod z Int.modulus) at 3;
        [ | intro c; discriminate c ];
        rewrite Z.add_assoc;
        rewrite (Z.mul_comm Int.modulus (z / Int.modulus));
        rewrite Z.add_opp_diag_l;
        symmetry; apply Z.add_0_l.
      + rewrite H1; [ reflexivity | ].
        apply Zle_trans with (m := 0 + f' mod Int.modulus);
        [ rewrite <- (Z.add_0_l 0) at 1; apply Zplus_le_compat_l |
          apply Zplus_le_compat_r ];
        apply Z_mod_lt, Int_modulus_gt_zero.

    (* Hbinary_ccorrect *)
    - intros; simpl in vc, vc' |- *.
      destruct v; destruct v'; try contradiction.
      exists (Vint (Int.add i i0)).
      split; [ unfold sem_binary_operation, sem_add, classify_add, typeconv,
                      unpair_ty, tint_Z32, tint_Z_bounded;
               reflexivity | ].
      assert (ht_ty_cond (tp := tint_Z32) (Vint (Int.add i i0))).
        unfold ht_ty_cond, int_Z_impl.
        unfold Int.unsigned, Int.intval.
        destruct (Int.add i i0).
        destruct intrange; apply Zlt_gt; assumption.
      exists H.
      unfold ht_spec, tint_Z32, tint_Z_bounded, int_Z_impl.
      rewrite Int.add_unsigned.
      rewrite (Int.unsigned_repr_eq (Int.unsigned i + Int.unsigned i0)).
      reflexivity.

    Grab Existential Variables.
    (* Hbinary_returns *)
    + intros; simpl.
      destruct (Z_mod_lt (f + f') _ Int_modulus_gt_zero).
      split.
      * apply Zgt_lt, Zle_succ_gt.
        unfold Z.succ, Z.add at 1, Z.pos_sub at 1.
        assumption.
      * apply Zlt_gt; assumption.
  Qed.
  *)

  Instance int_Z_bounded_add_impl
      : HyperBinaryImpl Oadd tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_cond f f' := f + f' < bound;
    Hbinary_ocond := oprop2 (fun f f' => f + f' < bound);
    Hbinary := Z.add
  }.
  Instance int_Z_bounded_add
      : HyperBinaryOp Oadd tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      split.
      + (* -1 < Hbinary f f' *)
        apply Z.le_succ_l; change (Z.succ (-1)) with (Z.succ (-1) + Z.succ (-1)).
        apply Z.add_le_mono; apply Z.le_succ_l; [ apply fc | apply fc' ].
      + (* bound > Hbinary f f' *)
        apply Z.lt_gt, oc.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor. simpl.
      rewrite add_repr; reflexivity.
  Qed.
  Instance int_Z_bounded_add_passthrough
      : HyperBinaryPassthrough Oadd tint_Z_bounded tint_Z_bounded tint_Z_bounded.

  Instance int_Z_bounded_sub_impl
      : HyperBinaryImpl Osub tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_cond f f' := f >= f';
    Hbinary_ocond := oprop2 (fun f f' => f >= f');
    Hbinary := Z.sub
  }.
  Instance int_Z_bounded_sub
      : HyperBinaryOp Osub tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      split.
      + (* -1 < Hbinary f f' *)
        simpl.
        rewrite <- Z.le_succ_l, <- Z.le_add_le_sub_r.
        apply Z.ge_le, oc.
      + (* bound > Hbinary f f' *)
        simpl in fc, fc' |- *.
        omega.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor.
      simpl.
      rewrite sub_repr; reflexivity.
  Qed.
  Instance int_Z_bounded_sub_passthrough
      : HyperBinaryPassthrough Osub tint_Z_bounded tint_Z_bounded tint_Z_bounded.

  Instance int_Z_bounded_mul_impl
      : HyperBinaryImpl Omul tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_cond f f' := f * f' < bound;
    Hbinary_ocond := oprop2 (fun f f' => f * f' < bound);
    Hbinary := Z.mul
  }.
  Instance int_Z_bounded_mul
      : HyperBinaryOp Omul tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      split.
      + (* -1 < Hbinary f f' *)
        apply Z.le_succ_l, Z.mul_nonneg_nonneg;
          change 0 with (Z.succ (-1)); apply Z.le_succ_l;
          [ apply fc | apply fc' ].
      + (* bound > Hbinary f f' *)
        apply Z.lt_gt, oc.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor. simpl.
      rewrite mul_repr; reflexivity.
  Qed.
  Instance int_Z_bounded_mul_passthrough
      : HyperBinaryPassthrough Omul tint_Z_bounded tint_Z_bounded tint_Z_bounded.

  Instance int_Z_bounded_mod_impl
      : HyperBinaryImpl Omod tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_cond f f' := f' <> 0;
    Hbinary_ocond := oprop2 (fun f f' => f' <> 0);
    Hbinary := Z.modulo
  }.
  Instance int_Z_bounded_mod
      : HyperBinaryOp Omod tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      simpl in oc, fc' |- *.
      split.
      + (* -1 < Hbinary f f' *)
        rewrite <- Z.le_succ_l.
        apply Z_mod_lt.
        apply proj1 in fc'.
        rewrite <- Z.le_succ_l, Z.lt_eq_cases in fc'.
        destruct fc' as [ lt | eq ];
          [ apply Z.lt_gt, lt | contradiction (oc (eq_sym eq)) ].
      + (* bound > Hbinary f f' *)
        eapply Zgt_trans; [ apply fc' |].
        apply Z.lt_gt, Z_mod_lt.
        apply proj1 in fc'.
        rewrite <- Z.le_succ_l, Z.lt_eq_cases in fc'.
        destruct fc' as [ lt | eq ];
          [ apply Z.lt_gt, lt | contradiction (oc (eq_sym eq)) ].

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel', fc, fc', oc |- *.

      assert (f_eq := unsigned_repr_eq _ fc).
      assert (f_eq' := unsigned_repr_eq _ fc').

      rewrite <- rel, <- rel'.
      simpl; unfold sem_mod, sem_binarith; simpl.
      assert (f_zero_spec := Int.eq_spec (Int.repr f') Int.zero).
      destruct (Int.eq (Int.repr f') Int.zero).
      + apply (f_equal Int.unsigned) in f_zero_spec.
        rewrite Int.unsigned_zero, f_eq' in f_zero_spec.
        contradiction (oc f_zero_spec).
      + simpl. Admitted.
     (* unfold cval_binary_operation. simpl.
        unfold sem_mod, sem_binarith. simpl.
        unfold Int.modu.
        constructor.
        unfold Int.modu; rewrite f_eq, f_eq'.
        reflexivity.
  Qed. *)
  Instance int_Z_bounded_mod_passthrough
      : HyperBinaryPassthrough Omod tint_Z_bounded tint_Z_bounded tint_Z_bounded.

  Instance int_Z_bounded_div_impl
      : HyperBinaryImpl Odiv tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_cond f f' := f' <> 0;
    Hbinary_ocond := oprop2 (fun f f' => f' <> 0);
    Hbinary := Z.div
  }.
  Instance int_Z_bounded_div
      : HyperBinaryOp Odiv tint_Z_bounded tint_Z_bounded tint_Z_bounded := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      simpl in oc, fc, fc' |- *.

      assert (f_pos' : 0 < f').
      { apply proj1 in fc'.
        rewrite <- Z.le_succ_l, Z.lt_eq_cases in fc'.
        destruct fc' as [ lt | eq ];
          [ exact lt | contradiction (oc (eq_sym eq)) ].
      }

      split.
      + (* -1 < Hbinary f f' *)
        rewrite <- Z.le_succ_l.
        apply Z_div_pos; [ apply Z.lt_gt, f_pos' |].
        rewrite <- Z.le_succ_l in fc.
        apply fc.
      + (* bound > Hbinary f f' *)
        apply Z.lt_gt, Zdiv_lt_upper_bound; [ exact f_pos' |].
        eapply Z.lt_le_trans; [ apply Z.gt_lt, fc |].
        replace bound with (bound * 1) at 1 by apply Z.mul_1_r.
        apply Zmult_le_compat_l;
          [| apply Z.lt_le_incl, integer_bound_positive ].
        rewrite <- Z.le_succ_l in f_pos'.
        exact f_pos'.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel', fc, fc', oc |- *.

      assert (f_eq := unsigned_repr_eq _ fc).
      assert (f_eq' := unsigned_repr_eq _ fc').

      rewrite <- rel, <- rel'.
      simpl; unfold sem_div, sem_binarith; simpl.
      assert (f_zero_spec := Int.eq_spec (Int.repr f') Int.zero).
      destruct (Int.eq (Int.repr f') Int.zero).
      + apply (f_equal Int.unsigned) in f_zero_spec.
        rewrite Int.unsigned_zero, f_eq' in f_zero_spec.
        contradiction (oc f_zero_spec).
      + Admitted.
  (*
        constructor.
        simpl.
        unfold Int.divu; rewrite f_eq, f_eq'.
        reflexivity.
  Qed. *)
  Instance int_Z_bounded_div_passthrough
      : HyperBinaryPassthrough Odiv tint_Z_bounded tint_Z_bounded tint_Z_bounded.

  Instance int_Z_bounded_eq_impl
      : HyperBinaryImpl Oeq tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := Z.eqb
  }.
  Instance int_Z_bounded_eq
      : HyperBinaryOp Oeq tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; exact I.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor. Admitted. (*
      unfold Int.cmpu, Int.eq, Coqlib.zeq.
      rewrite 2 unsigned_repr_eq; try assumption.
      destruct (Z.eq_dec f f') as [ dec_eq | dec_ne ],
               (f =? f') eqn:eqb_eq.
      + reflexivity.
      + exfalso.
        rewrite (proj2 (Z.eqb_eq _ _) dec_eq) in eqb_eq; discriminate.
      + contradict dec_ne.
        apply Z.eqb_eq, eqb_eq.
      + reflexivity.
  Qed. *)
  Instance int_Z_bounded_eq_passthrough
      : HyperBinaryPassthrough Oeq tint_Z_bounded tint_Z_bounded tint_bool.

  Instance int_Z_bounded_ne_impl
      : HyperBinaryImpl One tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary f f' := negb (Z.eqb f f')
  }.
  Instance int_Z_bounded_ne
      : HyperBinaryOp One tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; exact I.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor. Admitted. (*
      unfold Int.cmpu, Int.eq, Coqlib.zeq.
      rewrite 2 unsigned_repr_eq; try assumption.
      destruct (Z.eq_dec f f') as [ dec_eq | dec_ne ],
               (f =? f') eqn:eqb_eq.
      + reflexivity.
      + exfalso.
        rewrite (proj2 (Z.eqb_eq _ _) dec_eq) in eqb_eq; discriminate.
      + contradict dec_ne.
        apply Z.eqb_eq, eqb_eq.
      + reflexivity.
  Qed. *)
  Instance int_Z_bounded_ne_passthrough
      : HyperBinaryPassthrough One tint_Z_bounded tint_Z_bounded tint_bool.

  Instance int_Z_bounded_lt_impl
      : HyperBinaryImpl Olt tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := Z.ltb
  }.
  Instance int_Z_bounded_lt
      : HyperBinaryOp Olt tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; exact I.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor.
      unfold Int.cmpu, Int.ltu, Coqlib.zlt. Admitted.
      (* rewrite 2 unsigned_repr_eq; try assumption.
      destruct (Z_lt_dec f f') as [ dec_lt | dec_ge ],
               (f <? f') eqn:ltb_eq.
      + reflexivity.
      + exfalso.
        rewrite (proj2 (Z.ltb_lt _ _) dec_lt) in ltb_eq; discriminate.
      + contradict dec_ge.
        apply Z.ltb_lt, ltb_eq.
      + reflexivity.
  Qed. *)
  Instance int_Z_bounded_lt_passthrough
      : HyperBinaryPassthrough Olt tint_Z_bounded tint_Z_bounded tint_bool.

  Instance int_Z_bounded_gt_impl
      : HyperBinaryImpl Ogt tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := Z.gtb
  }.
  Instance int_Z_bounded_gt
      : HyperBinaryOp Ogt tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; exact I.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor.
      unfold Int.cmpu, Int.ltu, Coqlib.zlt. Admitted. (*
      rewrite 2 unsigned_repr_eq; try assumption.
      destruct (Z_lt_dec f' f) as [ dec_lt | dec_ge ],
               (f >? f') eqn:ltb_eq.
      + reflexivity.
      + exfalso.
        rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt _ _) dec_lt) in ltb_eq; discriminate.
      + contradict dec_ge.
        rewrite Z.gtb_ltb in ltb_eq.
        apply Z.ltb_lt, ltb_eq.
      + reflexivity.
  Qed. *)
  Instance int_Z_bounded_gt_passthrough
      : HyperBinaryPassthrough Ogt tint_Z_bounded tint_Z_bounded tint_bool.

  Instance int_Z_bounded_le_impl
      : HyperBinaryImpl Ole tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := Z.leb
  }.
  Instance int_Z_bounded_le
      : HyperBinaryOp Ole tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; exact I.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor.
      unfold Int.cmpu, Int.ltu, Coqlib.zlt. Admitted. (*
      rewrite 2 unsigned_repr_eq; try assumption.
      destruct (Z_lt_dec f' f) as [ dec_lt | dec_ge ],
               (f <=? f') eqn:ltb_eq.
      + exfalso.
        rewrite Z.leb_antisym, (proj2 (Z.ltb_lt _ _) dec_lt) in ltb_eq;
          discriminate.
      + reflexivity.
      + reflexivity.
      + contradict dec_ge.
        apply (f_equal negb) in ltb_eq.
        rewrite Z.leb_antisym, negb_involutive in ltb_eq.
        apply Z.ltb_lt, ltb_eq.
  Qed. *)
  Instance int_Z_bounded_le_passthrough
      : HyperBinaryPassthrough Ole tint_Z_bounded tint_Z_bounded tint_bool.

  Instance int_Z_bounded_ge_impl
      : HyperBinaryImpl Oge tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_cond f f' := True;
    Hbinary_ocond := otrue2;
    Hbinary := Z.geb
  }.
  Instance int_Z_bounded_ge
      : HyperBinaryOp Oge tint_Z_bounded tint_Z_bounded tint_bool := {
    Hbinary_mem_irr := fun _ _ _ _ => eq_refl _
  }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.

    - (* Hbinary_returns *)
      intros; exact I.

    - (* Hbinary_correct *)
      intros f f' v v' fc fc' oc rel rel'.
      simpl in rel, rel' |- *.
      rewrite <- rel, <- rel'.
      constructor.
      unfold Int.cmpu, Int.ltu, Coqlib.zlt. Admitted. (*
      rewrite 2 unsigned_repr_eq; try assumption.
      destruct (Z_lt_dec f f') as [ dec_lt | dec_ge ],
               (f >=? f') eqn:geb_eq.
      + exfalso.
        apply Z.geb_le, Z.le_ge in geb_eq.
        exact (geb_eq dec_lt).
      + reflexivity.
      + reflexivity.
      + contradict dec_ge.
        rewrite Z.geb_leb in geb_eq.
        apply Z.leb_gt, geb_eq.
  Qed. *)
  Instance int_Z_bounded_ge_passthrough
      : HyperBinaryPassthrough Oge tint_Z_bounded tint_Z_bounded tint_bool.

End BOUNDED.

  Global Instance modulus_bound : IntegerBound Int.modulus := {
    integer_bound_within_modulus := Z.le_ge _ _ (Zle_refl Int.modulus);
    integer_bound_positive := Z.gt_lt _ _ (Int.modulus_pos)
  }.

  Definition tint_Z32 := tint_Z_bounded Int.modulus.
  Typeclasses Transparent tint_Z32 tint_Z_bounded.

  Definition int_Z32_impl := int_Z_impl Int.modulus.
  Definition int_Z32 := int_Z Int.modulus.
  Definition int_Z32_by_value := int_Z_by_value Int.modulus.
  Definition int_Z32_pair := @mk_hyper_type_pair tint_Z32 int_Z32_impl (*int_Z32*).
  (*Definition int_Z32_self_cast := int_Z_self_cast Int.modulus.*)
  Definition int_Z32_arg_ret := int_Z_arg_ret.
  Existing Instance int_Z32_impl.

  Lemma int_Z32_ty_cond z
      : ht_ty_cond tint_Z32 (Values.Vint (Int.repr z)).
  Proof.
    unfold ht_ty_cond, int_Z32_impl, int_Z_impl.
    exists (Int.Z_mod_modulus z).
    split.
    - (* ht_ft_cond (Int.Z_mod_modulus z) *)
      split; [| apply Z.lt_gt ]; apply Int.Z_mod_modulus_range'.
    - (* ht_rel (Int.Z_mod_modulus z) (Vint (Int.repr z)) *)
      simpl. f_equal. Admitted. (*
      simpl; do 2 f_equal.
      rewrite Int.Z_mod_modulus_eq.
      apply Int.eqm_samerepr, Int.eqmod_sym, Int.eqmod_mod, Int.modulus_pos.
  Qed. *)

  Definition int_Z32_add_impl := int_Z_bounded_add_impl Int.modulus.
  Definition int_Z32_sub_impl := int_Z_bounded_sub_impl Int.modulus.
  Definition int_Z32_mul_impl := int_Z_bounded_mul_impl Int.modulus.
  Definition int_Z32_mod_impl := int_Z_bounded_mod_impl Int.modulus.
  Definition int_Z32_div_impl := int_Z_bounded_div_impl Int.modulus.

  Definition int_Z32_add := int_Z_bounded_add Int.modulus.
  Definition int_Z32_sub := int_Z_bounded_sub Int.modulus.
  Definition int_Z32_mul := int_Z_bounded_mul Int.modulus.
  Definition int_Z32_mod := int_Z_bounded_mod Int.modulus.
  Definition int_Z32_div := int_Z_bounded_div Int.modulus.

  Definition int_Z32_add_passthrough := int_Z_bounded_add_passthrough Int.modulus.
  Definition int_Z32_sub_passthrough := int_Z_bounded_sub_passthrough Int.modulus.
  Definition int_Z32_mul_passthrough := int_Z_bounded_mul_passthrough Int.modulus.
  Definition int_Z32_mod_passthrough := int_Z_bounded_mod_passthrough Int.modulus.
  Definition int_Z32_div_passthrough := int_Z_bounded_div_passthrough Int.modulus.  
  
  Definition int_Z32_eq_impl := int_Z_bounded_eq_impl Int.modulus.
  Definition int_Z32_ne_impl := int_Z_bounded_ne_impl Int.modulus.
  Definition int_Z32_lt_impl := int_Z_bounded_lt_impl Int.modulus.
  Definition int_Z32_gt_impl := int_Z_bounded_gt_impl Int.modulus.
  Definition int_Z32_le_impl := int_Z_bounded_le_impl Int.modulus.
  Definition int_Z32_ge_impl := int_Z_bounded_ge_impl Int.modulus.

  Definition int_Z32_eq := int_Z_bounded_eq Int.modulus.
  Definition int_Z32_ne := int_Z_bounded_ne Int.modulus.
  Definition int_Z32_lt := int_Z_bounded_lt Int.modulus.
  Definition int_Z32_gt := int_Z_bounded_gt Int.modulus.
  Definition int_Z32_le := int_Z_bounded_le Int.modulus.
  Definition int_Z32_ge := int_Z_bounded_ge Int.modulus.

  Definition int_Z32_eq_passthrough := int_Z_bounded_eq_passthrough Int.modulus.
  Definition int_Z32_ne_passthrough := int_Z_bounded_ne_passthrough Int.modulus.
  Definition int_Z32_lt_passthrough := int_Z_bounded_lt_passthrough Int.modulus.
  Definition int_Z32_gt_passthrough := int_Z_bounded_gt_passthrough Int.modulus.
  Definition int_Z32_le_passthrough := int_Z_bounded_le_passthrough Int.modulus.
  Definition int_Z32_ge_passthrough := int_Z_bounded_ge_passthrough Int.modulus.

  Definition tint_Z32_naturally_aligned : naturally_aligned (unpair_ty tint_Z32) := conj eq_refl I.
End HYPER_TYPE_INT.

Notation Z32 := (Z_bounded Int.modulus).

Existing Instances int_Z32_impl int_Z32 int_Z32_by_value int_Z32_arg_ret.
Existing Instances int_Z32_add_impl int_Z32_sub_impl int_Z32_mul_impl
                   int_Z32_mod_impl int_Z32_div_impl.
Existing Instances int_Z32_add int_Z32_sub int_Z32_mul int_Z32_mod int_Z32_div.
Existing Instances int_Z32_add_passthrough int_Z32_sub_passthrough
                   int_Z32_mul_passthrough int_Z32_mod_passthrough
                   int_Z32_div_passthrough.
Existing Instances int_Z32_eq_impl int_Z32_ne_impl int_Z32_lt_impl
                   int_Z32_gt_impl int_Z32_le_impl int_Z32_ge_impl.
Existing Instances int_Z32_eq int_Z32_ne int_Z32_lt int_Z32_gt
                   int_Z32_le int_Z32_ge.
Existing Instances int_Z32_eq_passthrough int_Z32_ne_passthrough
                   int_Z32_lt_passthrough int_Z32_gt_passthrough
                   int_Z32_le_passthrough int_Z32_ge_passthrough.
(*
Require Import Omega.

Section HYPER_TYPE_UNSIGNED.
  (* Local Open Scope Z_scope. *)

  Definition tint_U := Tpair int tint.

  Instance int_U_iso_impl : HyperTypeIsoImpl tint_U :=
    {
      ht_iso_ft_cond f := True;
      ht_iso_ty_cond v := match v with
                            | Vint i => Int.modulus > Int.unsigned i
                            | _ => False
                          end;
      ht_iso_default := Int.zero;
      ht_implement f := (Vint f);
      ht_spec v := match v with
                     | Vint i => i
                     | _ => Int.zero
                   end
    }.

  Instance int_U_iso : HyperTypeIso tint_U.
  Proof.
    esplit.
    - (* ht_implement_returns *)
      intros f fc. simpl in *.
      destruct f.
      simpl. omega.
    - (* ht_spec_returns *)
      intros v vc; simpl in *.
      destruct v; try contradiction.
      split; auto.
    - (* ht_iso_default_ft_cond *)
      unfold ht_iso_ft_cond. simpl; trivial.
    - (* ht_iso_has_type *)
      intros [] vc; try contradiction vc.
      simpl; trivial.
    - (* ht_proof_left *)
      intros f fc; reflexivity.
    - (* ht_proof_right *)
      intros [] vc; simpl in *; try contradiction.
      reflexivity.
  Qed.

  Instance int_U_impl : HyperTypeImpl tint_U := _.
  Instance int_U : HyperType tint_U := _.
  Global Instance int_U_by_value : HyperByValueType tint_U _ :=
    { ht_by_value_access_mode := eq_refl }.
  Proof.
    - discriminate.
    - reflexivity.
    - inversion 2; subst; clear H0.
      injection H3 as <-; reflexivity.
    - inversion 2; subst; clear H0.
      injection H3 as <-; reflexivity.
  Qed.

  Global Instance int_U_arg_ret : HyperArgRet tint_U.
  Proof.
    esplit.
    - (* ht_basic *)
      intros f valid.
      simpl; constructor.
    - (* ht_sem_cast_ident *)
      intros v (f & fvc & fc & rel); simpl in rel |- *.
      rewrite <- rel; reflexivity.
    - (* ht_injective *)
      simpl.
      intros ? ? fc fc' _ _ cv_eq.
      injection cv_eq; trivial.
    - (* ht_has_type *)
      simpl; inversion 3.
      injection H4 as <-; exact I.
  Qed.

  (**[int_U_add]******************************************)
  Instance int_U_add_impl : HyperBinaryImpl Oadd tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary x y := Int.add x y
    }.

  Instance int_U_add : HyperBinaryOp Oadd tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      split; omega.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      simpl in *. subst v v'.
      constructor.
      reflexivity.
  Qed.
  Instance int_U_add_passthrough : HyperBinaryPassthrough Oadd tint_U tint_U tint_U.

  (**[int_U_sub]******************************************)
  Instance int_U_sub_impl : HyperBinaryImpl Osub tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary x y := Int.sub x y
    }.

  Instance int_U_sub : HyperBinaryOp Osub tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      split; omega.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      simpl in *.
      subst v v'.
      constructor. reflexivity.
  Qed.
  Instance int_U_sub_passthrough : HyperBinaryPassthrough Osub tint_U tint_U tint_U.

  (**[int_U_mul]******************************************)
  Instance int_U_mul_impl : HyperBinaryImpl Omul tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary x y := Int.mul x y
    }.

  Instance int_U_mul : HyperBinaryOp Omul tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      split; simpl; omega.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      simpl in *.
      subst v v'.
      constructor.
      reflexivity.
  Qed.
  Instance int_U_mul_passthrough : HyperBinaryPassthrough Omul tint_U tint_U tint_U.

  (**[int_U_mod]******************************************)
  Instance int_U_mod_impl : HyperBinaryImpl Omod tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := f' <> Int.zero;
      Hbinary_ocond := oprop2 (fun f f' => f' <> Int.zero);
      Hbinary := Int.modu
    }.
    
  Instance int_U_mod : HyperBinaryOp Omod tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      simpl in *.
      split; omega.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'. simpl in *.
      unfold sem_mod, sem_binarith; simpl.
      rewrite (Int.eq_false _ _ oc).
      constructor. reflexivity.
  Qed.
  Instance int_U_mod_passthrough : HyperBinaryPassthrough Omod tint_U tint_U tint_U.

  (**[int_U_div]******************************************)
  Instance int_U_div_impl : HyperBinaryImpl Odiv tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := f' <> Int.zero;
      Hbinary_ocond := oprop2 (fun f f' => f' <> Int.zero);
      Hbinary := Int.divu
    }.
  Instance int_U_div : HyperBinaryOp Odiv tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      intros f f' fc fc' oc.
      simpl in *.
      split; omega.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'; simpl in *.
      unfold sem_div, sem_binarith; simpl.
      rewrite (Int.eq_false _ _ oc).
      constructor. reflexivity.
  Qed.
  Instance int_U_div_passthrough : HyperBinaryPassthrough Odiv tint_U tint_U tint_U.

  (**[int_U_eq]******************************************)
  Instance int_U_eq_impl : HyperBinaryImpl Oeq tint_U tint_U tint_bool :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.cmpu Ceq
    }.

  Instance int_U_eq : HyperBinaryOp Oeq tint_U tint_U tint_bool :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'; simpl in *.
      constructor; simpl.
      destruct (Int.eq f f'); reflexivity.
  Qed.
  Instance int_U_eq_passthrough : HyperBinaryPassthrough Oeq tint_U tint_U tint_bool .

  (**[int_U_ne]******************************************)
  Instance int_U_ne_impl : HyperBinaryImpl One tint_U tint_U tint_bool :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.cmpu Cne
    }.

  Instance int_U_ne : HyperBinaryOp One tint_U tint_U tint_bool :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'.
      constructor; simpl in *.
      destruct (Int.eq f f'); reflexivity.
  Qed.
  Instance int_U_ne_passthrough : HyperBinaryPassthrough One tint_U tint_U tint_bool.

  (**[int_U_lt]******************************************)
  Instance int_U_lt_impl : HyperBinaryImpl Olt tint_U tint_U tint_bool :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.cmpu Clt
    }.

  Instance int_U_lt : HyperBinaryOp Olt tint_U tint_U tint_bool :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'.
      constructor; simpl in *.
      destruct (Int.ltu f f'); reflexivity.
  Qed.
  Instance int_U_lt_passthrough : HyperBinaryPassthrough Olt tint_U tint_U tint_bool.

  (**[int_U_gt]******************************************)
  Instance int_U_gt_impl : HyperBinaryImpl Ogt tint_U tint_U tint_bool :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.cmpu Cgt
    }.

  Instance int_U_gt : HyperBinaryOp Ogt tint_U tint_U tint_bool :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'.
      constructor; simpl in *.
      destruct (Int.ltu f' f); reflexivity.
  Qed.
  Instance int_U_gt_passthrough : HyperBinaryPassthrough Ogt tint_U tint_U tint_bool.

  (**[int_U_le]******************************************)
  Instance int_U_le_impl : HyperBinaryImpl Ole tint_U tint_U tint_bool :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.cmpu Cle
    }.

  Instance int_U_le : HyperBinaryOp Ole tint_U tint_U tint_bool :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'.
      constructor; simpl in *.
      destruct (Int.ltu f' f); reflexivity.
  Qed.
  Instance int_U_le_passthrough : HyperBinaryPassthrough Ole tint_U tint_U tint_bool.

  (**[int_U_ge]******************************************)
  Instance int_U_ge_impl : HyperBinaryImpl Oge tint_U tint_U tint_bool :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.cmpu Cge
    }.

  Instance int_U_ge : HyperBinaryOp Oge tint_U tint_U tint_bool :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'.
      constructor; simpl in *.
      destruct (Int.ltu f f'); reflexivity.
  Qed.
  Instance int_U_ge_passthrough : HyperBinaryPassthrough Oge tint_U tint_U tint_bool.

  (**[int_U_notint]******************************************)
  Instance int_U_notint_impl : HyperUnaryImpl Onotint tint_U tint_U :=
    {
      Hunary_cond ft := True;
      Hunary_ocond := otrue1;
      Hunary := Int.not
    }.

  Instance int_U_notint : HyperUnaryOp Onotint tint_U tint_U.
  Proof.
    esplit.
    - (* Hunary_ocond_same *)
      reflexivity.
    - (* Hunary_returns *)
      trivial.
    - (* Hunary_correct *)
      simpl.
      intros f v fc oc rel.
      subst v. constructor. reflexivity.
  Qed.
  Instance int_U_notint_passthrough : HyperUnaryPassthrough Onotint tint_U tint_U.

  (**[int_U_and]******************************************)
  Instance int_U_and_impl : HyperBinaryImpl Oand tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.and
    }.

  Instance int_U_and : HyperBinaryOp Oand tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      simpl in *. subst v v'.
      constructor. reflexivity.
  Qed.
  Instance int_U_and_passthrough : HyperBinaryPassthrough Oand tint_U tint_U tint_U.
  
  (**[int_U_or]******************************************)
  Instance int_U_or_impl : HyperBinaryImpl Oor tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.or
    }.
  Instance int_U_or : HyperBinaryOp Oor tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      simpl in *. subst v v'.
      constructor. reflexivity.
  Qed.
  Instance int_U_or_passthrough : HyperBinaryPassthrough Oor tint_U tint_U tint_U.

  (**[int_U_shl]******************************************)
  Instance int_U_shl_impl : HyperBinaryImpl Oshl tint_U tint_Z32 tint_U :=
    {
      Hbinary_cond f f' := f' < Int.zwordsize;
      Hbinary_ocond := oprop2 (fun f f' => f' < Int.zwordsize);
      Hbinary x y := Int.shl x (Int.repr y)
    }.
  Lemma lt_zwordsize_lt_iwordsize :
    forall f,
      -1 < f < Int.zwordsize ->
      Int.ltu (Int.repr f) Int.iwordsize = true.
  Proof.
    intros.
    unfold Int.ltu, zlt.
    unfold Int.iwordsize.
    assert (Int.wordsize = 32%nat) by reflexivity.
    assert (Int.zwordsize = 32) by reflexivity.
    rewrite H1 in *.
    repeat rewrite (unsigned_repr_eq _ _).
    - destruct (Z_lt_dec f 32); auto.
      omega.
    - split.
      + omega.
      + unfold Int.modulus.
        rewrite H0.
        rewrite two_power_nat_equiv.
        reflexivity.
    - unfold Int.modulus.
      rewrite two_power_nat_equiv.
      rewrite H0.
      split.
      + omega.
      + cut (2 ^ Z.of_nat 32 > 32).
        * omega.
        * reflexivity.
  Qed.
  
  Instance int_U_shl : HyperBinaryOp Oshl tint_U tint_Z32 tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'; simpl in *.
      unfold sem_shl, sem_shift. simpl.
      rewrite lt_zwordsize_lt_iwordsize by omega.
      constructor; reflexivity.
  Qed.
  Instance int_U_shl_passthrough : HyperBinaryPassthrough Oshl tint_U tint_Z32 tint_U.

  (**[int_U_shr]******************************************)
  Instance int_U_shr_impl : HyperBinaryImpl Oshr tint_U tint_Z32 tint_U :=
    {
      Hbinary_cond f f' := f' < Int.zwordsize;
      Hbinary_ocond := oprop2 (fun f f' => f' < Int.zwordsize);
      Hbinary x y := Int.shru x (Int.repr y)
    }.
  Instance int_U_shr : HyperBinaryOp Oshr tint_U tint_Z32 tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      subst v v'; simpl in *.
      unfold sem_shr, sem_shift. simpl.
      rewrite lt_zwordsize_lt_iwordsize by omega.
      constructor; reflexivity.
  Qed.
  Instance int_U_shr_passthrough : HyperBinaryPassthrough Oshr tint_U tint_Z32 tint_U.

  (**[int_U_xor]******************************************)
  Instance int_U_xor_impl : HyperBinaryImpl Oxor tint_U tint_U tint_U :=
    {
      Hbinary_cond f f' := True;
      Hbinary_ocond := otrue2;
      Hbinary := Int.xor
    }.
  Instance int_U_xor : HyperBinaryOp Oxor tint_U tint_U tint_U :=
    {
      Hbinary_mem_irr := fun _ _ _ _ _ _ _ _ => eq_refl _
    }.
  Proof.
    - (* Hbinary_ocond_same *)
      reflexivity.
    - (* Hbinary_returns *)
      trivial.
    - (* Hbinary_correct *)
      intros mem mm f f' v v' fc fc' oc rel rel'.
      simpl in *. subst v v'.
      constructor; simpl.
      reflexivity.
  Qed.
  Instance int_U_xor_passthrough : HyperBinaryPassthrough Oxor tint_U tint_U tint_U.
  
  Typeclasses Transparent tint_U.
  Definition int_U_pair := @mk_hyper_type_pair tint_U int_U_impl.
  Existing Instance int_U_impl.

  Lemma int_U_ty_cond z :
    ht_ty_cond tint_U (CVval (Values.Vint z)).
  Proof.
    unfold ht_ty_cond, int_U_impl.
    exists z.
    split.
    - split.
    - simpl; do 2 f_equal.
  Qed.

  Definition tint_U_naturally_aligned : naturally_aligned (unpair_ty tint_U) := (eq_refl _).

End HYPER_TYPE_UNSIGNED.

Existing Instances int_U_impl int_U int_U_by_value int_U_arg_ret.
Existing Instances
         int_U_add_impl int_U_sub_impl int_U_mul_impl
         int_U_mod_impl int_U_div_impl.
Existing Instances
         int_U_add int_U_sub
         int_U_mul int_U_mod int_U_div.
Existing Instances
         int_U_add_passthrough int_U_sub_passthrough
         int_U_mul_passthrough int_U_mod_passthrough int_U_div_passthrough.
Existing Instances
         int_U_eq_impl int_U_ne_impl
         int_U_lt_impl int_U_gt_impl int_U_le_impl int_U_ge_impl.
Existing Instances
         int_U_eq int_U_ne
         int_U_lt int_U_gt int_U_le int_U_ge.
Existing Instances
         int_U_eq_passthrough int_U_ne_passthrough
         int_U_lt_passthrough int_U_gt_passthrough
         int_U_le_passthrough int_U_ge_passthrough.
Existing Instances
         int_U_notint_impl int_U_and_impl int_U_or_impl
         int_U_shl_impl int_U_shr_impl int_U_xor_impl.
Existing Instances
         int_U_notint int_U_and int_U_or
         int_U_shl int_U_shr int_U_xor.
Existing Instances
         int_U_notint_passthrough int_U_and_passthrough int_U_or_passthrough
         int_U_shl_passthrough int_U_shr_passthrough int_U_xor_passthrough.
*)
