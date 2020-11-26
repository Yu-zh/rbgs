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

(** Defining the "extended C value" [cval], its operations, and its relation
    with the vanilla C value type [val]. *)
(** This file defines a cval layer above CompCert C memory model. It also
  * defines some operators for cval, and proves simulation relation between
  * these two layers for each operator. *)

(* Standard library modules *)
Require Import BinInt.  (* Z_scope, (_ | _) *)

(* CompCert modules *)
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.common.Memtype. (* MemoryModelOps *)
Require Import compcert.common.Memdata. (* size_chunk *)
Require Import compcert.common.Memory. (* Mem.empty *)

(* Liblayers modules *)
(* Require        liblayers.compcertx.CompcertStructures. *)

(* DeepSpec modules *)
Require Import deepsea.CvalDef.
(* Require Import DeepSpec.xcore.MemoryModel. *)

Notation tint := (Tint I32 Unsigned noattr).
Notation tchar := (Tint I8 Unsigned noattr).
Notation tchar_pointer := (Tpointer tchar noattr).

(* cast value v of type tfrom into another value of type tto *)
Definition cval_cast (v : val) tfrom tto : option val :=
  sem_cast v tfrom tto Mem.empty.

Definition cval_unary_operation op (v: val) t : option val :=
  sem_unary_operation op v t Mem.empty.

(* test is pointer involved or not *)
Definition is_pointer_comparison op t1 t2 := match op with
  | Oeq | One | Olt | Ogt | Ole | Oge =>
    match classify_cmp t1 t2 with
    | cmp_default => false
    | _ => true
    end
  | _ => false
  end.

Definition cval_binary_operation op v1 t1 v2 t2 : option val :=
  if is_pointer_comparison op t1 t2 then None
  else sem_binary_operation (PTree.empty _) op v1 t1 v2 t2 Mem.empty.

Section WITH_MEM.
  (* Context`{UnderlaySpec : UnderlaySpecClass}. *)
  (* Variable (mem: Type). *)
  (* Context {memory_model_ops: Mem.MemoryModelOps mem}. *)

  Lemma cval_basic_cval_match v cv :
    cval_basic cv ->
    (cval_match v cv <-> cv = v).
  Proof.
    intros basic.
    split.
    - inversion basic; inversion 1;
        injection H1 as <-; reflexivity.
    - intros ->.
      inversion basic; constructor; reflexivity.
  Qed.

  Lemma cval_basic_match_cval_match v cv :
    cval_basic_match v cv -> cval_match v cv.
  Proof.
    inversion 1; constructor; reflexivity.
  Qed.

  Ltac TrivialExists :=
    match goal with
    | |- exists v', Some ?v = Some v' /\ _ => exists v; split; auto
    | |- exists v', (forall _, Some ?v = Some v') /\ _ => exists v; split; auto
    | _ => idtac
    end.

  Ltac DestructIval v cond :=
    destruct v; try discriminate;
      match goal with
      | [ H : context[ match glob_threshold_find_symbol ?i with | _ => _ end ] |- _ ]
        => destruct (glob_threshold_find_symbol i) eqn:?i_sym_eq
      | _ => idtac
      end;
      try discriminate; try injection cond as <-.

  (* v1 ---sem_cast--> v
     |                 |
 find_symbol       find_symbol
     |                 |
     tv1 --sem_cast--> tv *)
  Lemma sem_cast_find_symbol v1 ty1 ty v tv1 :
      sem_cast v1 ty1 ty Mem.empty = Some v ->
      val_find_symbol v1 tv1 ->
      exists tv, (forall m, sem_cast tv1 ty1 ty m = Some tv) /\ val_find_symbol v tv.
  Proof. Admitted.
  (* unfold sem_cast, val_find_symbol, find_val_symbol.
    intros cast_eq v1_find_symbol.
    destruct (classify_cast ty1 ty); DestructIval v1 v1_find_symbol;
      inv cast_eq; TrivialExists.
    - rewrite i_sym_eq; reflexivity.
    - destruct (cast_float_int si2 f); inv H0; TrivialExists.
    - destruct (cast_float_long si2 f); inv H0; TrivialExists.
    - destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; TrivialExists.
      rewrite i_sym_eq; reflexivity.
    - destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; TrivialExists.
      rewrite i_sym_eq; reflexivity.
    - rewrite i_sym_eq; reflexivity.
  Qed. *)

  (* v1 ---sem_cast---> v2
     |                  |
 cval_match         cval_match
     |                  |
     cv1 --cval_cast--> cv2 *)
  Lemma cval_sem_cast v1 cv1 cv2 t1 t2 :
      cval_match v1 cv1 ->
      cval_cast cv1 t1 t2 = Some cv2 ->
      exists v2, (forall m, sem_cast v1 t1 t2 m = Some v2) /\ cval_match v2 cv2.
  Proof. Admitted. (*
    inversion 1 as [ v1i ? v1_find_symbol |]; simpl; try discriminate;
      subst; clear H.
    - destruct (sem_cast v1i t1 t2) as [ vi |] eqn:cast_eq; try discriminate.
      injection 1 as <-; clear H.

      destruct (sem_cast_find_symbol _ _ _ _ _ cast_eq v1_find_symbol)
        as (v & v_cast_eq & v_find_symbol).

      exists v; split; [| constructor ]; assumption.
  Qed. *)

  (* v1 ---sem_unary---> v2
     |                   |
 cval_match          cval_match
     |                   |
     cv1 --cval_unary--> cv2 *)
  Lemma cval_sem_unary_operation op v1 cv1 cv2 t :
      cval_match v1 cv1 ->
      cval_unary_operation op cv1 t = Some cv2 ->
      exists v2, (forall m, sem_unary_operation op v1 t m = Some v2) /\ cval_match v2 cv2.
  Proof. (*
    intros H. inversion H as [v1i ? v1_find_symbol]. subst cv1. subst. clear H.
(*
    inversion 1 as [ v1i ? v1_find_symbol |]; simpl; try discriminate;
      subst; clear H.
*)
    unfold cval_unary_operation.
    destruct (sem_unary_operation op v1i t Mem.empty) as [vi |] eqn:unary_eq. 2:discriminate.
    injection 1 as <-.

    assert (exists v, sem_unary_operation op v1 t m = Some v /\ val_find_symbol vi v) as (v & v_unary_eq & v_find_symbol).
    { unfold val_find_symbol, find_val_symbol in v1_find_symbol.
      destruct vi as [| | | | | i ofs ].
      - unfold sem_unary_operation, sem_notbool, sem_notint, sem_neg,
               sem_absfloat in unary_eq.
        destruct op;
          [ destruct (classify_bool t) | destruct (classify_notint t)
          | destruct (classify_neg t) | destruct (classify_neg t) ]; simpl.
          try discriminate unary_eq;
          destruct v1i; try discriminate unary_eq.
        + destruct (Int.eq i Int.zero); discriminate unary_eq.
        + destruct (Floats.Float.cmp _ _); discriminate unary_eq.
        + destruct (Int.eq i Int.zero); discriminate unary_eq.
        + destruct (Int64.eq i Int64.zero); discriminate unary_eq.
      - exists (Vint i); split; [| reflexivity ].
        destruct v1i as [| | | | i' ofs ];
          [| | | | destruct (CompcertStructures.find_symbol i') as [ b |] eqn:i_sym_eq ];
          try discriminate v1_find_symbol;
          injection v1_find_symbol as <-; clear v1_find_symbol;
          exact unary_eq.
      - exists (Vlong i); split; [| reflexivity ].
        destruct v1i as [| | | | i' ofs ];
          [| | | | destruct (CompcertStructures.find_symbol i') as [ b |] eqn:i_sym_eq ];
          try discriminate v1_find_symbol;
          injection v1_find_symbol as <-; clear v1_find_symbol;
          exact unary_eq.
      - exists (Vfloat f); split; [| reflexivity ].
        destruct v1i as [| | | | i' ofs ];
          [| | | | destruct (CompcertStructures.find_symbol i') as [ b |] eqn:i_sym_eq ];
          try discriminate v1_find_symbol;
          injection v1_find_symbol as <-; clear v1_find_symbol;
          exact unary_eq.
      - destruct v1i as [| | | | i' ofs' ];
          [| | | | destruct (CompcertStructures.find_symbol i') as [ b' |] eqn:i_sym_eq ];
          try discriminate v1_find_symbol;
          injection v1_find_symbol as <-; clear v1_find_symbol.
        + unfold sem_unary_operation, sem_notbool, sem_notint, sem_neg,
                 sem_absfloat in unary_eq.
          destruct op;
            [ destruct (classify_bool t) | destruct (classify_notint t)
            | destruct (classify_neg t) | destruct (classify_neg t) ];
            try discriminate unary_eq;
            destruct (Int.eq i0 Int.zero);
            discriminate unary_eq.
        + unfold sem_unary_operation, sem_notbool, sem_notint, sem_neg,
                 sem_absfloat in unary_eq.
          destruct op;
            [ destruct (classify_bool t) | destruct (classify_notint t)
            | destruct (classify_neg t) | destruct (classify_neg t) ];
            try discriminate unary_eq;
            destruct (Int64.eq i0 Int64.zero);
            discriminate unary_eq.
        + unfold sem_unary_operation, sem_notbool, sem_notint, sem_neg,
                 sem_absfloat in unary_eq.
          destruct op;
            [ destruct (classify_bool t) | destruct (classify_notint t)
            | destruct (classify_neg t) | destruct (classify_neg t) ];
            try discriminate unary_eq;
            destruct (Floats.Float.cmp Ceq f Floats.Float.zero);
            discriminate unary_eq.
        + unfold sem_unary_operation, sem_notbool, sem_notint, sem_neg,
                 sem_absfloat in unary_eq |- *.
          destruct op;
            [ destruct (classify_bool t) | destruct (classify_notint t)
            | destruct (classify_neg t) | destruct (classify_neg t) ];
            discriminate unary_eq.
    }

    exists v; split; [| constructor ]; assumption.
  Qed. *)
  Admitted.

  Definition optval_self_find_symbol (ov: option val) : Prop :=
    match ov with
    | Some (Vptr b ofs) => False
    | Some (Vundef) => False
    | _ => True
  end.

  (* v1,v2 ---sem_binarith---> v
     |                         |
 find_symbol               find_symbol
     |                         |
    v1',v2' --sem_binarith---> v' *)
  Remark sem_binarith_find_symbol sem_int sem_long sem_float sem_single
        v1 t1 v2 t2 v v1' v2' :
      sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 Mem.empty = Some v ->
      val_find_symbol v1 v1' -> val_find_symbol v2 v2' ->
      (forall sg n1 n2, optval_self_find_symbol (sem_int sg n1 n2)) ->
      (forall sg n1 n2, optval_self_find_symbol (sem_long sg n1 n2)) ->
      (forall n1 n2, optval_self_find_symbol (sem_float n1 n2)) ->
      exists v', sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 Mem.empty = Some v'
              /\ val_find_symbol v v'.
  Proof. Admitted. (*
    intros.
    assert (SELF: forall ov v, ov = Some v -> optval_self_find_symbol ov -> val_find_symbol v v).
    {
      intros. subst ov; simpl in H6. destruct v0; contradiction || constructor.
    }
    unfold sem_binarith in *.
    set (c := classify_binarith t1 t2) in *.
    set (t := binarith_type c) in *.
    destruct (sem_cast v1 t1 t) as [w1|] eqn:C1; try discriminate.
    destruct (sem_cast v2 t2 t) as [w2|] eqn:C2; try discriminate.
    exploit (sem_cast_find_symbol v1); eauto. intros (w1' & C1' & INJ1).
    exploit (sem_cast_find_symbol v2); eauto. intros (w2' & C2' & INJ2).
    rewrite C1'; rewrite C2'.
    unfold val_find_symbol, find_val_symbol in *.
    destruct c; DestructIval w1 INJ1; DestructIval w2 INJ2; discriminate || eauto.
  Qed. *)

  (* v1,v2 ---sem_shift---> v
     |                      |
 find_symbol            find_symbol
     |                      |
    v1',v2' --sem_shift---> v' *)
  Remark sem_shift_find_symbol sem_int sem_long v1 t1 v2 t2 v v1' v2' :
      sem_shift sem_int sem_long v1 t1 v2 t2 = Some v ->
      val_find_symbol v1 v1' -> val_find_symbol v2 v2' ->
      exists v', sem_shift sem_int sem_long v1' t1 v2' t2 = Some v'
             /\ val_find_symbol v v'.
  Proof.
    intros shift_eq v1_find_symbol v2_find_symbol. exists v.
    unfold sem_shift, val_find_symbol, find_val_symbol in *;
      destruct (classify_shift t1 t2);
      DestructIval v1 v1_find_symbol;
      DestructIval v2 v2_find_symbol.
    destruct (Int.ltu i0 Int.iwordsize);
      try discriminate shift_eq; injection shift_eq as <-; auto.
    destruct (Int64.ltu i0 Int64.iwordsize);
      try discriminate shift_eq; injection shift_eq as <-; auto.
    destruct (Int64.ltu i0 (Int64.repr 32));
      try discriminate shift_eq; injection shift_eq as <-; auto.
    destruct (Int.ltu i0 Int64.iwordsize');
      try discriminate shift_eq; injection shift_eq as <-; auto.
  Qed.

  (* v1,v2 ---sem_cmp---> v
     |                    |
 find_symbol          find_symbol
     |                    |
    tv1,tv2 --sem_cmp---> tv *)
  Remark sem_cmp_find_symbol m cmp v1 tv1 ty1 v2 tv2 ty2 v :
    sem_cmp cmp v1 ty1 v2 ty2 m = Some v ->
    val_find_symbol v1 tv1 ->
    val_find_symbol v2 tv2 ->
    match classify_cmp ty1 ty2 with
    | cmp_case_pp => true
    | cmp_case_pl => true
    | cmp_case_lp => true
    | cmp_case_pi _ => true
    | cmp_case_ip _ => true
    | cmp_default => false
    end = false -> (* involves pointers *)
    exists tv, (forall m', sem_cmp cmp tv1 ty1 tv2 ty2 m' = Some tv) /\
               val_find_symbol v tv.
  Proof. Admitted. (*
    intros cmp_eq v1_find_symbol v2_find_symbol not_pointer_comparison.
    unfold sem_cmp in *; destruct (classify_cmp ty1 ty2); try discriminate.
    assert (SELF: forall b, optval_self_find_symbol (Some (Val.of_bool b))).
    {
      destruct b; exact I.
    }
    edestruct sem_binarith_find_symbol
        as (tv & sem_binarth_eq & val_find_symbol_eq);
      [ .. | exists tv; split; [ intros _ |] ]; eauto.
  Qed. *)

  (* v1,v2 ---sem_binary---> v
     |                       |
 cval_match              cval_match
     |                       |
    cv1,cv2 --cval_binary--> cv *)
  Lemma cval_sem_binary_operation op v1 v2 cv1 cv2 cv t1 t2 :
      cval_match v1 cv1 -> cval_match v2 cv2 ->
      cval_binary_operation op cv1 t1 cv2 t2 = Some cv ->
      exists v, (forall m cenv, sem_binary_operation cenv op v1 t1 v2 t2 m = Some v) /\
                cval_match v cv.
  Proof. Admitted. (*
    inversion 1 as [ v1i ? v1_find_symbol ];
    inversion 1 as [ v2i ? v2_find_symbol ];
      subst; try discriminate; clear H H2.
    unfold cval_binary_operation.
    destruct (is_pointer_comparison op t1 t2) eqn:not_pointer_comparison;
      try discriminate.
    destruct cv as [ vi | ];
      destruct (sem_binary_operation op v1i t1 v2i t2 (Mem.empty(*, snd m*))) eqn:binary_eq;
      try discriminate;
      injection 1 as ->; clear H.

    assert (exists v,
        (forall m, sem_binary_operation op v1 t1 v2 t2 m = Some v) /\
        val_find_symbol vi v) as (v & v_binary_eq & v_find_symbol).
    { unfold val_find_symbol, find_val_symbol in v1_find_symbol, v2_find_symbol.
      unfold sem_binary_operation in binary_eq |- *.
      unfold is_pointer_comparison in not_pointer_comparison.

      destruct op.
      - (* add *)
        unfold sem_add in *; destruct (classify_add t1 t2).
        + DestructIval v1i v1_find_symbol.
          DestructIval v2i v2_find_symbol.
          TrivialExists.
          unfold val_find_symbol, find_val_symbol.
          injection binary_eq as <-; rewrite i_sym_eq; reflexivity.
        + DestructIval v1i v1_find_symbol.
          DestructIval v2i v2_find_symbol.
          TrivialExists.
          unfold val_find_symbol, find_val_symbol.
          injection binary_eq as <-; rewrite i_sym_eq; reflexivity.
        + DestructIval v1i v1_find_symbol.
          DestructIval v2i v2_find_symbol.
          TrivialExists.
          unfold val_find_symbol, find_val_symbol.
          injection binary_eq as <-; rewrite i_sym_eq; reflexivity.
        + DestructIval v1i v1_find_symbol.
          DestructIval v2i v2_find_symbol.
          TrivialExists.
          unfold val_find_symbol, find_val_symbol.
          injection binary_eq as <-; rewrite i_sym_eq; reflexivity.
        + edestruct sem_binarith_find_symbol
              as (v & sem_binarth_eq & val_find_symbol_eq);
            [ .. | exists v; split; [ intros _ |] ];
            (eassumption || intros; exact I).
      - (* sub *)
        unfold sem_sub in *; destruct (classify_sub t1 t2).
        + DestructIval v1i v1_find_symbol.
          DestructIval v2i v2_find_symbol.
          TrivialExists.
          unfold val_find_symbol, find_val_symbol.
          injection binary_eq as <-; rewrite i_sym_eq; reflexivity.
        + DestructIval v1i v1_find_symbol.
          DestructIval v2i v2_find_symbol.
          unfold val_find_symbol, find_val_symbol.
          destruct (eq_block b b1); try discriminate; subst b.
          rewrite i_sym_eq in i_sym_eq0; injection i_sym_eq0 as <-; rewrite dec_eq_true.
          destruct (Int.eq (Int.repr (sizeof ty)) Int.zero); try discriminate.
          TrivialExists.
          injection binary_eq as <-; reflexivity.
        + DestructIval v1i v1_find_symbol.
          DestructIval v2i v2_find_symbol.
          TrivialExists.
          unfold val_find_symbol, find_val_symbol.
          injection binary_eq as <-; rewrite i_sym_eq; reflexivity.
        + edestruct sem_binarith_find_symbol
              as (v & sem_binarth_eq & val_find_symbol_eq);
            [ .. | exists v; split; [ intros _ |] ];
            (eassumption || intros; exact I).
      - (* mul *)
        edestruct sem_binarith_find_symbol
            as (v & sem_binarth_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ];
          (eassumption || intros; exact I).
      - (* div *)
        edestruct sem_binarith_find_symbol
            as (v & sem_binarth_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ]; try eassumption;
          intros.
        destruct sg.
        destruct (Int.eq n2 Int.zero
                  || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
        destruct (Int.eq n2 Int.zero); exact I.
        destruct sg.
        destruct (Int64.eq n2 Int64.zero
                  || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
        destruct (Int64.eq n2 Int64.zero); exact I.
        exact I.
      - (* mod *)
        edestruct sem_binarith_find_symbol
            as (v & sem_binarth_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ]; try eassumption;
          intros.
        destruct sg.
        destruct (Int.eq n2 Int.zero
                  || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
        destruct (Int.eq n2 Int.zero); exact I.
        destruct sg.
        destruct (Int64.eq n2 Int64.zero
                  || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
        destruct (Int64.eq n2 Int64.zero); exact I.
        exact I.
      - (* and *)
        edestruct sem_binarith_find_symbol
            as (v & sem_binarth_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ];
          (eassumption || intros; exact I).
      - (* or *)
        edestruct sem_binarith_find_symbol
            as (v & sem_binarth_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ];
          (eassumption || intros; exact I).
      - (* xor *)
        edestruct sem_binarith_find_symbol
            as (v & sem_binarth_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ];
          (eassumption || intros; exact I).
      - (* shl *)
        edestruct sem_shift_find_symbol
            as (v & sem_shift_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ];
          (eassumption || intros; exact I).
      - (* shr *)
        edestruct sem_shift_find_symbol
            as (v & sem_shift_eq & val_find_symbol_eq);
          [ .. | exists v; split; [ intros _ |] ];
          (eassumption || intros; exact I).
        (* comparisons *)
      - eapply sem_cmp_find_symbol; eauto.
      - eapply sem_cmp_find_symbol; eauto.
      - eapply sem_cmp_find_symbol; eauto.
      - eapply sem_cmp_find_symbol; eauto.
      - eapply sem_cmp_find_symbol; eauto.
      - eapply sem_cmp_find_symbol; eauto.
    }

    exists v; split; [| constructor ]; assumption.
  Qed. *)
(*
  Lemma by_value_chunk_size_eq ty chunk :
      access_mode ty = By_value chunk ->
      size_chunk chunk = sizeof ty.
  Proof.
    intros acc_mode.
    destruct ty as [| [] [] | | [] | | | | | |];
      try discriminate acc_mode;
      injection acc_mode as <-;
      reflexivity.
  Qed.
*)

(* Return a list made by mapping f over i...(i+len-1) *)
Fixpoint flat_map_range {A : Set} (f : Z -> list A) (i : Z) (len : nat) : list A :=
  match len with
    | O => nil
    | S len' => f i ++ flat_map_range f (i+1) len'
  end.
(*
Fixpoint cval_to_init_data  (cv : cval) (ty : type) {struct ty}  : list AST.init_data :=
  match cv, ty with
    | CVval (Vint x), Tint I32 Unsigned _ => AST.Init_int32 x :: nil
    | CVval (Vlong x), Tlong _ _ => AST.Init_int64 x :: nil
    | CVval (Vfloat x), Tfloat F32 _ =>  AST.Init_float32 x :: nil
    | CVval (Vfloat x), Tfloat F64 _ =>  AST.Init_float64 x ::nil                              
    | CVany, _ => AST.Init_space 0 :: nil
    | _, _ => nil                                    
  end
with
fields_to_init_data (cs: PTree.t cval) (fs : fieldlist) : list AST.init_data :=
  match fs with
    | Fnil => nil
    | Fcons i ty fs' => (match (cs ! i) with
                           | None => AST.Init_space 0 :: nil
                           | Some cv => cval_to_init_data cv ty
                         end) ++ fields_to_init_data cs fs' 
  end.
*)
(* And a function to encode that the cval actually matches the type, as assumed by the functions. *)
Fixpoint forallb_range (f : Z -> bool) (i :Z) (len :nat) : bool :=
  match len with
    | O => true
    | S len' => f i && forallb_range f (i+1) len'
  end.

End WITH_MEM.
