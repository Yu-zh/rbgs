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
Require Import compcert.common.Values. (* val *)
Require Import compcert.lib.Maps. (* PTree, ZMap *)
(* Require Import compcert.common.Globalenvs. (* find_symbol *) *)

(* Liblayers modules *)
(* Require        liblayers.compcertx.CompcertStructures. (* find_symbol *) *)
(*
Inductive cval : Type :=
  | CVval : val -> cval
  | CVany : cval (* corresponds to any C value, can be refined by any, even undefined value *)
.
*)

Section CVAL_MATCH.
  (* return Some v when v is pointer and points to global identifier (block number < glob_threshold)
     or is basic val (int, long, float) *)
(*
  Class Decision (P: Prop) := decide: {P} + {~P}.
  Arguments decide P {_}.
*)
  Definition glob_threshold: block := 10000%positive.
  
  Definition glob_threshold_find_symbol (i: AST.ident) : option block :=
    if (i <=? glob_threshold)%positive then Some i else None.

  Definition find_val_symbol v := match v with
  | Vptr i ofs => match glob_threshold_find_symbol i with
    | Some b => Some (Vptr b ofs)
    | None => None
    end
  | Vundef => None
  | _ => Some v
  end.
  Definition val_find_symbol vi v := find_val_symbol vi = Some v.

  Inductive cval_match : val -> val -> Prop :=
  | CVMval : forall v vb, 
      val_find_symbol v vb -> cval_match vb v
  .

  (* value is of basic cval type: int, long or float *)
  Inductive cval_basic : val -> Prop :=
  | CVBint : forall i, cval_basic (Vint i)
  | CVBlong : forall i, cval_basic (Vlong i)
  | CVBfloat : forall f, cval_basic (Vfloat f)
  .

  (* compcert val matches DeepSEA basic cval: int, long, float & any *)
  Inductive cval_basic_match : val -> val -> Prop :=
  | CVBMval_int : forall i, cval_basic_match (Vint i) (Vint i)
  | CVBMval_long : forall i, cval_basic_match (Vlong i) (Vlong i)
  | CVBMval_float : forall f, cval_basic_match (Vfloat f) (Vfloat f)
  .
End CVAL_MATCH.
