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
  | deref_same_union:
      deref_same ty b ofs m1 m2.
      
  Inductive unchanged_on (m1: mem)(m2: mem) : Prop :=
  | unchanged_on_cond id l (v : globvar type) (ty : type):
      Genv.find_symbol ge id = Some l ->
      Genv.find_def ge l = Some (Gvar v) ->
      ty = gvar_info v ->
      deref_same ty l Ptrofs.zero m1 m2 ->
      unchanged_on m1 m2.                  
End UNCHANGED_MEM.
