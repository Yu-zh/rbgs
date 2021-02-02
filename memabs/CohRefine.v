Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep Linking.
Require Import Clight Ctypes Cop SimplLocalsproof.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef.

Section LTS.
  Context {liA liB S} (L : lts liA liB S).

  Inductive lts_ext_calls : S -> token (!liA) -> S -> Prop :=
  | lts_ext_nil: forall s,
      lts_ext_calls s nil s
  | lts_ext_cons: forall s s' s'' q r t,
      Smallstep.at_external L s q ->
      Smallstep.after_external L s r s' ->
      lts_ext_calls s' t s'' ->
      lts_ext_calls s ((q, r) :: t) s''.

  Lemma lts_trace_concat s s' t1 t2 r:
    lts_ext_calls s t1 s' ->
    lts_trace L false s' t2 r ->
    lts_trace L false s (t1 ++ t2) r.
  Proof.
    intros H. induction H.
    - auto.
    - intros H'. specialize (IHlts_ext_calls H').
      rewrite <- app_comm_cons. econstructor; eauto.
      eapply lts_trace_steps. eapply Smallstep.star_refl. auto.
  Qed.
End LTS.

(* So far I don't know how to prove this generally. Therefore, I think I will
just add it to the DeepSEA correct criterion and it should be fairly
straightforward for both getter/setter cases and abstract function cases *)
Lemma trace_split {liA liB: language_interface} (σ: !liA --o !liB) q t r rest:
  has σ (t, (q,r) :: rest) ->
  exists t1 t2, t = t1 ++ t2 /\
           exec σ q t1 r /\
           has (next σ t1 q r) (t2, rest).
(* Proof. *)
(*   intros H. *)
(*   assert (H': exists t', has σ (t', (q,r) :: nil)). *)

Section REFINE.
  Variable se: Genv.symtbl.
  Variable C: Clight.program.
  Variable Σ: Genv.symtbl -> !li_d --o !li_d.
  (* li_dc is simply an adapter that forgets the memory in C calling
  convertions *)
  Let T1 := clight C se @ !li_dc @ (Σ se).
  Let sk := AST.erase_program C.
  (* Note that we can't prove the determinism of the mixed semantics. However we
  should be able to prove the coherence when embed it into a linear function *)
  Context (H : determinate (Abs.c_semantics sk C Σ)).
  Let T2 := compcerto_lmap (Abs.c_semantics sk C Σ) H se.

  Lemma mix_sem_ref: ref T1 T2.
  Proof.
    intros trace. cbn -[clight].
    destruct trace as [bottom_tr top_tr].
    intros (mid_tr_c & (mid_tr_d & Hbot & Hmid) & Htop).
    destruct top_tr as [top_q top_r].
    inversion Htop as [? s0 ? ? Hvq Hinit Htrace]. subst.
    econstructor; [ apply Hvq | econstructor; apply Hinit | ].
    clear Hvq Hinit Htop. clear T1 H T2.
    revert mid_tr_d bottom_tr Σ Hmid Hbot.
    induction Htrace.
    admit. admit.

  End REFINE.
