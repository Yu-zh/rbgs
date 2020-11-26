Require Import Coq.Logic.ProofIrrelevance. (* It will be imported by compcert.common.AST anyway *)

Lemma unique_eq_refl {A} {x: A}:
  forall (H: x = x), H = eq_refl.
Proof.
  intros H.
  apply ProofIrrelevance.proof_irrelevance.
Qed.

Lemma eq_rect_eq:
  forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof.
  intros.
  rewrite ProofIrrelevance.proof_irrelevance with (p1:=h) (p2:=eq_refl p).
  reflexivity.
Qed.
