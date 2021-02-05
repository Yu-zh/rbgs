Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory Smallstep.
Require Import Clight Ctypes Cop.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef MemAbs.

Definition q_with_mem (q: query li_d) m: query li_c :=
  match q with
    {|dq_vf:=vf;dq_sg:=sg;dq_args:=args|} =>
    {|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|}
  end.

Inductive vals_defined: list val -> Prop :=
| vals_defined_nil: vals_defined nil
| vals_defined_cons: forall v vs,
    v <> Vundef ->
    vals_defined vs ->
    vals_defined (v::vs).

Definition query_defined (q: query li_d): Prop :=
  match q with
    {|dq_vf:=_;dq_sg:=_;dq_args:=args|} => vals_defined args
  end.

Lemma defined_query_with_mem q q' m:
  query_defined q ->
  q_rel' q q' m ->
  q' = q_with_mem q m.
Proof.
  intros. inv H0. cbn in *.
  f_equal. symmetry.
  revert args' H1.
  induction H.
  intros. inv H1. auto.
  intros. inv H1. f_equal.
  inv H4; easy.
  apply IHvals_defined. auto.
Qed.

Lemma list_coh_refl {A} (xs ys: list (token A)):
  xs = ys ->
  list_coh _ xs ys.
Proof.
  revert ys. induction xs.
  - intros. constructor.
  - intros ? <-. constructor. reflexivity. intros.
    apply IHxs. auto.
Qed.

Lemma app_suffix_eq {A} (xs ys zs: list A):
  xs ++ ys = xs ++ zs -> ys = zs.
Proof.
  revert ys zs.
  induction xs. auto.
  intros. do 2 rewrite <- app_comm_cons in H.
  inv H. apply IHxs. auto.
Qed.

(* Correctness criterion for absfun modules *)
Section ABSFUN.
  (* Something weird about the symbol table *)
  Variable (p: Clight.program) (σ: !li_d --o li_d).
  Hypothesis sim:
    forall se, Genv.valid_for (AST.erase_program p) se ->
          forall t q r m,
            (* memory extension allows source query to have undefined values so
               the simulation in prog_sim is strengthened accordingly, which
               means the verification condition here also has to be augmented *)
            (* Otherwise, we could changed the calling convention used in the
               contextual refinement, which might be a better way to work
               around *)
            has σ (t, (q, r)) -> query_defined q /\
            has (clight_bigstep p se @ !li_dc)
                (t, (q_with_mem q m, r_with_mem r m)).

  Program Definition psim: prog_sim p (fun se => dag_ext σ) :=
    {|
    mspec_rel := fun Σ _ => Σ = dag_ext σ;
    init_mem := fun _ => True;
    |}.
  Next Obligation.
    exists m. repeat apply conj; try intuition.
    {
      inv H1. inv H0. destruct H1. inv H0; inv H1.
      eapply sim with (m := m) in H6; eauto.
      destruct H6. eapply defined_query_with_mem in H0; eauto.
      subst. inv H8. inv H3. rewrite app_nil_r.
      inv H1. destruct H0.
      eexists. split.
      apply H0. apply H1.
    }
    {
      inv H1. inv H0. destruct H1. inv H0; inv H1. inv H8. inv H3.
      rewrite app_nil_r.
      apply lmap_ext. intros xs ys.
      split.
      - inversion 1. destruct H1. inv H1; inv H3.
        assert (s = s0).
        {
          assert (list_coh _ s0 s).
          eapply prefix_coh with (t1 := a) (t2 := xs).
          apply list_coh_refl. apply H4.
          pose proof (has_coh _ _ _ _ H6 H9).
          exploit H3. symmetry. apply H1.
          intros [? ?]. apply H8. auto.
        }
        subst. apply app_suffix_eq in H4. subst.
        eexists. split. apply H5. apply H11.
      - inversion 1. destruct H1.
        exists (s :: x). split.
        constructor. apply H1.
        constructor. auto. apply H3.
    }
  Qed.
  Next Obligation.
    constructor.
    {
      intros.

    }
End ABSFUN.
