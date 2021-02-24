Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep Linking SmallstepLinking.
Require Import Clight Ctypes Cop SimplLocalsproof.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef MemAbs ProgSim.

Lemma lts_trace_star {liA liB S} (L: lts liA liB S) s0 s1 t r:
  Star L s0 E0 s1 ->
  lts_trace L true s1 t r ->
  lts_trace L true s0 t r.
Proof.
  intros Hstar Htr.
  inv Htr. econstructor.
  eapply Smallstep.star_trans.
  eauto. eauto. auto. auto.
Qed.

Section LINK_FSIM.
  (* The section proves: L1 # L2 ≤ L1 ⊕ L3 *)
  Context {li: language_interface} (L1 L2: Smallstep.semantics li li)
          (HL1: determinate L1) (HL2: determinate L2)
          (L2': Genv.symtbl -> !li --o li).
  Let L := fun b: bool => if b then L1 else L2.
  Variable sk: AST.program unit unit.
  Let T1 := Impl.semantics sk L2' L1.
  Let T2 := semantics L sk.

  Hypothesis Hexcl: forall (i j : bool) (se : Genv.symtbl) (q : query li),
      Smallstep.valid_query ((L i) se) q = true ->
      Smallstep.valid_query ((L j) se) q = true ->
      i = j.

  Lemma link_sem_coh: sem_coherence T2.
  Proof.
    apply determ_coh. apply semantics_determinate.
    exact Hexcl. intros [|]. exact HL1. exact HL2.
  Qed.
  (* Inductive state_match se: Smallstep.state T1 -> Smallstep.state T2 -> Prop := *)
  (* | st_match s: *)
  (*     state_match se (Impl.st L1 s) (st L true s :: nil) *)
  (* | ext_match s s' sx t r: *)
  (*     Smallstep.after_external (L1 se) sx r s' -> *)
  (*     lts_trace (L2 se) false s t r -> *)
  (*     state_match se (Impl.ext L1 s' t) (st L false s :: st L true sx :: nil). *)

  Lemma link_fsim: forward_simulation cc_id cc_id T1 T2.
  Proof. Abort.
  (* constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta. *)
  (* intros se ? [ ] [ ] Hse. *)
  (* apply forward_simulation_step with (match_states := state_match se). *)
  (* - intros q ? [ ]. cbn. unfold L. admit. *)
  (* - intros q ? s1 [ ] Hinit. *)
  (*   inv Hinit. exists (st L true s :: nil). *)
  (*   split. constructor. *)
  (*   + admit.                  (* initial state implies valid_query *) *)
  (*   + apply H. *)
  (*   + constructor. *)
  (* - intros s1 s2 r Hs Hfs. *)
  (*   inv Hfs. inv Hs. *)
  (*   exists r. split. *)
  (*   constructor. apply H. constructor. *)
  (* - intros s1 s2 q Hs Hext. *)
  (*   inversion Hext. subst. inv Hs. inv H3. *)
  (*   exists tt, q. repeat apply conj; try constructor. *)
  (*   + apply H4. *)
  (*   + admit.                  (* disjoint query *) *)
  (*   + intros r' ? s1' [ ] Haft. *)
  (*     inv Haft. inv H8. *)
  (*     eexists (st L false s'0 :: st L true sx :: nil). *)
  (*     split. *)
  (*     constructor. *)

  Let S1 := hcomp_sem L2' L1 HL1 sk.
  Let S2 := lts_sem (semantics L sk) link_sem_coh.
  Hypothesis Happrox: forall se tr q r,
      has (L2' se) (tr, (q, r)) -> lts_lmaps (L2 se) tr (q, r).
  Hypothesis Hexcl': forall se i s q,
      Smallstep.at_external (L i se) s q ->
      forall j, Smallstep.valid_query (L j se) q = false.

  Inductive state_match se: _ -> _ -> Prop :=
  | st_match s:
      state_match se (Impl.st L1 s) (st L true s :: nil)
  | ext_match s s' sx t r:
      Smallstep.after_external (L1 se) sx r s' ->
      lts_trace (L2 se) false s t r ->
      state_match se (Impl.ext L1 s' t) (st L false s :: st L true sx :: nil).

  Lemma link_ref' se: ref (S1 se) (S2 se).
  Proof.
    intros [tr [q r]] Htr.
    cbn -[semantics] in *.
    inversion Htr as [? s0 ? ? Hvq Hinit Htrace]. subst.
    inv Hinit.
    apply lts_lmaps_intro with (s0 := st L true s :: nil).
    - unfold L. cbn in *. unfold valid_query.
      apply orb_true_intro. firstorder.
    - unfold L. cbn in *. constructor; auto.
    - clear -Htrace Happrox Hexcl'.
      remember (Impl.st L1 s) as sa.
      remember (st L true s :: nil) as sb.
      assert (Hs: state_match se sa sb). subst. constructor.
      clear Heqsa Heqsb.
      revert sb Hs. induction Htrace.
      + intros s0' Hs. rename s' into s1.
        assert (exists s1', Star ((semantics L sk) se) s0' E0 s1' /\
                       state_match se s1 s1') as (s1' & Hstar' & Hs').
        {
          clear IHHtrace Htrace.
          revert s0' Hs.
          induction H.
          - intros. eexists. split. constructor. auto.
          - intros. inv H.
            + inv Hs.
              specialize (IHstar (st L true s' :: nil)).
              exploit IHstar. constructor.
              intros (s1' & Hstar & Hs'). exists s1'.
              split. econstructor. apply step_internal. apply H2.
              apply Hstar. auto. auto.
            + inv Hs. rename s0 into sx. clear s.
              assert (Hlmap: lts_lmaps (L2 se) t3 (q, r0)).
              { apply Happrox. auto. }
              inv Hlmap. inv H8.
              specialize (IHstar (st L false s'0 :: st L true sx :: nil)).
              exploit IHstar. econstructor. eauto. auto.
              intros (s1' & Hstar' & Hs'). exists s1'.
              split. econstructor. eapply step_push. eauto.
              instantiate (1 := false).
              apply H5. apply H7.
              eapply Smallstep.star_trans; eauto.
              apply star_internal. eauto. auto. auto.
            + inv Hs.
              specialize (IHstar (st L true s0 :: nil)).
              exploit IHstar. constructor.
              intros (s1' & Hstar & Hs'). exists s1'.
              split. inv H4.
              eapply Smallstep.star_left; eauto.
              eapply step_pop; eauto. auto.
        }
        exploit IHHtrace. eauto.
        intros Htr. eapply lts_trace_steps; eauto.
      + intros s0' Hs. constructor.
        inv Hs. constructor. inv H. apply H1. inv H.
      + intros s0' Hs.
        inv H. inv H0. inv Hs. inv H3.
        eapply lts_trace_external. constructor. apply H4.
        eapply Hexcl'. instantiate (2 := false). apply H4.
        econstructor. apply H6.
        inv H8. exploit IHHtrace.
        econstructor. eauto. eauto.
        intro Htr'.
        eapply lts_trace_star; eauto.
        apply star_internal. apply H.
  Qed.

End LINK_FSIM.

Section C_LINK_SEM.
  Context (C: Clight.program) (p: Clight.program).
  Context {sk: AST.program unit unit}
          (Hsk: link (skel (semantics1 C)) (skel (semantics1 p)) = Some sk).
  Let L := fun b: bool => if b then semantics1 C else semantics1 p.
  Lemma c_vq_excl (i j: bool) se q:
    Smallstep.valid_query ((if i then semantics1 C else semantics1 p) se) q = true ->
    Smallstep.valid_query ((if j then semantics1 C else semantics1 p) se) q = true ->
    i = j.
  Admitted.

  Lemma c_link_coh: sem_coherence (semantics L sk).
  Proof.
    apply link_sem_coh.
    apply clight_determinate.
    apply clight_determinate.
    apply c_vq_excl.
  Qed.

  Program Definition c_link_sem se: coh_semantics li_d li_c :=
    {|
    vq := Smallstep.valid_query (semantics L sk se);
    lf := compcerto_lmap' (semantics L sk) c_link_coh se @ !li_dc;
    |}.
  Next Obligation.
    inv H1. apply H4.
  Qed.
End C_LINK_SEM.

Section IMPL_COMP_PROP.
  Context {liA liB liC: language_interface} (σ: Genv.symtbl -> !liA --o liB)
          (L: Smallstep.semantics liB liC) (HL: determinate L).
  Context {liX: language_interface} (lm: liX --o liA).
  Variable sk: AST.program unit unit.

  Let S1 := hcomp_sem (fun se => (σ se) @ !lm) L HL sk.
  Let S2 := hcomp_sem σ L HL sk.

  Inductive impl_match: _ -> _ -> Prop :=
  | impl_st_match s:
      impl_match (Impl.st L s) (Impl.st L s)
  | impl_ext_match s tx ty:
      has (!lm) (tx, ty) ->
      impl_match (Impl.ext L s tx) (Impl.ext L s ty).

  Lemma hcomp_lmap_ref se:
    ref (S1 se) (S2 se @ !lm).
  Proof.
    intros [trx [q r]] H. inv H. inv H4.
    assert (exists tr, dag_lmaps lm trx tr /\
                  lts_trace (Impl.lts σ L se) true (Impl.st L s0) tr r)
      as (tr & Hlmap & Htr).
    {
      rename H5 into Htr. clear -Htr.
      remember (@Impl.st liX liB liC L s0) as s.
      remember (@Impl.st liA liB liC L s0) as s'.
      assert (Hs: impl_match s s'). subst. constructor.
      clear Heqs Heqs'. revert s' Hs.
      induction Htr.
      - intros s1 Hs. clear Htr.
        assert (exists s1', Star (Impl.lts σ L se) s1 E0 s1' /\ impl_match s' s1')
          as (s1' & Hstar & Hs').
        {
          clear IHHtr. revert s1 Hs. induction H.
          - eexists. split; eauto. apply Smallstep.star_refl.
          - inv H.
            + intros s1 Hs. inv Hs.
              exploit IHstar. econstructor.
              intros (s1' & Hstar & Hs').
              exists s1'. split; auto.
              eapply Smallstep.star_left; eauto.
              eapply Impl.step_internal. eauto.
            + intros s1 Hs. inv Hs.
              destruct H4 as (tr' & Hlm & Htr).
              exploit IHstar. econstructor. eauto.
              intros (s1' & Hstar & Hs').
              exists s1'. split; auto.
              eapply Smallstep.star_left; eauto.
              eapply Impl.step_at_external; eauto.
            + intros s1 Hs. inv Hs.
              inv H3.
              exploit IHstar. econstructor.
              intros (s1' & Hstar & Hs').
              exists s1'. split; auto.
              eapply Smallstep.star_left; eauto.
              eapply Impl.step_after_external.
        }
        exploit IHHtr. eauto. intros (tr & Hlm & Htr).
        exists tr. split; auto. econstructor; eauto.
      - intros s1 Hs. eexists. split. constructor.
        constructor. inv H. inv Hs. econstructor. auto.
      - intros s1 Hs. inv H. inv H0. inv Hs. inv H2.
        exploit IHHtr. econstructor. apply H4.
        intros (tr' & Hlm & Htr'). eexists. split.
        econstructor; eauto.
        destruct b.
        eapply lts_trace_external; eauto. constructor. constructor.
    }
    exists tr. split; auto.
    econstructor. apply H2.
    econstructor. apply H. auto.
  Qed.
End IMPL_COMP_PROP.

(* The linking for two Clight components *)
Section C_LINK_FSIM.

  Context (C: Clight.program) (p: Clight.program).
  Context {sk: AST.program unit unit}
          (Hsk: link (skel (semantics1 C)) (skel (semantics1 p)) = Some sk).

  Let L := fun b: bool => if b then semantics1 C else semantics1 p.

  Lemma c_ext_vq_excl se (i: bool) s q:
    Smallstep.at_external (L i se) s q ->
    forall j : bool, Smallstep.valid_query (L j se) q = false.
  Proof.
  Admitted.

  Let S1 := c_hcomp_sem p C sk.
  Let S1' := hcomp_sem (clight_bigstep p) (semantics1 C) (clight_determinate C) sk.
  Let S2 := c_link_sem C p Hsk.

  Lemma c_link_fsim: coh_refinement cc_id S1 S2 sk.
  Proof.
    constructor.
    admit.
    intros q ? r t Ht [ ]. inv H.
    exists r. split. 2: { constructor; auto. }
    rename se2 into se.
    assert (H: has ((S1' se) @ !li_dc) (t, (q, r))).
    {
      exploit @hcomp_lmap_ref. apply Ht. auto.
    }
    inversion H as (tr & Hx & Hy).
    exists tr. split; auto.
    exploit @link_ref'.
    3: { apply Hy. }
    - intros. eapply bigstep_lmaps_soundness in H1.
      instantiate (1 := semantics1 p). exact H1.
    - apply c_ext_vq_excl.
    - intros. apply H1.
      Unshelve.
      apply clight_determinate.
      apply (c_vq_excl _ _ Hsk).
  Admitted.
End C_LINK_FSIM.
