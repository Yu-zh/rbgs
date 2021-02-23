Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep Linking.
Require Import Clight Ctypes Cop SimplLocalsproof.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef MemAbs ProgSim.

(* Embedding preserves the simulation order:
   L1 ≤ L2 → ⟦ L1 ⟧ ⊑ ⟦ L2 ⟧ *)
Section FSIM_REF.
  Context {liA liB1 liB2} (L1: semantics liA liB1) (L2: semantics liA liB2).
  Context (HL1: sem_coherence L1) (HL2: sem_coherence L2).
  Context (cc: callconv liB1 liB2) (FSIM: forward_simulation 1 cc L1 L2).
  Let Σ1 := lts_sem L1 HL1.
  Let Σ2 := lts_sem L2 HL2.

  Lemma fsim_sound_cc: coh_refinement cc Σ1 Σ2 (skel L1).
  Proof.
    intros se1 se2 wB Hse Hsk.
    destruct FSIM as [[ind ord match_states _ H _]].
    specialize (H _ _ _ Hse Hsk).
    split.
    - intros. unfold Σ1. unfold Σ2. cbn.
      erewrite <- fsim_match_valid_query; eauto.
    - intros until t. intros Ht Hq. unfold Σ1 in Ht.
      inversion Ht as [? ? ? ? Hq1 Hs1 Ht1]. subst.
      exploit @fsim_match_initial_states; eauto. intros (i & s2 & Hs2 & Hs).
      erewrite <- fsim_match_valid_query in Hq1; eauto.
      assert (Hr2: exists r2, lts_trace (L2 se2) true s2 t r2 /\ match_reply cc wB r1 r2).
      {
        clear Hs1 Hs2 Ht Hq1 Hq. clear Σ1 Σ2. revert i s2 Hs.
        clear -Ht1 H. induction Ht1.
        - intros i s2 Hs.
          exploit @simulation_star; eauto.
          intros (i' & s2' & Hstar & Hs').
          specialize (IHHt1 _ _ Hs').
          destruct IHHt1 as (r2 & Ht' & Hr).
          exists r2. split; auto.
          econstructor; eauto.
        - intros i s2 Hs.
          exploit @fsim_match_final_states; eauto.
          intros (r2 & Ht' & Hr).
          exists r2. split; auto.
          constructor. auto.
        - intros i s2 Hs.
          exploit @fsim_match_external; eauto. cbn.
          intros ([ ] & q2 & Hext' & <- & <- & Hsim).
          exploit Hsim. reflexivity. apply H1.
          intros (i' & s2' & Haft' & Hs2').
          specialize (IHHt1 _ _ Hs2'). destruct IHHt1 as (r2 & Ht' & Hr).
          exists r2. split; auto.
          econstructor; eauto.
      }
      destruct Hr2 as (r2 & ? & ?).
      eexists. split. unfold Σ2. econstructor; eauto. auto.
  Qed.
End FSIM_REF.

Section COH_COMP.
  Context {liA liB liC: language_interface}
          (Σ1: Genv.symtbl -> !liA --o !liB)
          (Σ2: Genv.symtbl -> coh_semantics liB liC).
  Variable se: Genv.symtbl.
  Program Definition coh_comp: coh_semantics liA liC :=
    {|
    vq := vq _ _ (Σ2 se);
    lf := lf _ _ (Σ2 se) @ (Σ1 se);
    |}.
  Next Obligation.
    eapply Hvq. eauto.
  Qed.
End COH_COMP.

(* Underlay independence:
   Σ1 ⊑ Σ2 → Σ1 ∘ Σ ⊑ Σ2 ∘ Σ *)
Section MONOTONICITY.
  Context {liA liB liC1 liC2: language_interface}
          (Σ: Genv.symtbl -> !liA --o !liB)
          (Σ1: Genv.symtbl -> coh_semantics liB liC1)
          (Σ2: Genv.symtbl -> coh_semantics liB liC2).
  Variable sk : AST.program unit unit.
  Context (cc: callconv liC1 liC2) (REF: coh_refinement cc Σ1 Σ2 sk).
  (* This can be dischanged easily when sep_cklr is the calling convertion *)
  Hypothesis HΣ:
    forall se1 se2 w, match_senv cc w se1 se2 -> ref (Σ se1) (Σ se2).
  Let ΣL1 := coh_comp Σ Σ1.
  Let ΣL2 := coh_comp Σ Σ2.
  Lemma coh_comp_ref: coh_refinement cc ΣL1 ΣL2 sk.
  Proof.
    intros se1 se2 wB Hse Hsk. unfold ΣL1, ΣL2.
    specialize (REF _ _ _ Hse Hsk). specialize (HΣ _ _ _ Hse).
    clear -REF HΣ.
    destruct REF as [Hvq Href].
    split.
    - intros. cbn. now apply Hvq.
    - clear Hvq. cbn. intros until t. intros (w & Ht & Hw) Hq.
      specialize (Href _ _ _ _ Hw Hq).
      destruct Href as (r2 & Hw' & Hr).
      exists r2. split; auto.
      exists w. split; auto.
  Qed.
End MONOTONICITY.

(* Composition of refinement:
   Σ1 ⊑ Σ2 ∧ Σ2 ⊑ Σ3 → Σ1 ⊑ Σ3*)
Section REF_COMP.
  Context {liA liB1 liB2 liB3: language_interface}
          (Σ1: Genv.symtbl -> coh_semantics liA liB1)
          (Σ2: Genv.symtbl -> coh_semantics liA liB2)
          (Σ3: Genv.symtbl -> coh_semantics liA liB3).
  Variable sk : AST.program unit unit.
  Context (cc1: callconv liB1 liB2) (REF1: coh_refinement cc1 Σ1 Σ2 sk).
  Context (cc2: callconv liB2 liB3) (REF2: coh_refinement cc2 Σ2 Σ3 sk).
  Lemma coh_ref_comp: coh_refinement (cc1 @ cc2) Σ1 Σ3 sk.
    intros se1 se3 wB Hse Hsk. destruct wB as [[se2 wB1] wB2].
    destruct Hse as [Hse1 Hse2].
    specialize (REF1 _ _ _ Hse1 Hsk).
    eapply match_senv_valid_for in Hsk; eauto.
    specialize (REF2 _ _ _ Hse2 Hsk).
    split.
    - intros q1 q3 Hq13. destruct Hq13 as (q2 & Hq12 & Hq23).
      erewrite coh_vq_ref; [ | exact REF1 | eauto ].
      erewrite coh_vq_ref; [ | exact REF2 | eauto ].
      reflexivity.
    - intros q1 q3 r1 t Ht Hq13. destruct Hq13 as (q2 & Hq12 & Hq23).
      exploit @coh_lf_ref. exact REF1. eauto. eauto.
      intros (r2 & Ht2 & Hr2).
      exploit @coh_lf_ref. exact REF2. eauto. eauto.
      intros (r3 & Ht3 & Hr3).
      exists r3. split; auto.
      esplit; eauto.
  Qed.
End REF_COMP.

Section LTS.
  Context {liA liB S} (L : lts liA liB S).

  (* a sequence of external calls with no internal steps in between
     but we allow internal steps at the beginning and end *)
  Inductive lts_ext_calls : bool -> S -> token (!liA) -> bool -> S -> Prop :=
  | lts_ext_nil: forall s s',
      Star L s E0 s' ->
      lts_ext_calls false s nil false s'
  | lts_ext_cons: forall s s' s'' q r t,
      Smallstep.at_external L s q ->
      Smallstep.after_external L s r s' ->
      lts_ext_calls false s' t false s'' ->
      lts_ext_calls false s ((q, r) :: t) false s''
  | lts_ext_init: forall s s' s'' t,
      Star L s E0 s' ->
      lts_ext_calls false s' t false s'' ->
      lts_ext_calls true s t false s''.

  Lemma lts_trace_concat s s' t1 t2 r:
    lts_ext_calls true s t1 false s' ->
    lts_trace L false s' t2 r ->
    lts_trace L true s (t1 ++ t2) r.
  Proof.
    intros H.
    eapply lts_ext_calls_ind
      with (P := fun b s t b' s' =>
                   lts_trace L false s' t2 r ->
                   lts_trace L true s (t ++ t2) r).
    - intros. eapply lts_trace_steps; eauto.
    - intros until t. intros Hext Haft Hcalls IH H'.
      specialize (IH H'). rewrite <- app_comm_cons.
      eapply lts_trace_steps. eapply Smallstep.star_refl.
      eapply lts_trace_external; eauto.
    - intros until t. intros Hstar Hcalls IH H'.
      specialize (IH H').
      inv IH.
      eapply lts_trace_steps; [ | eauto ].
      eapply Smallstep.star_trans; eauto.
    - eauto.
  Qed.
End LTS.

Program Definition clight_coh (C: Clight.program) se :=
  {|
  vq := fun q => Genv.is_internal (Genv.globalenv se C) (entry q);
  lf := clight C se;
  |}.
Next Obligation.
  now inv H.
Qed.

Section REFINE.
  Variable C: Clight.program.
  Variable Σ: Genv.symtbl -> !li_d --o !li_d.
  Context {p: Clight.program} (ps: prog_sim p Σ).
  (* li_dc is simply an adapter that forgets the memory in C calling convertions
     so that outgoing calls from C can interact with the specification *)
  Variable sk: AST.program unit unit.
  Let T1 := fun se => clight C se @ !li_dc @ (Σ se). (* linear function *)
  Let T2 := c_mix_sem C Σ sk.              (* coherence semantics *)

  Lemma mix_sem_ref' se: ref (T1 se) (T2 se).
  Proof.
    intros trace. cbn -[clight].
    destruct trace as [bot_tr top_tr].
    intros (mid_tr_c & (mid_tr_d & Hbot & Hmid) & Htop).
    destruct top_tr as [top_q top_r].
    inversion Htop as [? s0 ? ? Hvq Hinit Htrace]. subst.
    econstructor; [ apply Hvq | econstructor; apply Hinit | ].
    clear Hvq Hinit Htop. clear T1 T2.
    pose proof (reactive_spec _ _ ps se) as RS.
    remember (Σ se) as σ0. clear Heqσ0.
    pose proof (self_reachable σ0) as Hreach.
    remember (reachable σ0) as reachp.
    revert mid_tr_d bot_tr Hreach Hmid Hbot.
    generalize σ0. subst reachp.
    eapply lts_trace_ind
      with (P := fun b s t r =>
                   forall (σ : !li_d --o !li_d) (mid_tr_d : token (!li_d))
                     (bot_tr : token (!li_d)) ,
                     reachable σ0 σ ->
                     dag_lmaps li_dc mid_tr_d t ->
                     has σ (bot_tr, mid_tr_d) ->
                     lts_trace (Abs.lts Σ (semantics1 C) li_rel se) true (Abs.st (semantics1 C) s σ) bot_tr r).
    4: {  apply Htrace. }
    - intros until r. intros Hstar H IH.
      intros ? ? ? Hreach Hmid Hbot. specialize (IH _ _ _ Hreach Hmid Hbot).
      inversion IH as [? s1 ? ? Hstar' | | ]. subst.
      eapply lts_trace_steps; [ | eauto].
      eapply Smallstep.star_trans; eauto.
      2: { instantiate (1 := E0). auto. }
      clear -Hstar. induction Hstar.
      + eapply Smallstep.star_refl.
      + eapply Smallstep.star_left; eauto.
        eapply Abs.step_internal; eauto.
    - intros until bot_tr. intros Hreach Hmid Hbot. eapply lts_trace_steps.
      eapply Smallstep.star_refl.
      inv Hmid. eapply RS in Hreach. inv Hreach. clear SPLIT.
      eapply EMPTY in Hbot. subst.
      eapply lts_trace_final.
      eapply Abs.final_state_intro. auto.
    - intros s qx rx s' t r Hext Haft H' IH.
      intros ? ? ? Hreach Hmid Hbot.
      inversion Hmid as [| [qd rd] [? ?] mid_tr_d' mid_tr_c' Hq Hmid']. subst.
      exploit RS. apply Hreach. inversion 1. clear H EMPTY.
      edestruct SPLIT as (t1 & t2 & Ht & Hexec). apply Hbot. subst.
      assert (Hnext': has (next σ t1 qd rd) (t2, mid_tr_d')) by apply Hbot.
      assert (Hnext: reachable σ0 (next σ t1 qd rd)). apply step_reachable; auto.
      specialize (IH _ _ _ Hnext Hmid' Hnext'). clear SPLIT.
      inversion IH as [? s1 ? ? Hstar | | ]. subst.
      eapply lts_trace_concat; eauto.
      eapply lts_ext_init.
      eapply Smallstep.star_one. eapply Abs.step_at_external; eauto.
      clear -Hstar.
      remember (next σ t1 qd rd) as σ'. clear Heqσ'.
      induction t1.
      + eapply lts_ext_nil.
        eapply Smallstep.star_left. eapply Abs.step_after_external.
        eapply Hstar. auto.
      + destruct a as [qx rx].
        eapply lts_ext_cons.
        constructor. econstructor. apply IHt1.
  Qed.

  Let T1' := (coh_comp Σ (coh_comp (fun se => !li_dc) (clight_coh C))).
  Lemma mix_sem_ref:
    coh_refinement 1 T1' T2 sk.
  Proof.
    intros se ? [ ] [ ] Hsk1.
    split.
    - intros ? ? [ ]. now cbn.
    - intros ? ? ? ? H [ ].
      exists r1. split; try easy.
      exploit mix_sem_ref'. unfold T1.
      unfold coh_comp in H. cbn -[lmap_compose] in H.
      rewrite lmap_compose_assoc in H. apply H. auto.
  Qed.
End REFINE.

Require Import CallconvAlgebra.
Section CC_REF.
  Context {liA liB1 liB2: language_interface}
          (cc1 cc2: callconv liB1 liB2) (Hcc: ccref cc1 cc2).
  Variable sk: AST.program unit unit.
  Context (Σ1: Genv.symtbl -> coh_semantics liA liB1)
          (Σ2: Genv.symtbl -> coh_semantics liA liB2)
          (HΣ: coh_refinement cc2 Σ1 Σ2 sk).

  Lemma coh_cc_ref: coh_refinement cc1 Σ1 Σ2 sk.
  Proof.
    intros se1 se2 wB Hse Hsk.
    split.
    - intros q1 q2 Hq.
      specialize (Hcc _ _ _ _ _ Hse Hq).
      destruct Hcc as (w' & Hse' & Hq' & ?).
      specialize (HΣ _ _ _ Hse' Hsk).
      eapply coh_vq_ref; eauto.
    - intros q1 q2 r1 t Ht Hq.
      specialize (Hcc _ _ _ _ _ Hse Hq).
      destruct Hcc as (w' & Hse' & Hq' & ?).
      specialize (HΣ _ _ _ Hse' Hsk).
      exploit @coh_lf_ref; eauto.
      intros (r2 & Ht' & Hr).
      exists r2. split; auto.
  Qed.
End CC_REF.

Section CONTEXTUAL_REF.
  Context (Σ: Genv.symtbl -> !li_d --o !li_d) (p: Clight.program)
          (ps: prog_sim p Σ).
  Variable C: Clight.program.
  Variable U: Genv.symtbl -> !li_d --o !li_d.
  Context {sk: AST.program unit unit}
          (Hsk: link (skel (semantics1 C)) (skel (semantics1 p)) = Some sk).
  (* ⟦ C ⟧ ∘ Σ ∘ U *)
  Let S1 := (coh_comp U (coh_comp Σ (coh_comp (fun se => !li_dc) (clight_coh C)))).
  (* ⟦ C ⊕ p ⟧ ∘ U *)
  Let S2 := (coh_comp U (c_hcomp_sem p C sk)).
  Let Sx := (c_mix_sem C Σ sk).

  (* Let sk := AST.erase_program C. *)
  Lemma contextual_ref: coh_refinement (sepcc ps) S1 S2 sk.
  Proof.
    unfold S1, S2.
    apply coh_comp_ref. 2: { now intros ? ? ? [ ] x. }.
    apply coh_cc_ref with (cc2 := (1 @ sepcc ps)%cc).
    apply cc_compose_id_left.
    apply coh_ref_comp with (Σ2 := Sx).
    eapply mix_sem_ref. eauto.
    apply fsim_sound_cc. apply fsim_abs_impl; auto.
  Qed.
End CONTEXTUAL_REF.

Section VCOMP.
  Context (Σ1: Genv.symtbl -> !li_d --o !li_d)
          (p1: Clight.program) (ps1: prog_sim p1 Σ1).
  Context (Σ2: Genv.symtbl -> !li_d --o !li_d)
          (p2: Clight.program) (ps2: prog_sim p2 Σ2).
  Variable C: Clight.program.
  Variable U: Genv.symtbl -> !li_d --o !li_d.

End VCOMP.
