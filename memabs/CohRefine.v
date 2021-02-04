Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep Linking.
Require Import Clight Ctypes Cop SimplLocalsproof.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef MemAbs.

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
      with (P := fun b s t b' s' => lts_trace L false s' t2 r -> lts_trace L true s (t ++ t2) r).
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

Section MIX_SEM.

  Context {liA liB: language_interface} (Σ: Genv.symtbl -> !liA --o !liB).
  Context {liC liD: language_interface} (L: semantics liC liD) (HL: determinate L).
  Variable li_rel: token liB -> token liC -> Prop.

  Definition li_rel_determ : Prop :=
    forall qx rx qy ry qx' rx' qy' ry',
    li_rel (qx, rx) (qy, ry) ->
    li_rel (qx', rx') (qy', ry') ->
    qy = qy' -> qx = qx' /\ (rx = rx' -> ry = ry').

  Hypothesis lr_determ: li_rel_determ.

  Lemma star_ext_state se σ s w ws t s':
    Star (Abs.lts Σ L li_rel se) (Abs.ext L s (w :: ws) σ) t s' ->
    s' = Abs.ext L s (w :: ws) σ.
  Proof.
    intros Hstar.
    inv Hstar. reflexivity. inv H.
  Qed.

  Lemma trace_prefix se s w σ t r:
    lts_trace (Abs.lts Σ L li_rel se) false (Abs.ext L s w σ) t r ->
    exists t', t = w ++ t'.
  Proof.
    revert t. induction w.
    - intros. eexists. reflexivity.
    - intros t Hlts.
      inv Hlts. inv H. inv H. inv H0.
      inv H1. destruct w.
      + eexists. cbn. reflexivity.
      + eapply star_ext_state in H.
        subst. exploit IHw. eauto.
        intros [? ?]. eexists.
        rewrite <- app_comm_cons. f_equal. eauto.
  Qed.

  Program Definition mix_sem_lmap se: !liA --o liD :=
    {|
    has '(t, u) := lts_lmaps (Abs.semantics (skel L) li_rel Σ L se) t u;
    |}.
  Next Obligation.
    rename l0 into bot_tr'. rename l into bot_tr.
    rename q0 into q'. rename r0 into r'.
    intros Hcoh. assert (q' = q -> r' = r /\ bot_tr' = bot_tr).
    {
      intros ->. inv H. inv H0. inv H5. inv H7.
      exploit (sd_initial_determ (HL se)). apply H. apply H0.
      intros ->. clear H H0 H2 H3.
      revert bot_tr Hcoh H8. induction H6.
      - intros tr Hcoh Hlts.
        inv Hlts. apply IHlts_trace. auto.
        replace s' with s'0. auto.
        clear - lr_determ Hcoh HL H H0 H1 H6. revert s'0 H0 H1.
        induction H.
        + intros. inv H0; auto.
          inv H6.
          * inv H0. inv H.
            -- exploit (sd_final_nostep (HL se)); eauto. easy.
            -- exploit (sd_final_noext (HL se)); eauto. easy.
          * inv H0. inv H.
        + intros. specialize (IHstar H6).
          inv H2.
          * inv H3.
            -- inv H1. inv H.
               ** exploit (sd_final_nostep (HL se)); eauto. easy.
               ** exploit (sd_final_noext (HL se)); eauto. easy.
            -- inv H1. inv H.
          * inv H.
            -- inv H4.
               ** exploit (sd_determ (HL se)). apply H1. apply H10.
                  exploit (sd_traces (HL se)). apply H1.
                  exploit (sd_traces (HL se)). apply H10. intros l1 l2.
                  intros [Hmt Ht].
                  assert (t1 = t3 /\ t2 = t4).
                  destruct t1. inv Hmt. split; auto.
                  destruct t1. 2: { simpl in l2. try omegaContradiction. }
                  destruct t3. inv Hmt. destruct t3.
                  2: { simpl in l1. try omegaContradiction. }
                  simpl in H7. inv H7. split; auto.
                  exploit Ht. apply H. intros <-.
                  destruct H as [<- <-].
                  eapply IHstar. auto. auto.
               ** exploit (sd_at_external_nostep (HL se)); eauto. easy.
            -- inv H4.
               ** exploit (sd_at_external_nostep (HL se)); eauto. easy.
               ** exploit (sd_at_external_determ (HL se)). apply H1. apply H11.
                  intros <-. inv H8. inv H13.
                  exploit lr_determ. apply H9. apply H16. auto.
                  intros [<- Hr].
                  destruct w; destruct w0.
               ++ pose proof (has_coh _ _ _ _ H H4).
                  cbn in H8. exploit H8. constructor.
                  intros [Hl Hqr]. inv Hl.
                  cbn in H15. exploit (proj2 H15). auto. intros <-.
                  exploit Hr. auto. intros <-.
                  exploit (sd_after_external_determ (HL se)). apply H2. apply H12.
                  intros <-. simpl in H7. subst. apply IHstar. auto. auto.
               ++ pose proof (has_coh _ _ _ _ H H4).
                  cbn in H8. exploit H8. constructor.
                  intros [Hl Hqr]. inv Hl.
                  cbn in H15. exploit (proj2 H15). auto. intros <-.
                  exploit Hqr. constructor. intros. easy.
               ++ pose proof (has_coh _ _ _ _ H H4).
                  cbn in H8. exploit H8. constructor.
                  intros [Hl Hqr]. inv Hl.
                  cbn in H15. exploit (proj2 H15). auto. intros <-.
                  exploit Hqr. constructor. intros. easy.
               ++ pose proof (has_coh _ _ _ _ H H4).
                  cbn in H8. exploit H8.
                  exploit star_ext_state. apply H0. intros ->.
                  exploit star_ext_state. apply H5. intros ->.
                  exploit trace_prefix. apply H6. intros [? ->].
                  exploit trace_prefix. apply H3. intros [? ->].
                  eapply prefix_coh. eauto.
                  intros [Hl Hqr]. inv Hl.
                  cbn in H15. exploit (proj2 H15). auto.
                  intros <-. exploit Hr. auto. intros <-.
                  exploit (sd_after_external_determ (HL se)). apply H2. apply H12.
                  intros <-. simpl in H7. subst.
                  exploit Hqr. auto. intros. inv H7.
                  apply IHstar. auto. auto.
            -- inv H4. simpl in H7. subst.
               apply IHstar. auto. auto.
      - intros tr Hcoh Hlts. inv Hcoh.
        + inv H. inv Hlts.
          * inv H. exploit (sd_final_determ (HL se)). apply H0. apply H4. easy.
          * inv H.
        + inv Hlts. inv H. inv H0.
          exploit (sd_final_determ (HL se)). apply H1. apply H4. easy.
      - intros tr Hcoh Hlts.
        inv Hcoh.
        + inv Hlts. inv H1. inv H.
        + destruct b as [q' r'].
          inv Hlts. inv H. inv H7.
          inv H0. inv H9. exploit H5. auto.
          intros Hcoh'.
          exploit IHlts_trace; eauto. intros [<- <-]. easy.
    }
    split. split; auto. apply H1. intros. apply H1. inv H2. auto.
  Qed.

End MIX_SEM.

Lemma determ_li_dc: li_rel_determ li_rel.
Proof.
  unfold li_rel_determ.
  intros. inv H. inv H0.
  split. auto. intros. inv H. auto.
Qed.

Definition clight_mix_lmap p (Σ : Genv.symtbl -> !li_d --o !li_d) se :=
  mix_sem_lmap Σ (semantics1 p) (clight_determinate p)
               li_rel determ_li_dc se.

Section REFINE.
  Variable se: Genv.symtbl.
  Variable C: Clight.program.
  Variable Σ: Genv.symtbl -> !li_d --o !li_d.
  Context {p: Clight.program} (ps: prog_sim p Σ).
  (* li_dc is simply an adapter that forgets the memory in C calling convertions
  so that outgoing calls from C can interact with the specification *)
  Let T1 := clight C se @ !li_dc @ (Σ se).
  Let T2 := clight_mix_lmap C Σ se.

  Lemma mix_sem_ref: ref T1 T2.
  Proof.
    intros trace. cbn -[clight].
    destruct trace as [bottom_tr top_tr].
    intros (mid_tr_c & (mid_tr_d & Hbot & Hmid) & Htop).
    destruct top_tr as [top_q top_r].
    inversion Htop as [? s0 ? ? Hvq Hinit Htrace]. subst.
    econstructor; [ apply Hvq | econstructor; apply Hinit | ].
    clear Hvq Hinit Htop. clear T1 T2.
    pose proof (reactive_spec _ _ ps se) as RS.
    remember (Σ se) as σ. clear Heqσ ps.
    revert mid_tr_d bottom_tr σ RS Hmid Hbot.
    eapply lts_trace_ind
      with (P := fun b s t r =>
                   forall (mid_tr_d : list (d_query * d_reply))
                     (bottom_tr : token (!li_d)) (σ : !li_d --o !li_d),
                     reactive σ ->
                     dag_lmaps li_dc mid_tr_d t ->
                     has σ (bottom_tr, mid_tr_d) ->
                     lts_trace (Abs.lts Σ (semantics1 C) li_rel se) true (Abs.st (semantics1 C) s σ) bottom_tr r).
    4: {  apply Htrace. }
    - intros until r. intros Hstar H IH.
      intros ? ? ? RS Hmid Hbot. specialize (IH _ _ _ RS Hmid Hbot).
      inversion IH as [? s1 ? ? Hstar' | | ]. subst.
      eapply lts_trace_steps; [ | eauto].
      eapply Smallstep.star_trans; eauto.
      2: { instantiate (1 := E0). auto. }
      clear -Hstar. induction Hstar.
      + eapply Smallstep.star_refl.
      + eapply Smallstep.star_left; eauto.
        eapply Abs.step_internal; eauto.
    - intros until σ. intros RS Hmid Hbot. eapply lts_trace_steps.
      eapply Smallstep.star_refl.
      inv Hmid. inv RS. clear SPLIT.
      eapply EMPTY in Hbot. subst.
      eapply lts_trace_final.
      eapply Abs.final_state_intro. auto.
    - intros s qx rx s' t r Hext Haft H' IH.
      intros ? ? ? RS Hmid Hbot.
      inversion Hmid as [| [qd rd] [? ?] mid_tr_d' mid_tr_c' Hq Hmid']. subst.
      inv RS. clear EMPTY.
      edestruct SPLIT as (t1 & t2 & Ht & Hexec & Hnext). apply Hbot.
      subst bottom_tr.
      assert (Hnext': has (next σ t1 qd rd) (t2, mid_tr_d')) by apply Hbot.
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
End REFINE.
