Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep Linking.
Require Import Clight Ctypes Cop SimplLocalsproof.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef MemAbs ProgSim.

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

Section REFINE.
  Variable se: Genv.symtbl.
  Variable C: Clight.program.
  Variable Σ: Genv.symtbl -> !li_d --o !li_d.
  Context {p: Clight.program} (ps: prog_sim p Σ).
  (* Hypothesis RS: forall σ, reachable (Σ se) σ -> reactive σ. *)
  (* li_dc is simply an adapter that forgets the memory in C calling convertions
  so that outgoing calls from C can interact with the specification *)
  Let T1 := clight C se @ !li_dc @ (Σ se).
  Let T2 := c_mix_sem C Σ se.

  Lemma mix_sem_ref: ref T1 T2.
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
End REFINE.
