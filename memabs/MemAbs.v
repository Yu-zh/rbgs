Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep Linking.
Require Import Clight Ctypes Cop SimplLocalsproof.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef SepCKLR ProgSim.

Definition get_mem (s: state) : mem :=
  match s with
  | State _ _ _ _ _ m => m
  | Callstate _ _ _ m => m
  | Returnstate _ _ m => m
  end.


Lemma perm_imp m b ofs k p:
  Mem.perm m b ofs k p ->
  Mem.perm m b ofs Max Nonempty.
Proof.
  intros Hp.
  destruct k.
  - eapply Mem.perm_implies; eauto. constructor.
  - eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
Qed.

Hypothesis module_var_dec: forall se p b ofs,
    {module_var (globalenv se p) b ofs} + {~module_var (globalenv se p) b ofs}.

Lemma mem_match_sim p m1 m2 m2' mx se Hvbx Hvb:
  Mem.unchanged_on (fun (b : block) (ofs : Z) => ~ module_var (globalenv se p) b ofs) m2 m2' ->
  Mem.nextblock m2 = Mem.nextblock m2' ->
  sepc_mm p (sepcw p se mx Hvbx) m1 m2 ->
  sepc_mm p (sepcw p se m2' Hvb) m1 m2'.
Proof.
  intros H Hnext Hm. inversion Hm as [? ? ? ? ? Hext Hinv Hx]. subst. clear Hm.
  constructor.
  - constructor.
    (* nextblock m1 = nextblock m2' *)
    + destruct Hext. congruence.
    (* memory injection *)
    + constructor.
      * inversion 1. subst. intros Hp.
        exploit Mem.mi_perm. apply Mem.mext_inj; apply Hext. eauto. eauto.
        replace (ofs + 0) with ofs in * by omega. intros Hp'.
        destruct (module_var_dec se p b2 ofs) as [Hmv | Hmv].
        (* zero permission blocks inject into any block *)
        -- eapply Hx in Hmv. exfalso. apply Hmv.
           eapply perm_imp. eauto.
        (* unchanged vars perserve injections *)
        -- rewrite <- Mem.unchanged_on_perm. apply Hp'. apply H. apply Hmv.
           eapply Mem.perm_valid_block. eauto.
      * inversion 1. subst. intros.
        exploit Mem.mi_align; eauto. apply Hext.
      * inversion 1. subst. intros Hp.
        exploit Mem.mi_memval; [ apply Hext | eauto | eauto | ]. intros Hv.
        replace (ofs + 0) with ofs in * by omega.
        destruct (module_var_dec se p b2 ofs) as [Hmv | Hmv].
        -- eapply Hx in Hmv. exfalso.
           apply Hmv. eapply perm_imp. eauto.
        -- exploit Mem.unchanged_on_contents. apply H. apply Hmv.
           exploit Mem.mi_perm; [ apply Hext | eauto | eauto | ].
           replace (ofs + 0) with ofs in * by omega. auto.
           intros ->. auto.
    (* permission *)
    + intros b ofs k perm Hp.
      destruct (module_var_dec se p b ofs) as [Hmv | Hmv].
      * right. apply Hx. auto.
      * exploit Mem.unchanged_on_perm. apply H. apply Hmv.
        unfold Mem.valid_block. rewrite Hnext.
        eapply Mem.perm_valid_block. apply Hp.
        intros Hp'. rewrite <- Hp' in Hp.
        eapply Mem.mext_perm_inv; eauto.
  - eapply Mem.unchanged_on_refl.
  - auto.
Qed.

Lemma list_inj f xs ys:
  list_rel (Val.inject f) xs ys ->
  Val.inject_list f xs ys.
Proof.
  induction 1; try constructor; auto.
Qed.

Lemma sepc_cont_match_le p w w' k1 k2:
  cont_match (sepc p) w k1 k2 ->
  cont_match (sepc p) w' k1 k2.
Proof.
  induction 1; try constructor; auto.
Qed.

Lemma state_match_mem_unchanged p se m Hvb s1 s2:
  state_match (sepc p) (sepcw p se m Hvb) s1 s2 ->
  Mem.unchanged_on (module_var (globalenv se p)) m (get_mem s2).
Proof.
  inversion 1; subst; cbn in *.
  - inv H3. auto.
  - inv H3. auto.
  - inv H2. auto.
Qed.

Lemma state_match_mem_nextblock p w s1 s2:
  state_match (sepc p) w s1 s2 ->
  Mem.nextblock (get_mem s1) = Mem.nextblock (get_mem s2).
Proof.
  inversion 1; subst; cbn in *.
  - inv H3. apply H4.
  - inv H3. apply H4.
  - inv H2. apply H3.
Qed.

Lemma unchanged_on_sym P m1 m2:
  Mem.unchanged_on P m1 m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  Mem.unchanged_on P m2 m1.
Proof.
  intros Hinv Hnxt. constructor.
  - destruct Hinv. congruence.
  - intros. symmetry. apply Hinv; auto.
    unfold Mem.valid_block in *. congruence.
  - intros. symmetry. apply Hinv; auto.
    rewrite Mem.unchanged_on_perm; eauto.
    unfold Mem.valid_block. rewrite Hnxt.
    eapply Mem.perm_valid_block. eauto.
Qed.

Section SIM.
  Context {p: Clight.program} {Σ: Genv.symtbl -> !li_d --o !li_d} (ps: prog_sim p Σ).
  Variable C: Clight.program.
  Context {sk: AST.program unit unit} (Hlk: link (skel (semantics1 C)) (skel (semantics1 p)) = Some sk).
  Definition sem_abs: semantics li_d li_c := Abs.c_semantics sk C Σ.
  Definition sem_impl: semantics li_d li_c := Impl.c_semantics sk C p.

  (* It's not possible to infer the outgoing interface so we define the following notations *)
  Notation " 'st1' " := (@Abs.st li_d li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'st2' " := (@Impl.st li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'ext1' " := (@Abs.ext li_d li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'ext2' " := (@Impl.ext li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'state1' " := (@Abs.state li_d li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Notation " 'state2' " := (@Impl.state li_d li_c li_c (semantics1 C)) (at level 1) : sim_scope.
  Open Scope sim_scope.

  Variable se: Genv.symtbl.
  Let sepv := sepc p.

  Inductive comp_state_match:  world sepv -> state1 -> state2 -> Prop :=
  | st_match: forall (s1 s2: state) σ1 se m Hvb,
      state_match sepv (sepcw p se m Hvb) s1 s2 ->  ps σ1 m ->
      comp_state_match (sepcw p se m Hvb) (st1 s1 σ1) (st2 s2)
  | ext_match: forall (s1 s2: state) σ1 t1 t2 se m Hvb,
      state_match sepv (sepcw p se m Hvb) s1 s2 ->
      t1 = t2 -> ps σ1 m ->
      comp_state_match (sepcw p se m Hvb) (ext1 s1 t1 σ1) (ext2 s2 t2).

  Inductive cc_query: (world sepv) -> query li_c -> query li_c -> Prop :=
  | cc_query_intro: forall se m Hvb q1 q2,
      match_query (cc_c sepv) (sepcw p se m Hvb) q1 q2 ->
      (init_mem _ _  ps) m ->
      cc_query (sepcw p se m Hvb) q1 q2.

  Program Definition sepcc :=
    {|
    ccworld := ccworld (cc_c sepv);
    match_senv := match_senv (cc_c sepv);
    match_query := cc_query;
    match_reply _ r1 r2 := exists w, (cc_c_reply sepv) w r1 r2;
    |}.
  Next Obligation.
    inv H. auto.
  Qed.
  Next Obligation.
    inv H. auto.
  Qed.

  Theorem fsim_abs_impl:
    forward_simulation cc_id sepcc sem_abs sem_impl.
  Proof.
    constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. cbn -[sem_abs sem_impl semantics1] in *.
    inv Hse. clear se. rename se2 into se.
    eapply link_linkorder in Hlk as [HseC Hsep].
    eapply Genv.valid_for_linkorder in HseC; eauto.
    eapply Genv.valid_for_linkorder in Hsep; eauto.
    pose (ms := fun s1 s2 => exists w, comp_state_match w s1 s2 /\ match_stbls sepv w se se).
    apply forward_simulation_step with (match_states := ms).
    - intros ? ? Hq. inv Hq. inv H1.
      cbn. eapply Genv.is_internal_match; eauto.
      + instantiate (1 := p).
        repeat apply conj; auto.
        induction (AST.prog_defs (_ C)) as [ | [id [f|v]] defs IHdefs];
          repeat (econstructor; eauto).
        * apply incl_refl.
        * apply linkorder_refl.
        * instantiate (1 := fun _ => eq). reflexivity.
        * instantiate (1 := eq). destruct v; constructor; auto.
      + eapply match_stbls_proj; eauto. constructor.
      + cbn. congruence.
    - intros q1 q2 s1 Hq Hs1. inv Hq. inv H1. inv Hs1. inv H1.
      set (w := sepcw p se m Hvb0).
      assert (Hge: genv_match C sepv w (globalenv se C) (globalenv se C)).
      {
        eapply (rel_push_rintro (fun se=> globalenv se C) (fun se=> globalenv se C)).
        constructor.
      }
      transport_hyps.
      exists (st2 (Callstate vf2 vargs2 Kstop m2)). split.
      + constructor. econstructor; eauto.
        * revert vargs2 H0. clear -H12.
          induction H12; inversion 1; subst; constructor; eauto.
          eapply val_casted_inject; eauto.
        * eapply match_stbls_nextblock; eauto.
          constructor.
      + exists w. split; try constructor.
        * constructor; eauto.
          -- clear -H0. induction H0; constructor; eauto.
          -- constructor.
        * apply correct_cond; eauto.
    - intros s1 s2 r1 (w & Hs & Hge) H. inv H. inv Hs. inv H0. inv H3.
      eexists. split.
      + constructor. inv H6.
        constructor.
      + eexists. constructor; eauto.
    - intros s1 s2 qx1 (w & Hs & Hge) Hq1.
      inv Hq1. inv Hs. eexists tt, _.
      repeat apply conj; try constructor.
      intros r1 r2 s1' Hr1 Hs1'. inv Hr1. inv Hs1'.
      eexists. split.
      + constructor.
      + econstructor. split; try econstructor; eauto. constructor; eauto.
    - intros s1 t s1' Hstep s2 (w & Hs & Hge). inv Hstep.
      + inv Hs. inv Hge. set (w := sepcw p se m0 Hvb) in *.
        assert (Hge': genv_match C sepv w (globalenv se C) (globalenv se C)).
        {
          eapply (rel_push_rintro (fun se=> globalenv se C) (fun se=> globalenv se C)).
          subst w. constructor.
        }
        eapply step_rel in H; eauto.
        2: { repeat rstep. }
        destruct H as (s2' & Hstep' & Hs2').
        exists (st2 s2'). split.
        * constructor. apply Hstep'.
        * destruct Hs2' as (w' & Hw' & Hs2').
          inv Hw'. eexists (sepcw  _ _ _ _). split; constructor; eauto.
      + cbn in *. inv Hs. rename s' into s1. rename s0 into s'.
        inv Hge. set (w := sepcw p se m0 Hvb) in *.
        assert (Hsim: exists q', at_external (globalenv se C) s' q' /\ match_query (cc_c sepv) w qb q').
        {
          inv H. inv H6.
          assert (vf <> Vundef). destruct vf; cbn in *; try congruence.
          assert (genv_match C sepv w (globalenv se C) (globalenv se C)).
          eapply (rel_push_rintro (fun se=> globalenv se C) (fun se=> globalenv se C)).
          subst w; constructor.
          transport_hyps.
          eexists. split.
          - econstructor. eauto.
          - inv H2. constructor; auto.
            clear -H12. induction H12; constructor; auto.
        }
        destruct Hsim as (q' & Hsim & Hq). inversion Hq.
        assert (q_rel' qa q' m2).
        {
          inv H2. inv H15.
          replace vf1 with vf2.
          2: { cbn in H3. rewrite val_inject_id in H3. inv H3; try congruence. }
          constructor. clear -H4. induction H4; constructor; auto.
          cbn in H. rewrite val_inject_id in H. auto.
        }
        eapply mem_scope with (m' := m2) in H8; eauto.
        2: { inv H5. auto. }
        edestruct simulation as (m' & impl & Hmem & Hnext & Hs'); eauto.
        assert (Hvb': forall b ofs, module_var (globalenv se p) b ofs -> Mem.valid_block m' b).
        {
          intros b ofs Hb. eapply Hm2 in Hb. inv H5.
          eapply Mem.valid_block_unchanged_on; eauto.
          eapply Mem.valid_block_unchanged_on; eauto.
        }
        assert (Hsim': exists s1', after_external s' (r_with_mem ra m') s1' /\ state_match sepv (sepcw p se m' Hvb') s1 s1').
        {
          inv H2. unfold r_with_mem. inv H16. inv Hsim. inv H0. inv H6.
          eexists _. split.
          - econstructor.
          - econstructor. apply val_inject_refl.
            eapply sepc_cont_match_le. eauto. cbn in *.
            eapply mem_match_sim; eauto.
        }
        destruct Hsim' as (s1' & H' & Hs1').
        exists (ext2 s1' w0). split.
        * eapply Impl.step_at_external; eauto.
        * eexists. split. constructor; eauto.
          constructor.
      + inv Hs.
        exists (st2 s0). split.
        * constructor.
        * eexists. split; eauto. constructor; auto.
    - apply well_founded_ltof.
    Qed.
    Close Scope sim_scope.
  End SIM.
