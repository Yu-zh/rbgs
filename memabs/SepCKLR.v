Require Import Relations RelationClasses.
Require Import List.
Require Import Events Values Memory.
Require Import CKLR Extends.

Section SepCKLR.
  Variable vars: block -> Z -> Prop.
  (* the target memory and local variables that belong to the component
     constitute the klr index *)
  Inductive sep_world :=
    sepw (m: mem) (Hvb: forall b ofs, vars b ofs -> Mem.valid_block m b).
  Inductive sep_acc: relation sep_world :=
    acc_intro m1 m2 Hm1 Hm2:
      (* External call into the component only touches its own variables  *)
      Mem.unchanged_on (fun b ofs => ~ vars b ofs) m1 m2 ->
      sep_acc (sepw m1 Hm1) (sepw m2 Hm2).

  Inductive sep_mm: sep_world -> mem -> mem -> Prop :=
    match_intro: forall m m1 m2 Hvb,
      (* source memory extends into target memory *)
      Mem.extends m1 m2 ->
      (* local variables of the component are only modified during external
         calls so they don't change in the course of internal steps*)
      Mem.unchanged_on vars m m2 ->
      (* m1 and locals don't have blocks in common *)
      (forall b ofs, vars b ofs -> ~ Mem.perm m1 b ofs Max Nonempty) ->
      sep_mm (sepw m Hvb) m1 m2.

  Instance sep_acc_preo:
    PreOrder sep_acc.
  Proof.
    split.
    - intros [m]. constructor.
      apply Mem.unchanged_on_refl.
    - intros [m1] [m2] [m3].
      inversion 1. subst.
      inversion 1. subst.
      constructor.
      eapply Mem.unchanged_on_trans; eauto.
  Qed.

  Program Definition sep: cklr :=
    {|
    world := sep_world;
    wacc := sep_acc;
    mi w := inject_id;
    match_mem w := sep_mm w;
    match_stbls w := eq;
    |}.
  (* mi_acc *)
  Next Obligation.
    repeat rstep. apply inject_incr_refl.
  Qed.
  (* match_stbls_acc *)
  Next Obligation.
    rauto.
  Qed.
  (* match_stbls_proj *)
  Next Obligation.
    intros ? ? ->. apply Genv.match_stbls_id.
  Qed.
  (* match_stbls_nextblock *)
  Next Obligation.
    inv H0. erewrite <- Mem.mext_next; eauto.
  Qed.
  (* cklr_alloc *)
  Next Obligation.
    intros [ ] m1 m2 Hm lo hi. inv Hm.
    destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn: Hm1.
    edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
    rewrite Hm2'.
    eexists (sepw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
    - intros. specialize (Hvb _ _ H).
      specialize (H2 _ _ H). intros Hp. apply H2.
      eapply Mem.perm_alloc_4 in Hp; eauto.
      eapply Mem.alloc_result in Hm1. subst.
      exploit Mem.valid_block_unchanged_on; eauto.
      erewrite Mem.mext_next; eauto. apply Plt_ne.
  Qed.
  (* cklr_free *)
  Next Obligation.
    intros [ ] m1 m2 Hm [[b lo] hi] r2 Hr. inv Hm.
    apply coreflexivity in Hr. subst. simpl. red.
    destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. constructor.
    eexists (sepw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.free_unchanged_on; eauto.
      intros ofs Hofs Hv. specialize (H2 _ _ Hv). apply H2.
      exploit Mem.free_range_perm. apply Hm1'. eauto.
      intros Hp. eapply Mem.perm_cur_max.
      eapply Mem.perm_implies. apply Hp. constructor.
    - intros. specialize (H2 _ _ H).
      intros Hp. apply H2.
      eapply Mem.perm_free_3; eauto.
  Qed.
  (* cklr_load *)
  Next Obligation.
    intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp. inv Hm.
    apply coreflexivity in Hp; subst. simpl. red.
    destruct (Mem.load chunk m1 b ofs) as [v1|] eqn:Hv1; [|constructor].
    edestruct Mem.load_extends as (v2 & Hv2 & Hv); eauto.
    rewrite Hv2. rewrite val_inject_lessdef_eqrel. rauto.
  Qed.
  (* cklr_store *)
  Next Obligation.
    intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp v1 v2 Hv. inv Hm.
    apply coreflexivity in Hp; subst. simpl. red.
    destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
    apply val_inject_lessdef in Hv.
    edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. constructor.
    eexists (sepw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.store_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H2 _ _ Hp). apply H2.
      exploit Mem.store_valid_access_3. apply Hm1'.
      unfold Mem.valid_access. intros [Hpr ?]. specialize (Hpr _ Hofs).
      eapply Mem.perm_cur_max. eapply Mem.perm_implies. apply Hpr. constructor.
    - intros. specialize (H2 _ _ H).
      intros Hp. apply H2.
      eapply Mem.perm_store_2; eauto.
  Qed.
  (* cklr_loadbytes *)
  Next Obligation.
    intros [ ] m1 m2 Hm [b ofs] p2 Hp sz. inv Hm.
    apply coreflexivity in Hp; subst. simpl. red.
    destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
    edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
    rewrite Hv2. rauto.
  Qed.
  (* cklr_storebytes *)
  Next Obligation.
    intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp vs1 vs2 Hv. inv Hm.
    apply coreflexivity in Hp. subst. simpl. red.
    destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
    edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
    eapply list_rel_forall2. apply Hv.
    rewrite Hm2'. constructor.
    eexists (sepw m _); split; repeat rstep.
    constructor; auto.
    - eapply Mem.unchanged_on_trans; eauto.
      eapply Mem.storebytes_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H2 _ _ Hp). apply H2.
      exploit Mem.storebytes_range_perm. apply Hm1'.
      rewrite length_rel; eauto. intros.
      eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
    - intros. specialize (H2 _ _ H).
      intros Hp. apply H2.
      eapply Mem.perm_storebytes_2; eauto.
  Qed.
  (* cklr_perm *)
  Next Obligation.
    intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp p k H. inv Hm.
    apply coreflexivity in Hp. subst. simpl in *.
    eapply Mem.perm_extends; eauto.
  Qed.
  (* cklr_valid_block *)
  Next Obligation.
    intros [ ] m1 m2 Hm b1 b2 Hb. inv Hm.
    apply coreflexivity in Hb. subst.
    apply Mem.valid_block_extends; eauto.
  Qed.
  (* cklr_no_overlap *)
  Next Obligation.
    intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 Hb Hb1' Hb2' Hp1 Hp2.
    inv Hb1'. inv Hb2'. eauto.
  Qed.
  (* cklr_representable *)
  Next Obligation.
    xomega.
  Qed.
  (* cklr_aligned_area_inject *)
  Next Obligation.
    rewrite Z.add_0_r. assumption.
  Qed.
  (* cklr_disjoint_or_equal_inject *)
  Next Obligation.
    intuition xomega.
  Qed.
End SepCKLR.
