Require Import Relations RelationClasses.
Require Import List.
Require Import Integers Coqlib Maps.
Require Import LanguageInterface Events Globalenvs Values Memory Smallstep.
Require Import Clight Ctypes Cop.
Require Import CKLR Clightrel.
Require Import Coherence CompCertSem Bigstep.
Require Import SemDef SepCKLR ProgSim.

Section TRACE_INV.
  (* outside each pair of query and reply *)
  (* cross_event_inv = ⊤ means choice of query *)
  Variable cross_event_inv: mem -> mem -> Prop.
  (* inside each pair of query and reply *)
  (* in_event_inv = ⊤ means choice of reply *)
  Variable in_event_inv: mem -> mem -> Prop.

  Inductive dtrace_inv: mem -> token (!li_d) -> token (!li_c) -> mem -> Prop :=
  | dtrace_inv_nil:
      forall m m'
        (INV: cross_event_inv m m'),
        dtrace_inv m nil nil m'
  | dtrace_inv_cons:
      forall m0 m1 m2 m3 dq dr drest crest
        (INV1: cross_event_inv m0 m1)
        (INV2: in_event_inv m1 m2)
        (REST: dtrace_inv m2 drest crest m3),
        dtrace_inv m0 ((dq, dr) :: drest)
                   ((q_with_mem dq m1, r_with_mem dr m2) :: crest) m3.
  (* This should be a relation like memory extention *)
  Variable mem_inv: mem -> mem -> Prop.

  Inductive ctrace_inv: mem -> token (!li_c) -> token (!li_c) -> mem -> Prop :=
  | ctrace_inv_nil:
      forall m m'
        (INV: cross_event_inv m m'),
        ctrace_inv m nil nil m'
  | ctrace_inv_cons:
      forall m0 m1 q r q' r' rest rest'
        (HM1: mem_inv (cq_mem q) (cq_mem q'))
        (HM2: mem_inv (cr_mem r) (cr_mem r'))
        (INV1: cross_event_inv m0 (cq_mem q'))
        (INV2: in_event_inv (cq_mem q') (cr_mem r'))
        (REST: ctrace_inv (cr_mem r') rest rest' m1),
        ctrace_inv m0 ((q, r) :: rest) ((q', r') :: rest') m1.

End TRACE_INV.

Record prim_sim
       (σ: Genv.symtbl -> !li_c --o li_c)
       (Σ: Genv.symtbl -> !li_d --o !li_d) :=
  {
  (* The sim_rel doesn't allow memory with variables more than necessary. It
  doesn't matter whether an abstract stack is represented as an array with
  counter or two arrays. But it can't contain variables that are used by other
  components *)
  sim_rel :> (!li_d --o !li_d) -> mem -> Prop;
  init_mem : mem -> Prop;
  valid_se : Genv.symtbl -> Prop;
  vars : Genv.symtbl -> block -> Z -> Prop;

  rel_scope : forall m m' s se,
      valid_se se -> Mem.unchanged_on (vars se) m m' ->
      sim_rel s m -> sim_rel s m';
  prim_scope: forall se q r tr,
      valid_se se -> has (σ se) (tr, (q, r)) ->
      Mem.unchanged_on (fun b ofs => ~ vars se b ofs)
                       (cq_mem q) (cr_mem r) /\
      Mem.nextblock (cq_mem q) = Mem.nextblock (cr_mem r);
  prim_inv: forall se q r tr q' r' tr',
      valid_se se -> has (σ se) (tr, (q, r)) ->
      ctrace_inv (Mem.unchanged_on (fun b ofs => ~ vars se b ofs))
                 (* as long as outgoing query won't mess up non-locals *)
                 (fun _ _ => True)
                 (* forall reply *)
                 (Mem.unchanged_on (vars se)) (cq_mem q) tr tr' (cr_mem r') ->
      Mem.unchanged_on (vars se) (cq_mem q) (cq_mem q') ->
      Mem.unchanged_on (vars se) (cr_mem r) (cr_mem r') ->
      has (σ se) (tr', (q', r'));
  simulation: forall s dq dr dt m se,
      valid_se se -> sim_rel s m -> exec s dq dt dr ->
      exists m' ct, has (σ se) (ct, (q_with_mem dq m, r_with_mem dr m')) /\
               dtrace_inv (fun _ _ => True) (* there exists outgoing query *)
                          (Mem.unchanged_on (vars se))
                          (* its reply preserves local vars *)
                          m  dt ct m' /\
               sim_rel (next s dt dq dr) m';
  correct_cond: forall m se,
      valid_se se -> init_mem m -> sim_rel (Σ se) m;
  reactive_spec: forall se s, reachable (Σ se) s -> reactive s;
  }.

Arguments init_mem [_ _].
Arguments valid_se [_ _].
Arguments vars [_ _].

Inductive exec_star {liA liB: language_interface} (σ: !liA --o !liB):
  list (token liA) -> list (token liB) -> (!liA --o !liB) -> Prop:=
| exec_star_empty:
    exec_star σ nil nil σ
| exec_star_step:
    forall q t r σ' σ'' qrs ts
      (EXEC: exec σ q t r)
      (NEXT: σ' = next σ t q r)
      (REST: exec_star σ' ts qrs σ''),
      exec_star σ (t ++ ts) ((q, r) :: qrs) σ''.

Lemma exec_star_intro {liA liB: language_interface} (σ: !liA --o !liB) xs ys:
  has σ (ys, xs) -> (forall s, reachable σ s -> reactive s) ->
  exists σ', exec_star σ ys xs σ'.
Proof.
  intros H Hclose.
  induction xs.
  - exists σ. admit.
  - admit.
Admitted.

Lemma exec_star_elim1 {liA liB: language_interface} (σ σ': !liA --o !liB) aa bb:
  exec_star σ bb aa σ' ->
  forall aa' bb', has σ' (bb', aa') ->
             has σ (bb++bb', aa++aa').
Proof.
  induction 1.
  - trivial.
  - intros. exploit IHexec_star.
    eauto. intros. subst.
    cbn in H1. rewrite app_assoc in H1.
    rewrite app_comm_cons in H1. auto.
Qed.

Lemma exec_star_elim2 {liA liB: language_interface} (σ σ': !liA --o !liB) aa bb:
  exec_star σ bb aa σ' ->
  forall bb' aax, has σ (bb++bb', aax) ->
             exists aa', aax = aa ++ aa' /\
                    has σ' (bb', aa').
Proof.
  induction 1.
  - intros. exists aax. split; auto.
  - intros. subst. cbn in *.
    inv EXEC. assert (exists aax', aax = (q, r) :: aax') as (aax' & ->).
    {
      pose proof (@has_coh _ σ).
      exploit H2. apply H0. apply H1.
      intros Hcoh. cbn in Hcoh. exploit Hcoh.
      rewrite <- app_assoc.
      admit. intros (? & ?). inv H3.
      admit. admit.
    }
    exploit IHexec_star.
    rewrite app_assoc. eauto.
    intros (aa' & -> & ?). exists aa'. split; auto.
Admitted.

Lemma exec_star_next {liA liB liC: language_interface}
      (s1: !liB --o !liA) (s2: !liC --o !liB) bot mid s2' dq dr:
  exec_star s2 bot mid s2' ->
  next (s1 @ s2) bot dq dr = next s1 mid dq dr @ s2'.
Proof.
  intros Hstar. apply lmap_ext. intros cc aa.
  split; intro H.
  - inversion H as (bb & Hcb & Hba). clear H.
    exploit @exec_star_elim2. apply Hstar. apply Hcb.
    intros (aa' & Hbb & Hs2'). subst bb.
    cbn. exists aa'. split; auto.
  - inversion H as (bb & Hcb & Hba). clear H.
    cbn in *. exploit @exec_star_elim1. apply Hstar.
    apply Hcb. intro. exists (mid ++ bb). split; auto.
Qed.

Section TRACE_SIM.
  Context {σ Σ} (psim: prim_sim σ Σ).
  Variable se: Genv.symtbl.

  Let triv_inv := fun (_ _: mem) => True.
  Let local_inv := Mem.unchanged_on (vars psim se).
  Let nonlocal_inv := Mem.unchanged_on (fun b ofs => ~ vars psim se b ofs).
  Lemma simulation_ext: forall s m m' dqrs dtr cqrs s',
      valid_se psim se -> psim s m -> exec_star s dtr dqrs s' ->
      dtrace_inv triv_inv (* forall query *)
                 nonlocal_inv (* reply preserves non-local *)
                 m dqrs cqrs m' ->
      exists mx cqrs' ctr,
        ctrace_inv local_inv (* next query preserves local *)
                   triv_inv (* exists such a reply *)
                   nonlocal_inv
                   m cqrs cqrs' mx /\
        nonlocal_inv m' mx /\
        (* bottom layer trace should preserve both local and non-local vars *)
        dtrace_inv triv_inv local_inv m dtr ctr mx /\
        has (dag_ext (σ se)) (ctr, cqrs') /\
        psim s' mx.
  Proof.
  Admitted.

End TRACE_SIM.

Section VCOMP.
  Context {σ1 Σ1} (psim1: prim_sim σ1 Σ1).
  Context {σ2 Σ2} (psim2: prim_sim σ2 Σ2).

  (* TODO: hypothesis -- exclusive variables *)
  Hypothesis Hunch1: forall se, Mem.unchanged_on (fun b ofs => ~ vars psim2 se b ofs) = Mem.unchanged_on (vars psim1 se).
  Hypothesis Hunch2: forall se, Mem.unchanged_on (fun b ofs => ~ vars psim1 se b ofs) = Mem.unchanged_on (vars psim2 se).

  Let Σ := fun se => (Σ1 se) @ (Σ2 se).
  Let σ := fun se => (σ1 se) @ dag_ext (σ2 se).
  Program Definition vcomp_sim: prim_sim σ Σ :=
    {|
    sim_rel := fun s m => exists s1 s2, psim1 s1 m /\ psim2 s2 m /\ s = s1 @ s2;
    init_mem := fun m => init_mem psim1 m /\ init_mem psim2 m;
    valid_se := fun se => valid_se psim1 se /\ valid_se psim2 se;
    vars := fun se b ofs => vars psim1 se b ofs \/ vars psim2 se b ofs;
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    rename H0 into s1. rename H3 into s2.
    inv H1. destruct H0 as (dmid & Hs2 & Hs1).
    exploit (simulation _ _ psim1); eauto.
    econstructor. apply Hs1.
    intros (m1' & cmid & Hprim1 & Hinv1 & Hrest1).
    exploit @trace_exec_star. apply Hs2.
    admit.
    intros (s2' & Hstar).
    exploit @simulation_ext. apply H2. eauto. eauto.
    rewrite -> Hunch1. apply Hinv1.
    intros (m2' & cmid' & ctr & Hinv2 & Hmx & Htr & Hext & Hrest2).
    exploit (@prim_inv _ _ psim1). apply H. apply Hprim1.
    rewrite -> Hunch1 in Hinv2.
    rewrite -> Hunch2. replace (cq_mem (q_with_mem dq m)) with m.
    2: { unfold q_with_mem. destruct dq. auto. }.
    4: {
      intros Hprim1'.
      exists m2'. exists ctr. split.
      exists cmid'. split. apply Hext. apply Hprim1'.
      split. admit.
      exists (next s1 dmid dq dr). exists s2'.
      split. eapply (rel_scope _ _ psim1). apply H.
      rewrite -> Hunch1 in Hmx. eauto. auto.
      split; auto.
      admit.
    }
    replace (cr_mem (r_with_mem dr m2')) with m2'. auto.
    unfold r_with_mem. destruct dr. auto.




End VCOMP.
