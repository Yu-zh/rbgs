Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs Values Memory AST Errors Smallstep.
Require Import Clight Ctypes Cop.
Require Import CKLR.
Require Import Coherence CompCertSem Bigstep.

Definition sem_coherence {liA liB} (L: semantics liA liB) :=
  forall se t1 e1 t2 e2,
    lts_lmaps (L se) t1 e1 ->
    lts_lmaps (L se) t2 e2 ->
    @coh (!liA --o liB) (t1, e1) (t2, e2).

Lemma determ_coh {liA liB} (L: semantics liA liB):
  determinate L -> sem_coherence L.
Proof.
  intros HL.
  intros se eas [qb rb] eas' [qb' rb'] lmap lmap' coheas. cbn.
  split.
  - split; auto.
    intros <-.
    inversion lmap as [? ? ? ? valid_q init_q transition_q]. subst.
    inversion lmap' as [? ? ? ? valid_q' init_q' transition_q']. subst.
    determ_solve (sd_initial_determ (HL se)).
    exploit @trace_determ. exact HL.
    exact coheas. exact transition_q. exact transition_q'.
    intuition.
  - intros h. inv h.
    inversion lmap as [? ? ? ? valid_q init_q transition_q]. subst.
    inversion lmap' as [? ? ? ? valid_q' init_q' transition_q']. subst.
    determ_solve (sd_initial_determ (HL se)).
    exploit @trace_determ. exact HL.
    exact coheas. exact transition_q. exact transition_q'.
    intuition.
Qed.

(* A semantics embedding with deterministic condition relaxed *)
Section SEMANTICS.
  Context {liA liB} (L : semantics liA liB) (HL : sem_coherence L).
  Program Definition compcerto_lmap' se : !liA --o liB :=
    {|
    has '(t, u) := lts_lmaps (L se) t u;
    |}.
  Next Obligation.
    intros Hcoh. exploit HL. apply H. apply H0. apply Hcoh.
    now cbn.
  Qed.
End SEMANTICS.

(* A coh semantics with valid_query predicate; eventually the semantics should
   also include a predicate to make sure outgoing calls are in scope *)
Record coh_semantics (liA liB: language_interface): Type :=
  {
  vq: query liB -> bool;            (* valid_query *)
  lf:> !liA --o liB;            (* linear func *)
  Hvq: forall t q r, has lf (t, (q, r)) -> vq q = true;
  }.
Record coh_refinement' {liA liB1 liB2} (ccB: callconv liB1 liB2) (wB: ccworld ccB)
       (Σ1: coh_semantics liA liB1) (Σ2: coh_semantics liA liB2) : Prop :=
  {
  coh_vq_ref: forall q1 q2, match_query ccB wB q1 q2 -> vq _ _ Σ1 q1 = vq _ _ Σ2 q2;
  coh_lf_ref: forall q1 q2 r1 t, has Σ1 (t, (q1, r1)) ->
                            match_query ccB wB q1 q2 ->
                            exists r2, has Σ2 (t, (q2, r2)) /\
                                  match_reply ccB wB r1 r2;
  }.
Definition coh_refinement {liA liB1 liB2: language_interface}
           (ccB: callconv liB1 liB2)
           (Σ1: Genv.symtbl -> coh_semantics liA liB1)
           (Σ2: Genv.symtbl -> coh_semantics liA liB2) sk : Prop :=
  forall se1 se2 wB,
    match_senv ccB wB se1 se2 ->
    Genv.valid_for sk se1 ->
    coh_refinement' ccB wB (Σ1 se1) (Σ2 se2).

Section COH_UNSEM.
  Context {liA liB : language_interface} (Σ : coh_semantics liA liB).
  Definition coh_lts : lts liA liB UnSem.state :=
    {|
    Smallstep.step _ := UnSem.step;
    Smallstep.valid_query q := vq _ _ Σ q;
    Smallstep.initial_state := UnSem.initial_state Σ;
    Smallstep.at_external := UnSem.at_external;
    Smallstep.after_external := UnSem.after_external;
    Smallstep.final_state := UnSem.final_state;
    Smallstep.globalenv := tt;
    |}.
End COH_UNSEM.
(* Anti-embedding coh semantics into lts *)
Definition coh_unsem {liA liB : language_interface} skel
           (Σ : _ -> coh_semantics liA liB) :=
  {|
  Smallstep.skel := skel;
  Smallstep.activate se := coh_lts (Σ se);
  |}.
(* Embedding lts semantics into coh *)
Program Definition lts_sem {liA liB: language_interface}
        (L: semantics liA liB) (HL: sem_coherence L) se: coh_semantics liA liB :=
  {|
  vq := valid_query (L se);
  lf := compcerto_lmap' L HL se;
  |}.
Next Obligation.
  intros. now inv H.
Qed.

(* The Galois Connection with calling conventions on incoming queries and
   replies. The proof hasn't been figured out. 1. sem_coherence is too weak;
   2. match_states should take the cc into consideration *)
Section GC_CC.
  Context {liA liB : language_interface}.
  Context (Σ : Genv.symtbl -> coh_semantics liA liB).
  Context (L : semantics liA liB) (HL : sem_coherence L).

  Inductive match_states se : nat -> UnSem.state -> Smallstep.state L -> Prop :=
    match_states_intro (b : bool) (σ : UnSem.trace_set) (s : Smallstep.state L) :
      (forall t r, has σ (t, r) -> lts_trace (L se) b s t r) ->
      match_states se (Nat.b2n b) (b, σ) s.

  Definition measure : (@UnSem.state liA liB) -> nat :=
    fun '(b, _) => if b then 1%nat else 0%nat.

  Let sk := skel L.
  Lemma sem_unsem_gc cc:
    coh_refinement cc Σ (lts_sem L HL) sk <->
    forward_simulation cc_id cc (coh_unsem sk Σ) L.
  Proof.
  Admitted.
End GC_CC.

(* A simplified version of GC without calling convertions and deterministic
   condition is assumed *)
Section GC.
End GC.

(* A language interface without memory involved *)
Record d_query :=
  dq { dq_vf: val;
       dq_sg: signature;
       dq_args: list val; }.
Record d_reply :=
  dr { dr_retval: val; }.
Canonical Structure li_d :=
  {| query := d_query;
     reply := d_reply;
     entry := dq_vf; |}.
(* A relation that allows arguments in C language interface to be more
   defined than those in abstract language interface *)
Inductive q_rel': query li_d -> query li_c -> mem -> Prop:=
| q_rel'_intro:
    forall vf sg args args' m,
      list_rel Val.lessdef args args' ->
      q_rel' ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|})
             ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args';cq_mem:=m|}) m.
Definition r_with_mem (r: reply li_d) m: reply li_c :=
  match r with
    {|dr_retval:=ret|} => ({|cr_retval:=ret;cr_mem:=m|})
  end.
Definition q_with_mem (q: query li_d) m: query li_c :=
  match q with
    {|dq_vf:=vf;dq_sg:=sg;dq_args:=args|} =>
    {|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|}
  end.
Inductive vals_defined: list val -> Prop :=
| vals_defined_nil: vals_defined nil
| vals_defined_cons: forall v vs,
    v <> Vundef -> vals_defined vs ->
    vals_defined (v::vs).
Definition query_defined (q: query li_d): Prop :=
  match q with
    {|dq_vf:=_;dq_sg:=_;dq_args:=args|} => vals_defined args
  end.
Lemma defined_query_with_mem q q' m:
  query_defined q -> q_rel' q q' m ->
  q' = q_with_mem q m.
Proof.
  intros. inv H0. cbn in *.
  f_equal. symmetry. revert args' H1.
  induction H.
  intros. inv H1. auto. intros. inv H1. f_equal.
  inv H4; easy. apply IHvals_defined. auto.
Qed.
(* Inductive q_rel: query li_d -> query li_c -> mem -> Prop:= *)
(* | q_rel_intro: *)
(*     forall vf sg args m, *)
(*       q_rel ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|}) *)
(*             ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|}) m. *)
(* Inductive r_rel: reply li_d -> reply li_c -> mem -> Prop:= *)
(*   r_rel_intro: *)
(*     forall ret m, *)
(*       r_rel ({|dr_retval:=ret|}) *)
(*             ({|cr_retval:=ret;cr_mem:=m|}) m. *)
(* Inductive qr_rel_list: list (query li_d * reply li_d) -> list (query li_c * reply li_c) -> Prop:= *)
(* | qr_rel_nil: qr_rel_list nil nil *)
(* | qr_rel_cons: *)
(*     forall dq dr cq cr ds cs m m', *)
(*       q_rel dq cq m -> *)
(*       r_rel dr cr m' -> *)
(*       qr_rel_list ds cs -> *)
(*       qr_rel_list ((dq, dr)::ds) ((cq, cr)::cs). *)
Inductive li_rel: token li_d -> token li_c -> Prop:=
| rel_intro:
    forall vf sg args ret m,
      li_rel ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|},
              {|dr_retval:=ret|})
             ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|},
              {|cr_retval:=ret;cr_mem:=m|}).

Program Definition li_dc: li_d --o li_c :=
  {|
  has '(d, c) := li_rel d c
  |}.
Next Obligation.
  destruct d1 as [dq1 dr1]. destruct d2 as [dq2 dr2].
  destruct c1 as [cq1 cr1]. destruct c2 as [cq2 cr2].
  intuition.
  - inv H. inv H0. f_equal. exploit H3. f_equal. inversion 1. auto.
  - inv H. inv H0. inv H1. auto.
Defined.

Inductive exec {liA liB: language_interface} (σ: !liA --o !liB): query liB -> list (token liA) -> reply liB -> Prop:=
| exec_intro: forall t q r,
    has σ (t, (q, r) :: nil) ->
    exec σ q t r.

Program Definition next {liA liB: language_interface} (σ : !liA --o !liB) w qx rx : !liA --o !liB :=
  {|
  has '(s, t) := has σ (w ++ s, (qx, rx)::t);
  |}.
Next Obligation.
  pose proof (has_coh _ _ _ _ H H0). cbn in H1. clear H H0.
  intros Ht. edestruct H1 as [Hr Hl].
  apply (@app_coh liA). apply Ht.
  split. inversion Hr. subst. apply H5. auto.
  intro. exploit Hl. f_equal. auto. apply app_inv_head.
Qed.
(* This module aims to define C @ Σ, where C is a Clight program and Σ is an
   underlay specification within coherent spaces. The composed transition system
   behaves like C with external calls interpreted by Σ. We first define a
   general version L @ Σ for arbitrary transition system L and later refine it
   to C semantics *)
Module Abs.
  Section ABS_SEMANTICS.
    (* the linked system has type liA ->> liD *)
    Context {liA liB liC liD: language_interface}
            (Σ: Genv.symtbl -> !liA --o !liB) (L: semantics liC liD).
    Variable li_rel: token liB -> token liC -> Prop.
    Variable se: Genv.symtbl.

    Variant state : Type :=
    | st (s: Smallstep.state L) (σ: !liA --o !liB)
    (* s and σ constitute the state after the external call *)
    | ext (s: Smallstep.state L) (t: list (token liA)) (σ: !liA --o !liB).

    Inductive step: state -> trace -> state -> Prop :=
    | step_internal: forall s s' t σ,
        Step (L se) s t s' ->
        step (st s σ) t (st s' σ)
    | step_at_external: forall s s' qa ra qb rb σ w,
        (* Upon an external query, the memory is dropped from the query. The
           system proceeds with the same memory for whatever reply from Σ *)
        Smallstep.at_external (L se) s qb ->
        Smallstep.after_external (L se) s rb s' ->
        (* [exec σ q w r] introduces non-determinism *)
        exec σ qa w ra ->
        li_rel (qa, ra) (qb, rb) ->
        step (st s σ) E0 (ext s' w (next σ w qa ra))
    | step_after_external: forall s σ,
        step (ext s nil σ) E0 (st s σ).

    Inductive initial_state: query liD -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (L se) q s ->
        initial_state q (st s (Σ se)).

    Inductive at_external: state -> query liA -> Prop :=
    | ext_at_external: forall s q r t σ,
        at_external (ext s ((q, r) :: t) σ) q.
    Inductive after_external: state -> reply liA -> state -> Prop :=
    | ext_after_external: forall s q r t σ,
        after_external (ext s ((q, r) :: t) σ) r (ext s t σ).

    Inductive final_state: state -> reply liD -> Prop :=
    | final_state_intro: forall s r σ,
        Smallstep.final_state (L se) s r ->
        final_state (st s σ) r.

    Definition lts : lts liA liD state :=
      {|
      Smallstep.step _ := step;
      Smallstep.valid_query := Smallstep.valid_query (L se);
      Smallstep.initial_state := initial_state;
      Smallstep.at_external := at_external;
      Smallstep.after_external := after_external;
      Smallstep.final_state := final_state;
      Smallstep.globalenv := Smallstep.globalenv (L se);
      |}.
  End ABS_SEMANTICS.
  Definition semantics {liA liB liC liD: language_interface}
             skel li_rel (Σ: Genv.symtbl -> !liA --o !liB)
             (L: Smallstep.semantics liC liD) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts Σ L li_rel se;
    |}.
  Definition c_semantics sk (C: Clight.program)
             (Σ: Genv.symtbl -> !li_d --o !li_d): Smallstep.semantics li_d li_c :=
    semantics sk li_rel Σ (semantics1 C).
End Abs.

(* 〚L @ Σ〛 Embedding of a mixed semantics into coherent spaces *)
Section ABS_EMBED.
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

  (* L determ + Σ coherence = L @ Σ coherence *)
  Let LΣ := Abs.semantics (skel L) li_rel Σ L.
  Lemma LΣ_coh: sem_coherence LΣ.
  Proof.
    intros se bot_tr' [q' r'] bot_tr [q r] H H0. cbn.
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

  Program Definition mix_sem se: coh_semantics liA liD :=
    {|
    vq := valid_query (L se);
    lf := compcerto_lmap' LΣ LΣ_coh se;
    |}.
  Next Obligation.
    inv H. apply H2.
  Qed.
End ABS_EMBED.
Lemma determ_li_dc: li_rel_determ li_rel.
Proof.
  unfold li_rel_determ.
  intros. inv H. inv H0.
  split. auto. intros. inv H. auto.
Qed.
Definition c_mix_sem p (Σ : Genv.symtbl -> !li_d --o !li_d) se :=
  mix_sem Σ (semantics1 p) (clight_determinate p)
          li_rel determ_li_dc se.

(* This module aims to define C ⊕ p, where C and p are both Clight program. The
   composition in not commutative in the sense that the only interactive between
   C and p is C make calls defined within the scope p. We first define L ⊕ σ,
   where L is arbitrary transition system and σ can be thought as a form of
   big-step semantics, which will be instantiated to C big-step semantics *)
Module Impl.
  Section IMPL_SEMANTICS.
    Context {liA liB liC: language_interface}
            (σ: Genv.symtbl -> !liA --o liB) (L: semantics liB liC).
    Variable se: Genv.symtbl.

    Variant state :=
    | st (s: Smallstep.state L)
    | ext (s: Smallstep.state L) (t: list (token liA)).

    Inductive step: state -> trace -> state -> Prop :=
    | step_internal: forall s s' t,
        Step (L se) s t s' ->
        step (st s) t (st s')
    | step_at_external: forall s s' q r t,
        Smallstep.at_external (L se) s q ->
        Smallstep.after_external (L se) s r s' ->
        has (σ se) (t, (q, r)) ->
        step (st s) E0 (ext s' t)
    | step_after_external: forall s,
        step (ext s nil) E0 (st s).

    Inductive initial_state: query liC -> state -> Prop :=
    | initial_state_intro: forall q s,
        Smallstep.initial_state (L se) q s ->
        initial_state q (st s).

    Inductive at_external: state -> query liA -> Prop :=
    | ext_at_external: forall s q r t,
        at_external (ext s ((q, r) :: t)) q.
    Inductive after_external: state -> reply liA -> state -> Prop :=
    | ext_after_external: forall s q r t,
        after_external (ext s ((q, r) :: t)) r (ext s t).

    Inductive final_state: state -> reply liC -> Prop :=
    | final_state_intro: forall s r,
        Smallstep.final_state (L se) s r ->
        final_state (st s) r.

    Definition lts : lts liA liC state :=
      {|
      Smallstep.step _ := step;
      Smallstep.valid_query := Smallstep.valid_query (L se);
      Smallstep.initial_state := initial_state;
      Smallstep.at_external := at_external;
      Smallstep.after_external := after_external;
      Smallstep.final_state := final_state;
      Smallstep.globalenv := Smallstep.globalenv (L se);
      |}.
  End IMPL_SEMANTICS.
  Definition semantics {liA liB liC: language_interface}
             skel (σ: Genv.symtbl -> !liA --o liB)
             (L: Smallstep.semantics liB liC) :=
    {|
    Smallstep.skel := skel;
    Smallstep.activate se := lts σ L se;
    |}.
  Definition c_semantics sk (C: Clight.program) (p: Clight.program):
    Smallstep.semantics li_d li_c :=
    semantics sk (fun se => clight_bigstep p se @ !li_dc) (semantics1 C).
End Impl.

(* 〚C ⊕ p〛Embedding of the composed semantics *)
Section IMPL_EMBED.

  Context {liA liB liC: language_interface}
          (σ: Genv.symtbl -> !liA --o liB) (L: semantics liB liC)
          (HL: determinate L).

  Lemma star_ext_state' se s w ws t s':
    Star (Impl.lts σ L se) (Impl.ext L s (w :: ws)) t s' ->
    s' = @Impl.ext _ liB liC L s (w :: ws).
  Proof.
    intros Hstar.
    inv Hstar. reflexivity. inv H.
  Qed.

  Lemma trace_prefix' se s w t r:
    lts_trace (Impl.lts σ L se) false (Impl.ext L s w) t r ->
    exists t', t = w ++ t'.
  Proof.
    revert t. induction w.
    - intros. eexists. reflexivity.
    - intros t Hlts.
      inv Hlts. inv H. inv H. inv H0.
      inv H1. destruct w.
      + eexists. cbn. reflexivity.
      + eapply star_ext_state' in H.
        subst. exploit IHw. eauto.
        intros [? ?]. eexists.
        rewrite <- app_comm_cons. f_equal. eauto.
  Qed.

  Let Lσ := Impl.semantics (skel L) σ L.
  Lemma Lσ_coh: sem_coherence Lσ.
  Proof.
    intros se bot_tr' [q' r'] bot_tr [q r] H H0. cbn.
    intros Hcoh. assert (q' = q -> r' = r /\ bot_tr' = bot_tr).
    {
      intros ->. inv H. inv H0. inv H5. inv H7.
      exploit (sd_initial_determ (HL se)). apply H. apply H0.
      intros ->. clear H H0 H2 H3.
      revert bot_tr Hcoh H8. induction H6.
      - intros tr Hcoh Hlts.
        inv Hlts. apply IHlts_trace. auto.
        replace s' with s'0. auto.
        clear - Hcoh HL H H0 H1 H6. revert s'0 H0 H1.
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
               ** exploit (sd_determ (HL se)). apply H1. apply H2.
                  exploit (sd_traces (HL se)). apply H1.
                  exploit (sd_traces (HL se)). apply H2. intros l1 l2.
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
               ** exploit (sd_at_external_determ (HL se)). apply H1. apply H9.
                  intros <-.
                  destruct t0; destruct t1.
               ++ pose proof (has_coh _ _ _ _ H8 H11).
                  cbn in H. exploit H. constructor.
                  intros [Hl Hqr]. exploit (proj2 Hl). auto. intros <-.
                  exploit (sd_after_external_determ (HL se)). apply H2. apply H10.
                  intros <-. simpl in H7. subst. apply IHstar. auto. auto.
               ++ pose proof (has_coh _ _ _ _ H8 H11).
                  cbn in H. exploit H. constructor.
                  intros [Hl Hqr]. exploit (proj2 Hl). auto. intros <-.
                  exploit Hqr. auto. intros. easy.
               ++ pose proof (has_coh _ _ _ _ H8 H11).
                  cbn in H. exploit H. constructor.
                  intros [Hl Hqr]. exploit (proj2 Hl). auto. intros <-.
                  exploit Hqr. constructor. intros. easy.
               ++ pose proof (has_coh _ _ _ _ H8 H11).
                  cbn in H. exploit H.
                  exploit star_ext_state'. apply H0. intros ->.
                  exploit star_ext_state'. apply H5. intros ->.
                  exploit trace_prefix'. apply H6. intros [? ->].
                  exploit trace_prefix'. apply H3. intros [? ->].
                  eapply prefix_coh. eauto.
                  intros [Hl Hqr]. exploit (proj2 Hl). auto. intros <-.
                  exploit (sd_after_external_determ (HL se)). apply H2. apply H10.
                  intros <-. simpl in H7. subst.
                  exploit Hqr. auto. intros. inv H4.
                  apply IHstar. auto. auto.
            -- inv H4. simpl in H7. subst.
               apply IHstar. auto. auto.
      - intros tr Hcoh Hlts. inv Hcoh.
        + inv H. inv Hlts.
          * inv H. exploit (sd_final_determ (HL se)). apply H0. apply H2. easy.
          * inv H.
        + inv Hlts. inv H. inv H0.
          exploit (sd_final_determ (HL se)). apply H1. apply H2. easy.
      - intros tr Hcoh Hlts.
        inv Hcoh.
        + inv Hlts. inv H1. inv H.
        + destruct b as [q' r'].
          inv Hlts. inv H. inv H7.
          inv H0. inv H9. exploit H5. auto.
          intros Hcoh'.
          exploit IHlts_trace; eauto. intros [<- <-]. easy.
    }
    intuition. apply H1. now injection H2.
  Qed.

  Program Definition hcomp_sem se: coh_semantics liA liC :=
    {|
    vq := valid_query (L se);
    lf := compcerto_lmap' Lσ Lσ_coh se;
    |}.
  Next Obligation.
    inv H. apply H2.
  Qed.
End IMPL_EMBED.
Definition c_hcomp_sem p C se :=
  hcomp_sem (fun se => clight_bigstep p se @ !li_dc)
            (semantics1 C) (clight_determinate C) se.
