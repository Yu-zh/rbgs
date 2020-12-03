Require Import Relations RelationClasses.
Require Import List.
Require Import compcert.common.LanguageInterface.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import models.Coherence.
Require Import examples.CompCertSem.
Require Import examples.Bigstep.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Memory. (* mem *)
Require Import compcert.common.AST.    (* Gvar *)
Require Import compcert.cfrontend.Ctypes. (* type *)
Require Import compcert.common.Values.    (* block *)
Require Import compcert.lib.Integers.     (* ptrofs *)
Require Import compcert.lib.Coqlib.       (* Z *)
Require Import compcert.lib.Maps.         (* PTree.get *)
Require Import compcert.common.Errors.    (* res *)
Require Import compcert.common.Memory.    (* unchanged_on *)
Require Import compcert.cfrontend.Cop.    (* val_casted_list *)

Section MEM_INJ.
  Variable p: Clight.program.
  Variable se: Genv.symtbl.
  Let ge: genv := globalenv se p.
  Variable w: meminj_thr.

  Inductive match_tr: list (c_query * c_reply) -> list (c_query * c_reply) -> list (ccworld cc_injp) -> Prop:=
  | match_tr_nil:
      match_tr nil nil nil
  | match_tr_cons wx q r q1 r1 rest rest1 rest_wx:
      match_query cc_injp wx q q1 ->
      (match_reply cc_injp wx r r1 -> match_tr rest rest1 rest_wx) ->
      match_tr ((q, r)::rest) ((q1, r1)::rest1) (wx::rest_wx).
  Lemma valid_query_match q q1:
    match_query cc_inj w q q1 ->
    Genv.is_internal ge (entry q) = true ->
    Genv.is_internal ge (entry q1) = true.
  Admitted.
  Lemma initial_state_match vf vf1 vargs vargs1 m m1 f targs:
    Val.inject w vf vf1 ->
    Val.inject_list w vargs vargs1 ->
    Mem.inject w m m1 ->
    Genv.find_funct ge vf = Some (Internal f) ->
    val_casted_list vargs targs ->
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    Genv.find_funct ge vf1 = Some (Internal f) /\
    val_casted_list vargs1 targs /\
    Ple (Genv.genv_next ge) (Mem.nextblock m1).
  Admitted.
  Lemma eval_fun_match m m1 vf vf1 vargs vargs1 m' tr vres:
    Val.inject w vf vf1 ->
    Val.inject_list w vargs vargs1 ->
    Mem.inject w m m1 ->
    eval_funcall ge m vf vargs m' tr vres ->
    exists m'1 tr1 vres1 wx,
      eval_funcall ge m1 vf1 vargs1 m'1 tr1 vres1 /\
      Val.inject w vres vres1 /\
      match_tr tr tr1 wx /\
      Mem.inject w m' m'1.
  Admitted.
  Lemma bigstep_match:
    forall tr q r,
      bigstep_lmaps ge tr (q, r) ->
      forall q',
        match_query cc_inj w q q' ->
        exists tr' r' wx,
          bigstep_lmaps ge tr' (q', r') /\
          match_reply cc_inj w r r' /\
          match_tr tr tr' wx.
  Proof.
    intros tr q r bigstep q' q_match.
    inversion bigstep. subst tr0 q0 r0.
    exploit valid_query_match.
    exact q_match. exact H1. clear H1. intros h1.
    rewrite H2 in q_match. inversion q_match. subst m1 vf1 sg vargs1.
    exploit initial_state_match.
    exact H10. exact H11. exact H12.
    exact H3. clear H3. exact H5. clear H5. exact H6. clear H6.
    intros [h2 [h3 h4]].
    exploit eval_fun_match.
    exact H10. exact H11. exact H12.
    exact H8.
    intros [m1' [tr1 [vres1 [eval1 [resinj [trinj minj]]]]]].
    eexists _, _.
    split.
    - econstructor. subst q'. exact h1. reflexivity. exact h2. exact H4. exact h3. exact h4.
      exact eval1. reflexivity.
    - split.
      subst r. econstructor. apply mit_incr_refl. exact resinj. exact minj.
      admit. admit.
      exact trinj.
  Admitted.

End MEM_INJ.

Section ABS_LI.
  (* This section defines a language interface with memory abstracted out *)
  Record d_query :=
    dq {
        dq_vf: val;
        dq_sg: signature;
        dq_args: list val;
      }.
  Record d_reply :=
    dr {
        dr_retval: val;
      }.
  Canonical Structure li_d :=
    {|
      query := d_query;
      reply := d_reply;
      entry := dq_vf;
    |}.
  Inductive q_rel: query li_d -> query li_c -> mem -> Prop:=
  | q_rel_intro:
      forall vf sg args m,
        q_rel ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|})
              ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|}) m.
  Inductive r_rel: reply li_d -> reply li_c -> mem -> Prop:=
    r_rel_intro:
      forall ret m,
        r_rel ({|dr_retval:=ret|})
              ({|cr_retval:=ret;cr_mem:=m|}) m.
  Inductive qr_rel_list: list (query li_d * reply li_d) -> list (query li_c * reply li_c) -> Prop:=
  | qr_rel_nil: qr_rel_list nil nil
  | qr_rel_cons:
      forall dq dr cq cr ds cs m m',
        q_rel dq cq m ->
        r_rel dr cr m' ->
        qr_rel_list ds cs ->
        qr_rel_list ((dq, dr)::ds) ((cq, cr)::cs).
  Inductive li_rel: (query li_d * reply li_d) -> (query li_c * reply li_c) -> Prop:=
  | rel_intro:
      forall vf sg args ret m,
        li_rel ({|dq_vf:=vf;dq_sg:=sg;dq_args:=args|}, {|dr_retval:=ret|})
               ({|cq_vf:=vf;cq_sg:=sg;cq_args:=args;cq_mem:=m|}, {|cr_retval:=ret;cr_mem:=m|}).
  Local Obligation Tactic := idtac.
  Program Definition li_dc: li_d --o li_c :=
    {|
      has '(d, c) := li_rel d c
    |}.
  Next Obligation.
    intros [[dq1 dr1] [cq1 cr1]] [[dq2 dr2] [cq2 cr2]]. simpl.
    intros rel1 rel2. intuition.
    - destruct cq1. destruct cq2. inversion H. clear H. subst.
      inversion rel1. subst. inversion rel2. subst.
      f_equal. exploit H1. auto. congruence.
    - injection H. destruct cr1. destruct cr2. destruct cq1. destruct cq2.
      inversion rel1. inversion rel2. subst. intros.
      f_equal. congruence. congruence.
  Defined.
End ABS_LI.

Section MODULE_VAR.
  Variable se : Genv.symtbl.
  Variable p : Clight.program.
  Let ge : genv := globalenv se p.

  Inductive module_var : block -> Z -> Prop :=
  | module_var_intro id b (v : globvar type) (ty : type):
      Genv.find_symbol ge id = Some b ->
      Genv.find_def ge b = Some (Gvar v) ->
      ty = gvar_info v ->
      module_var b (sizeof ge ty).
  Definition non_module_var (b : block) (ofs : Z) : Prop :=
    ~ module_var b ofs.
End MODULE_VAR.

Section MEM_ABSTRACTION.
  Variable inj: meminj_thr.
  Variable p_abs: !li_d --o li_c.
  Variable p_con: !li_d --o li_c.

  Definition mem_refine (q: query li_c)(r: reply li_c): Prop :=
    forall s q',
      has p_abs (s, (q, r)) ->
      cc_inj_query inj q q' ->
      exists r',
        has p_con (s, (q', r')) /\
        cc_inj_reply inj r r'.
End MEM_ABSTRACTION.

(* The general case for a clight program to be correct w.r.t its specification *)
Section CORRECTNESS.
  Variable p : Clight.program.
  Variable se : Genv.symtbl.
  Let clight_p : !li_c --o li_c := clight_bigstep p se. (* the semantics of the clight program *)
  (* the semantics of the clight program on top of a deepsea underlay *)
  Let d_p : !li_d --o li_c := clight_p @ !li_dc.
  (* the coherent space where specification lives in *)
  Let spec_space : space := !li_d --o !li_d.
  (* the specification *)
  Variable spec : !li_d --o !li_d.

  Record correctness :=
    {
      (* rel : the relation that relates specifications and the memory *)
      rel : token spec_space -> mem -> Prop;
      (* the condition that the memory has to satisfy *)
      init_mem : mem -> Prop;
      mem_scope : forall m m' t, Mem.unchanged_on (module_var se p) m m' -> rel t m -> rel t m';
      simulation:
        forall s dq dr t m,
          rel (s, (dq, dr)::t) m ->
          exists u v cr cq m',
            s = u ++ v /\
            (* Clight implementation simulates deepsea event e *)
            q_rel dq cq m /\
            has d_p (u, (cq, cr)) /\
            r_rel dr cr m' /\
            Mem.unchanged_on (non_module_var se p) m m' /\
            (* behavior of the remaning trace *)
            rel (v, t) m';
      correct_cond: forall m t, has spec t -> init_mem m -> rel t m;
    }.
  Inductive init_mem_match: token (!li_c) -> mem -> Prop :=
  | nil_match m:
      init_mem_match nil m
  | cons_match q r s m:
      cq_mem q = m ->
      init_mem_match ((q,r) :: s) m.
  Inductive final_mem_match: token (!li_c) -> mem -> Prop :=
  | f_nil_match m:
      final_mem_match nil m
  | f_last_match q r m:
      cr_mem r = m ->
      final_mem_match ((q, r) :: nil) m
  | f_cons_match q s m:
      final_mem_match s m ->
      final_mem_match (q :: s) m.
  Definition final_state (co: correctness):
    forall us ds m,
      rel co (us, ds) m ->
      exists cs m',
        init_mem_match cs m /\
        has (dag_ext d_p) (us, cs) /\
        qr_rel_list ds cs /\ 
        final_mem_match cs m' /\
        Mem.unchanged_on (non_module_var se p) m m'.
  Proof.
    destruct co as [rel ? scope sim ?]. simpl.
    intros us ds.
    revert us.
    induction ds.
    - intros. assert (us = nil). admit.
      subst. exists nil, m.
      split. constructor.
      split. exists nil. split. constructor. constructor.
      split. constructor. split. constructor. apply Mem.unchanged_on_refl.
    - intros. destruct a as [dq dr].
      specialize (sim _ _ _ _ _ H) as [vs [ws [cr0 [cq0 [m0 [useq [q0rel [impl [r0rel [m0_unchanged rest]]]]]]]]]].
      specialize (IHds _ _ rest) as [cs1 [m1 [mm1 [[dus [dus_concat dus_lmap]] [dc_map [mm2 m1_unchanged]]]]]].
      exists ((cq0, cr0)::cs1). exists m1.
      split. constructor. inversion q0rel. auto.
      split. exists (vs::dus). split. rewrite useq. constructor. auto. constructor. auto. auto.
      split. econstructor. exact q0rel. exact r0rel. auto.
      split. constructor. auto.
      eapply Mem.unchanged_on_trans. exact m0_unchanged. exact m1_unchanged.
  Admitted.
  Section SOUND.
    Context {co: correctness}.
    Variable c: Clight.program.
    Variable c_se: Genv.symtbl.
    Let inj: meminj_thr :=
      {|
        mit_meminj :=
          fun b =>
            match Genv.find_def (globalenv se p) b with
            | Some (Gvar _) => Some(b, 0)
            | _ => None
            end;
        mit_l := 1%positive;
        mit_r := 1%positive
      |}.
    Let p_abs: !li_d --o li_c :=
      clight_bigstep c c_se @ !li_dc @ spec.
    Let p_con: !li_d --o li_c :=
      clight_bigstep c c_se @ (dag_ext d_p).
    Theorem mem_abs_sound:
      forall q r,
        (forall m, Mem.inject inj (cq_mem q) m -> init_mem co m) ->
        mem_refine inj p_abs p_con q r.
    Proof.
      intros q r m_cond. intros us q' abs_map qinj. inversion qinj. subst.
      specialize (m_cond _ H1).
      simpl in abs_map. destruct abs_map as [abs_cs [[spec_ds [has_spec dc_rel]] abs_impl_qr]].
      exploit (correct_cond co). exact has_spec. exact m_cond. intros init_rel.
      exploit (final_state co). exact init_rel.
      intros [cs [mc' [mm0 [impl [rel_cs [mm1 unchanged]]]]]].
      exists ({|cr_retval:= cr_retval r; cr_mem:= mc'|}).
      split. simpl. exists cs.
      split. apply impl.
      
      
  End SOUND.
End CORRECTNESS.

Local Obligation Tactic := idtac.
Program Definition empty_obj : ObjSig :=
  {|
    event := Empty_set
  |}.
Next Obligation.
  esplit; intros; try contradiction.
  refine None.
  Unshelve.
  intros; try contradiction.
  intros; try contradiction.
Defined.
Next Obligation.
  esplit; intros; try contradiction.
Defined.
Program Definition unit_trace : clique (!empty_obj) :=
  {|
    has s := s = nil
  |}.
Next Obligation.
  simpl. intros. subst. constructor.
Defined.
Program Definition unit_trace_extend {s : space} (c : clique s) : !empty_obj --o s :=
  {|
    has '(u, t) := u = nil /\ has c t
  |}.
Next Obligation.
  intros s c [u1 s1] [u2 s2]. simpl.
  intros [-> has1] [-> has2] coh.
  split.
  - exploit (has_coh _ c s1 s2); auto.
  - auto.
Defined.

Section GS_CORRECT.
  Variable p : Clight.program.  (* a getter/setter program *)
  Variable se : Genv.symtbl.
  Let clight_p : !li_c --o li_c := clight_bigstep p se.
  Variable gs_obj: ObjSig.
  (* the getter/setter program represented as 1 --o li_c *)
  Program Definition deepsea_p : !empty_obj --o li_c :=
    {|
      has '(s, c) := s = nil /\ has clight_p (nil, c)
    |}.
  Next Obligation.
    intros [s1 qr1] [s2 qr2]. simpl.
    intros [-> lmaps1] [-> lmaps2] H.
    split; intuition.
    exploit (has_coh _ (c_bigstep_lmaps se p) (nil, qr1) (nil, qr2)).
    apply lmaps1. apply lmaps2. constructor.
    intuition.
  Defined.
  (* Since the getter/setter objects do not interact with the environment,
     their specifications are just a clique within the space of !obj *)
  Variable spec : clique (!gs_obj).
  (* The witness relation *)
  Variable gs_rel : token (!gs_obj) -> mem -> Prop.
  (* The condition on the initial memory *)
  Variable gs_init_mem : mem -> Prop.
  (* Proof obligation 1 *)
  Hypothesis gs_mem_scope :
    forall m m' t, Mem.unchanged_on (module_var se p) m m' -> gs_rel t m -> gs_rel t m'.
  (* Proof obligation 2 *)
  Hypothesis gs_simulation :
    forall e t m,
      gs_rel (e :: t) m ->
      exists cq cr m',
        m = cq_mem cq /\
        event_C_args gs_obj e = cq_args cq /\
        has clight_p (nil, (cq, cr)) /\
        m' = cr_mem cr /\
        event_C_res gs_obj e = cr_retval cr /\
        gs_rel t m'.
  (* Proof obligation 3 *)
  Hypothesis gs_init_rel : forall m t, has spec t -> gs_init_mem m -> gs_rel t m.

  (* Adapt the correctness of a getter/setter object into the general form *)
  Program Definition gs_correct : correctness p se empty_obj gs_obj (unit_trace_extend spec) :=
    {|
      rel '(u, o) m := gs_rel o m /\ u = nil;
      init_mem := gs_init_mem
    |}.
  Next Obligation.
    intros m m' [s t] unchanged. simpl.
    intros [rel <-]. intuition.
    eapply gs_mem_scope. apply unchanged. auto.
  Defined.
  Next Obligation.
    intros s e t m. simpl.
    intros [rel ->]. exists nil, nil.
    specialize (gs_simulation e t m rel) as [cq [cr [m' [meq [arg [impl [res [m'eq rest]]]]]]]].
    exists cq, cr, m'.
    intuition.
    exists nil. split; intuition. constructor.
  Defined.
  Next Obligation.
    intros m [s t]. simpl.
    intros [-> H] H1. split; auto.
  Defined.
End GS_CORRECT.

Section ABSFUN_CORRECT.
  Variable p : Clight.program.  (* an absfun program *)
  Variable se : Genv.symtbl.
  Let clight_p : !li_c --o li_c := clight_bigstep p se.
  Variable underlay_obj : ObjSig.
  Variable overlay_obj : ObjSig.
  (* the clight program on top of a deepsea underlay *)
  Let deepsea_p : !underlay_obj --o li_c := clight_p @ !(objsig2lic underlay_obj).
  (* Since the absfun objects are linear, we can use their linear pattern as spec
     Regular externsion extends the linear paatern to the general form *)
  Variable spec : !underlay_obj --o overlay_obj.
  (* The proof obligation for absfun objects *)
  Hypothesis absfun_sim:
    forall s e,
      has spec (s, e) ->
      exists cq cr,
        event_C_args overlay_obj e = cq_args cq /\
        event_C_res overlay_obj e = cr_retval cr /\
        cq_mem cq = cr_mem cr /\
        has deepsea_p (s, (cq, cr)) .

  (* Adapt the correctness of the absfun objects into the genral form *)
  Program Definition absfun_correct : correctness p se underlay_obj overlay_obj (dag_ext spec) :=
    {|
      rel '(s, t) _ := has (dag_ext spec) (s, t);
      init_mem _ := True;
    |}.
  Next Obligation.
    intros m m' [s t] unchanged. simpl.
    auto.
  Defined.
  Next Obligation.
    intros s e t m. simpl.
    intros [ss [comul lmap]].
    inversion comul.
    - inversion lmap. subst. inversion H3.
    - exists s0, a.
      specialize (absfun_sim s0 e).
      subst ss. subst s.
      inversion lmap. subst.
      specialize (absfun_sim H3) as [q [r [arg [res [meq impl]]]]].
      exists ({|cq_vf:=(cq_vf q); cq_sg:=(cq_sg q); cq_args:=(cq_args q); cq_mem:=m|}).
      exists r, m.
      intuition. unfold cq_mem. reflexivity.
      Focus 3. exists aa. intuition.
      Admitted.
  Next Obligation.
    intros m [s t]. auto.
  Defined.
End ABSFUN_CORRECT.
