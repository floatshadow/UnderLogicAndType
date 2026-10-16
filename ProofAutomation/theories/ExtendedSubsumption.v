(** * Case-study semantic subtyping checkpoints

    This file is intentionally proof-automation facing.  Case-study
    refinements should be exposed as ordinary [sub_type_under] lemmas:

      Γ |- τ1 <: τ2

    They can then be consumed by the existing [EXT_Sub] rule.  Avoid
    term-specific subsumption facts here; if a fact only holds for one
    particular program body, it is not a subtype lemma. *)

From stdpp Require Import gmap.
From CoreLang Require Import Syntax.
From ContextTypeLanguage Require Import Syntax.
From Denotation Require Import Context.
From ContextTyping Require Import Typing.
From CoreLang Require Import BasicTyping BasicTypingProps.
From ContextLogic Require Import FormulaConnectivesHigher.
From ContextTypeLanguage Require Import WF.
From ContextBasicDenotation Require Import RelevantEnv BasicTypingFormula.
From Denotation Require Import TypeEquivCore TypePersistBase.
From ProofAutomation Require Export ExtendedTyping.

Open Scope core_scope.
Open Scope case_scope.
Open Scope cty_scope.
Open Scope ctx_scope.

Definition extended_semantic_subtype
    (Σ : gmap atom ty) (Γ : ctx) (τsrc τtgt : context_ty) : Prop :=
  sub_type_under Σ Γ τsrc τtgt.

(** Well-formedness side of [sub_type_under]; every generic subtyping
    checkpoint below must carry it, since [sub_type_under] is false for
    ill-formed contexts/types. *)
Definition subtype_wf
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) : Prop :=
  wf_ctx_under Σ Γ ∧
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ1 ∧
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ2 ∧
  erase_ty τ1 = erase_ty τ2.

Definition qualifier_entails (q1 q2 : type_qualifier) : Prop :=
  forall s : LStoreOn (qual_vars q1 ∪ qual_vars q2),
    qual_prop q1 (lstore_on_restrict (qual_vars q1) s ltac:(set_solver)) ->
    qual_prop q2 (lstore_on_restrict (qual_vars q2) s ltac:(set_solver)).

(* Proofs (formerly ExtendedSubsumptionProofs.v). *)
(** * Proofs of the generic semantic subtyping checkpoints

    The generic lemmas are proved under the name [<lemma>_proof] and exported
    under their original names below.

    Proved verbatim:
      extended_semantic_subtype_trans, extended_semantic_subtype_inter_left,
      extended_semantic_subtype_inter_right, extended_semantic_subtype_inter_comm,
      subtype_inter_over_under_to_over_part, subtype_inter_over_under_to_over,
      subtype_vacuous_of_unmodelable_ctx, subtype_over_closed_by_qualifier.

    FALSE as stated (counterexamples below; corrected versions proved as
    [<lemma>_corrected]):
      subtype_under_closed_by_qualifier, subtype_inter_over_under_to_under_and,
      subtype_inter_over_under_to_under.

    Counterexamples (Σ = ∅, Γ = CtxEmpty, b = ℕ, e = tret (vconst (cnat _))).
    Key semantic facts: [FAtom q] is EXACT and worlds are nonempty, so
    (a) [FUnder (FAtom q)] is unsatisfiable when [q] is unsatisfiable, and
    (b) a qualifier that does not mention [ν] (e.g. [qual_top = tqual ∅ (λ _, True)])
        gives a TRIVIAL under type: [U[b] = [: b | qual_top]] holds for every
        total term (see [subtype_over_to_UTop_trivial]).
    - subtype_under_closed_by_qualifier, q1 := mk_q_eq ν 0,
      q2 := tqual {[LVBound 0]} (λ _, False): [qualifier_entails q2 q1] holds
      vacuously, [tret 0 : [: ℕ | ν = 0]], but [[: ℕ | false]] is uninhabited
      (by (a)).  Even with a satisfiable target: q1 := qual_top,
      q2 := mk_q_eq ν 0; [tret 1] inhabits [U[ℕ]] by (b), but its only result
      1 does not cover 0.
    - subtype_inter_over_under_to_under_and, q_over := q_nonneg ν (all naturals),
      q_under := qual_top: [tret 0] inhabits {: ℕ | q_nonneg ν} ⊓ U[ℕ], while
      [: ℕ | qual_and (q_nonneg ν) qual_top] (vars {ν}) demands that every
      natural number is reachable.  The same instance with
      q_tgt := qual_and q_over q_under (reflexive premise) refutes
      subtype_inter_over_under_to_under. *)



Open Scope core_scope.
Open Scope case_scope.
Open Scope cty_scope.
Open Scope ctx_scope.

Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation StoreT := (Store (V := value)) (only parsing).

Lemma ext_observed_world_dom (Σ : gmap atom ty) Γ e τ (m : WfWorldT) :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ ->
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  fv_tm e ∪ fv_cty τ ⊆ world_dom (m : WorldT).
Proof.
  intros HΓ Hτ He Hctx.
  assert (Hwf : context_typing_wf Σ Γ e τ) by (split; [|split]; assumption).
  pose proof (context_typing_wf_fv_tm_subset Σ Γ e τ Hwf) as Htm.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ Hwf) as Hτfv.
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m Hworld) as Hdom.
  pose proof (ctx_erasure_under_erase_ctx_dom_subset Σ Γ).
  set_solver.
Qed.

Lemma ext_ty_denote_scoped (Σ : gmap atom ty) Γ e τ (m : WfWorldT) :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ ->
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  formula_scoped_in_world m (ty_denote (erase_ctx Γ) τ e).
Proof.
  intros HΓ Hτ He Hctx.
  pose proof (ext_observed_world_dom Σ Γ e τ m HΓ Hτ He Hctx).
  unfold formula_scoped_in_world, ty_denote.
  pose proof (ty_denote_gas_fv_subset (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx Γ)) τ e).
  set_solver.
Qed.

(** Generic recipe: a pointwise (per world) implication between two type
    denotations at the same erased basic type yields semantic subtyping. *)
Lemma ext_sub_type_of_pointwise Σ Γ τ1 τ2 :
  subtype_wf Σ Γ τ1 τ2 ->
  (forall e (m : WfWorldT),
     erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ1 ->
     m ⊨ ty_denote (erase_ctx Γ) τ1 e ->
     m ⊨ ty_denote (erase_ctx Γ) τ2 e) ->
  extended_semantic_subtype Σ Γ τ1 τ2.
Proof.
  intros [HΓ [H1 [H2 Herase]]] Hpt.
  unfold extended_semantic_subtype, sub_type_under.
  split; [exact HΓ|]. split; [exact H1|]. split; [exact H2|].
  split; [exact Herase|].
  intros e He m Hctx.
  eapply res_models_impl_intro_scoped.
  - eapply ext_ty_denote_scoped; eauto.
  - eapply ext_ty_denote_scoped; eauto. rewrite <- Herase. exact He.
  - intros Hm. eapply Hpt; eauto.
Qed.

Lemma extended_semantic_subtype_trans_proof
    Σ Γ τ1 τ2 τ3 :
  extended_semantic_subtype Σ Γ τ1 τ2 ->
  extended_semantic_subtype Σ Γ τ2 τ3 ->
  extended_semantic_subtype Σ Γ τ1 τ3.
Proof.
  intros [HΓ [H1 [H2 [He12 Hent12]]]] [_ [_ [H3 [He23 Hent23]]]].
  unfold extended_semantic_subtype, sub_type_under.
  split; [exact HΓ|]. split; [exact H1|]. split; [exact H3|].
  split; [congruence|].
  intros e He m Hctx.
  pose proof (Hent12 e He m Hctx) as Himp12.
  assert (He2 : erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ2) by (rewrite <- He12; exact He).
  pose proof (Hent23 e He2 m Hctx) as Himp23.
  eapply res_models_impl_intro_future.
  - apply formula_scoped_impl_iff. split.
    + eapply formula_scoped_impl_l. eapply res_models_scoped. exact Himp12.
    + eapply formula_scoped_impl_r. eapply res_models_scoped. exact Himp23.
  - intros m' Hle Hm'.
    eapply res_models_impl_elim_future; [exact Hle|exact Himp23|].
    eapply res_models_impl_elim_future; [exact Hle|exact Himp12|exact Hm'].
Qed.

Lemma subtype_vacuous_of_unmodelable_ctx_proof
    Σ Γ τ1 τ2 :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ1 ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ2 ->
  erase_ty τ1 = erase_ty τ2 ->
  entails (ctx_denote_under Σ Γ) FFalse ->
  extended_semantic_subtype Σ Γ τ1 τ2.
Proof.
  intros HΓ H1 H2 Herase Hfalse.
  unfold extended_semantic_subtype, sub_type_under.
  split; [exact HΓ|]. split; [exact H1|]. split; [exact H2|].
  split; [exact Herase|].
  intros e He m Hctx.
  pose proof (Hfalse m Hctx) as Hf.
  unfold res_models in Hf. cbn in Hf. tauto.
Qed.

Lemma ty_denote_inter_elim_l Δ τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote Δ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote Δ τ1 e.
Proof.
  unfold ty_denote. cbn [cty_depth ty_denote_gas].
  intros Hm. apply res_models_and_elim_r in Hm.
  apply res_models_and_elim_l in Hm.
  rewrite ty_denote_gas_saturate in Hm by lia. exact Hm.
Qed.

Lemma ty_denote_inter_elim_r Δ τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote Δ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote Δ τ2 e.
Proof.
  unfold ty_denote. cbn [cty_depth ty_denote_gas].
  intros Hm. apply res_models_and_elim_r in Hm.
  apply res_models_and_elim_r in Hm.
  rewrite ty_denote_gas_saturate in Hm by lia. exact Hm.
Qed.
Lemma relevant_env_inter_comm Σ τ1 τ2 e :
  relevant_env Σ (CTInter τ2 τ1) e = relevant_env Σ (CTInter τ1 τ2) e.
Proof.
  unfold relevant_env, context_ty_lvars. cbn [context_ty_lvars_at].
  f_equal. set_solver.
Qed.

Lemma ty_guard_inter_comm Σ τ1 τ2 e (m : WfWorldT) :
  erase_ty τ1 = erase_ty τ2 ->
  m ⊨ ty_guard_formula (relevant_env Σ (CTInter τ1 τ2) e) (CTInter τ1 τ2) e ->
  m ⊨ ty_guard_formula (relevant_env Σ (CTInter τ2 τ1) e) (CTInter τ2 τ1) e.
Proof.
  intros Herase Hguard.
  rewrite relevant_env_inter_comm.
  unfold ty_guard_formula in *.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  repeat rewrite res_models_and_iff.
  split; [|split; [exact Hworld|split; [|exact Htotal]]].
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hdom [Hvars Hshape]]].
    split; [exact Hlc|]. split; [exact Hdom|]. split.
    + unfold context_ty_lvars in *. cbn [context_ty_lvars_at] in *. set_solver.
    + cbn [context_ty_shape_ok] in *. destruct Hshape as [? [? ?]]. split; [assumption|]. split; [assumption|]. cbn [erase_ty] in *; congruence.
  - cbn [erase_ty] in *. rewrite <- Herase. exact Hbasic.
Qed.

Lemma ty_denote_inter_comm Δ τ1 τ2 e (m : WfWorldT) :
  erase_ty τ1 = erase_ty τ2 ->
  m ⊨ ty_denote Δ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote Δ (CTInter τ2 τ1) e.
Proof.
  intros Herase.
  unfold ty_denote. cbn [cty_depth ty_denote_gas].
  intros Hm. apply res_models_and_iff in Hm as [Hg Hm].
  apply res_models_and_iff in Hm as [H1 H2].
  apply res_models_and_intro_from_models.
  - apply ty_guard_inter_comm; assumption.
  - rewrite Nat.max_comm.
    apply res_models_and_intro_from_models; assumption.
Qed.

Lemma extended_semantic_subtype_inter_left_proof
    Σ Γ τ1 τ2 :
  subtype_wf Σ Γ (τ1 ⊓ τ2) τ1 ->
  extended_semantic_subtype Σ Γ (τ1 ⊓ τ2) τ1.
Proof.
  intros Hwf. apply ext_sub_type_of_pointwise; [exact Hwf|].
  intros e m _. apply ty_denote_inter_elim_l.
Qed.

Lemma extended_semantic_subtype_inter_right_proof
    Σ Γ τ1 τ2 :
  subtype_wf Σ Γ (τ1 ⊓ τ2) τ2 ->
  extended_semantic_subtype Σ Γ (τ1 ⊓ τ2) τ2.
Proof.
  intros Hwf. apply ext_sub_type_of_pointwise; [exact Hwf|].
  intros e m _. apply ty_denote_inter_elim_r.
Qed.

Lemma extended_semantic_subtype_inter_comm_proof
    Σ Γ τ1 τ2 :
  subtype_wf Σ Γ (τ1 ⊓ τ2) (τ2 ⊓ τ1) ->
  extended_semantic_subtype Σ Γ (τ1 ⊓ τ2) (τ2 ⊓ τ1).
Proof.
  intros Hwf. apply ext_sub_type_of_pointwise; [exact Hwf|].
  destruct Hwf as [_ [Hτ _]]. cbn [wf_context_ty_at] in Hτ.
  destruct Hτ as [_ [_ Herase]].
  intros e m _. apply ty_denote_inter_comm. exact Herase.
Qed.

Lemma subtype_inter_over_under_to_over_part_proof
    Σ Γ b q_over q_under :
  subtype_wf Σ Γ (({: b | q_over }) ⊓ ([: b | q_under ])) ({: b | q_over }) ->
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ({: b | q_over }).
Proof. apply extended_semantic_subtype_inter_left_proof. Qed.

Lemma subtype_inter_over_under_to_over_proof
    Σ Γ b q_over q_under q_tgt :
  subtype_wf Σ Γ (({: b | q_over }) ⊓ ([: b | q_under ])) ({: b | q_tgt }) ->
  extended_semantic_subtype Σ Γ
    ({: b | q_over }) ({: b | q_tgt }) ->
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ({: b | q_tgt }).
Proof.
  intros Hwf Hsub.
  eapply extended_semantic_subtype_trans_proof; [|exact Hsub].
  apply subtype_inter_over_under_to_over_part_proof.
  destruct Hwf as [HΓ [Hsrc [_ Herase]]].
  destruct Hsub as [_ [Hover _]].
  split; [exact HΓ|]. split; [exact Hsrc|]. split; [exact Hover|].
  reflexivity.
Qed.
Lemma qual_open_holds_entails (q1 q2 : type_qualifier) (y : atom)
    (σ : gmap atom value) :
  qualifier_entails q1 q2 ->
  lc_lvars (lvars_open 0%nat y (qual_vars q2)) ->
  lvars_fv (lvars_open 0%nat y (qual_vars q2)) ⊆ dom σ ->
  qualifier_holds_store (qual_open_atom 0%nat y q1) σ ->
  qualifier_holds_store (qual_open_atom 0%nat y q2) σ.
Proof.
  destruct q1 as [D1 P1], q2 as [D2 P2].
  unfold qualifier_entails.
  cbn [qual_vars qual_lvars qual_prop qual_open_atom qualifier_holds_store].
  intros Hent Hlc2 Hsub2 [Hlc1 [Hsub1 HP1]].
  exists Hlc2, Hsub2.
  assert (Hlc12 : lc_lvars (lvars_open 0%nat y (D1 ∪ D2))).
  { rewrite lvars_open_union. intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv]; [apply Hlc1|apply Hlc2]; exact Hv. }
  assert (Hsub12 : lvars_fv (lvars_open 0%nat y (D1 ∪ D2)) ⊆ dom σ).
  { rewrite lvars_open_union, lvars_fv_union. set_solver. }
  set (s := lstore_on_open_back 0 y (D1 ∪ D2)
    (lstore_on_lift_store _ σ Hlc12 Hsub12)).
  specialize (Hent s).
  assert (Heq : forall D (HD : D ⊆ D1 ∪ D2) Hlc Hsub,
    lstore_on_restrict D s HD =
    lstore_on_open_back 0 y D
      (lstore_on_lift_store (set_swap (LVBound 0) (LVFree y) D) σ Hlc Hsub)).
  {
    intros D HD Hlc Hsub. apply lstore_on_ext. subst s.
    unfold lstore_on_restrict, storeA_on_restrict, lstore_on_open_back,
      lstore_on_lift_store, lso_store.
    cbn [storeAO_store].
    unfold lstore_swap, lstore_rekey. apply storeA_map_eq. intros z.
    pose proof (swap_inj (LVBound 0) (LVFree y)) as Hinj.
    rewrite (storeA_restrict_lookup (V:=value)).
    set (w := swap (LVBound 0) (LVFree y) z).
    assert (Hz : z = swap (LVBound 0) (LVFree y) w)
      by (subst w; symmetry; apply swap_involutive).
    rewrite Hz. rewrite !(lookup_kmap (swap (LVBound 0) (LVFree y))).
    rewrite !(storeA_restrict_lookup (lstore_lift_free σ)).
    subst w. rewrite swap_involutive in *.
    destruct (decide (z ∈ D)) as [HzD|HzD]; repeat destruct decide;
      try reflexivity; exfalso;
      rewrite ?elem_of_set_swap, ?swap_involutive in *; set_solver.
  }
  rewrite (Heq D1 _ Hlc1 Hsub1) in Hent.
  rewrite (Heq D2 _ Hlc2 Hsub2) in Hent.
  exact (Hent HP1).
Qed.

Lemma erase_ctx_dom_subset_ctx_dom Γ :
  dom (erase_ctx Γ) ⊆ ctx_dom Γ.
Proof.
  induction Γ.
  - cbn [erase_ctx ctx_dom]. intros x Hx. apply elem_of_dom in Hx as [? Hx]. rewrite lookup_empty in Hx. discriminate.
  - rewrite erase_ctx_bind_dom. cbn [ctx_dom]. set_solver.
  - cbn [erase_ctx ctx_dom]. intros z Hz. apply elem_of_dom in Hz as [? Hz].
    apply lookup_union_Some_raw in Hz as [Hz|[_ Hz]];
      apply elem_of_dom_2 in Hz; set_solver.
  - cbn [erase_ctx ctx_dom]. intros z Hz. apply elem_of_dom in Hz as [? Hz].
    apply lookup_union_Some_raw in Hz as [Hz|[_ Hz]];
      apply elem_of_dom_2 in Hz; set_solver.
  - cbn [erase_ctx ctx_dom]. set_solver.
Qed.

Definition qual_only_nu (q : type_qualifier) : Prop :=
  forall v, v ∈ qual_vars q -> v = LVBound 0.

Lemma qual_only_nu_of_wf Γ q :
  lvars_wf_at 1 (dom (erase_ctx Γ)) (qual_vars q) ->
  qual_dom q ## ctx_dom Γ ->
  qual_only_nu q.
Proof.
  intros Hwf Hdisj [k|x] Hv.
  - specialize (Hwf _ Hv). cbn [lvar_wf_at] in Hwf.
    f_equal. lia.
  - exfalso. specialize (Hwf _ Hv). cbn [lvar_wf_at] in Hwf.
    pose proof (erase_ctx_dom_subset_ctx_dom Γ).
    assert (x ∈ qual_dom q) by (unfold qual_dom; apply lvars_fv_elem; exact Hv).
    set_solver.
Qed.

Lemma qual_only_nu_dom q :
  qual_only_nu q -> qual_dom q = ∅.
Proof.
  intros Honly. apply set_eq. intros x. split; [|set_solver].
  intros Hx. unfold qual_dom in Hx. apply lvars_fv_elem in Hx.
  apply Honly in Hx. discriminate.
Qed.

Lemma qual_only_nu_context_ty_lvars_over b q :
  qual_only_nu q -> context_ty_lvars (CTOver b q) = ∅.
Proof.
  intros Honly. unfold context_ty_lvars. cbn [context_ty_lvars_at].
  apply set_eq. intros u. split; [|set_solver].
  intros Hu. apply lvars_at_depth_elem in Hu as [v [Hv Hdepth]].
  apply Honly in Hv. subst v. cbn in Hdepth. discriminate.
Qed.

Lemma qual_only_nu_context_ty_lvars_under b q :
  qual_only_nu q -> context_ty_lvars (CTUnder b q) = ∅.
Proof.
  intros Honly. unfold context_ty_lvars. cbn [context_ty_lvars_at].
  apply set_eq. intros u. split; [|set_solver].
  intros Hu. apply lvars_at_depth_elem in Hu as [v [Hv Hdepth]].
  apply Honly in Hv. subst v. cbn in Hdepth. discriminate.
Qed.

Lemma qual_only_nu_open_diff q y :
  qual_only_nu q ->
  qual_vars (qual_open_atom 0%nat y q) ∖ {[LVFree y]} = ∅.
Proof.
  intros Honly. rewrite qual_open_atom_vars.
  apply set_eq. intros v. split; [|set_solver].
  intros Hv. apply elem_of_difference in Hv as [Hv Hne].
  apply elem_of_set_swap in Hv. apply Honly in Hv.
  exfalso. apply Hne. apply elem_of_singleton.
  rewrite <- (swap_involutive (LVBound 0) (LVFree y) v), Hv, swap_l.
  reflexivity.
Qed.

Lemma qual_only_nu_open_lc q y :
  qual_only_nu q ->
  lc_lvars (lvars_open 0%nat y (qual_vars q)).
Proof.
  intros Honly v Hv.
  apply elem_of_set_swap in Hv. apply Honly in Hv.
  rewrite <- (swap_involutive (LVBound 0) (LVFree y) v), Hv, swap_l.
  exact I.
Qed.

Lemma qual_only_nu_open_fv q y :
  qual_only_nu q ->
  lvars_fv (lvars_open 0%nat y (qual_vars q)) ⊆ {[y]}.
Proof.
  intros Honly x Hx. apply lvars_fv_elem in Hx.
  apply elem_of_set_swap in Hx. apply Honly in Hx.
  revert Hx. unfold swap. repeat destruct decide; try congruence; set_solver.
Qed.

Lemma ty_guard_transport Σ τ1 τ2 e (m : WfWorldT) :
  erase_ty τ1 = erase_ty τ2 ->
  context_ty_lvars τ2 ⊆ context_ty_lvars τ1 ->
  context_ty_shape_ok τ2 ->
  m ⊨ ty_guard_formula (relevant_env Σ τ1 e) τ1 e ->
  m ⊨ ty_guard_formula (relevant_env Σ τ1 e) τ2 e.
Proof.
  intros Herase Hlv Hshape Hguard.
  unfold ty_guard_formula in *.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  repeat rewrite res_models_and_iff.
  split; [|split; [exact Hworld|split; [|exact Htotal]]].
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hdom [Hvars _]]].
    split; [exact Hlc|]. split; [exact Hdom|]. split; [set_solver|exact Hshape].
  - rewrite <- Herase. exact Hbasic.
Qed.

Lemma over_open_body_store_iff q y (my : WfWorldT) :
  qual_only_nu q ->
  y ∈ world_dom (my : WorldT) ->
  my ⊨ over_open_body q y <->
  forall σ, (my : WorldT) σ -> qualifier_holds_store (qual_open_atom 0%nat y q) σ.
Proof.
  intros Honly Hy. unfold over_open_body.
  rewrite (qual_only_nu_open_diff q y Honly).
  split.
  - intros H. apply res_models_fibvars_empty_elim in H.
    apply res_models_over_FAtom_store_holds. exact H.
  - intros H. apply res_models_fibvars_empty_intro.
    apply res_models_over_FAtom_intro_store_holds; [|exact H].
    unfold formula_scoped_in_world.
    rewrite formula_fv_over, formula_fv_atom, qual_open_atom_vars.
    pose proof (qual_only_nu_open_fv q y Honly). set_solver.
Qed.

Lemma subtype_over_closed_by_qualifier_proof
    Σ Γ b q1 q2 :
  subtype_wf Σ Γ ({: b | q1 }) ({: b | q2 }) ->
  qual_dom q1 ## ctx_dom Γ ->
  qual_dom q2 ## ctx_dom Γ ->
  qualifier_entails q1 q2 ->
  extended_semantic_subtype Σ Γ
    ({: b | q1 }) ({: b | q2 }).
Proof.
  intros Hwf Hd1 Hd2 Hent.
  pose proof Hwf as [_ [Hwf1 [Hwf2 _]]].
  unfold over_ty in Hwf1, Hwf2. cbn [wf_context_ty_at] in Hwf1, Hwf2.
  pose proof (qual_only_nu_of_wf Γ q1 Hwf1 Hd1) as Hq1.
  pose proof (qual_only_nu_of_wf Γ q2 Hwf2 Hd2) as Hq2.
  apply ext_sub_type_of_pointwise; [exact Hwf|].
  intros e m _ Hm.
  unfold ty_denote, over_ty in *. cbn [cty_depth ty_denote_gas] in *.
  set (Σl := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hrel : relevant_env Σl (CTOver b q2) e = relevant_env Σl (CTOver b q1) e).
  { unfold relevant_env.
    rewrite (qual_only_nu_context_ty_lvars_over b q1 Hq1),
      (qual_only_nu_context_ty_lvars_over b q2 Hq2). reflexivity. }
  rewrite Hrel.
  apply res_models_and_iff in Hm as [Hg Hall].
  apply res_models_and_intro_from_models.
  - eapply ty_guard_transport; [reflexivity| |exact I|exact Hg].
    rewrite (qual_only_nu_context_ty_lvars_over b q2 Hq2). set_solver.
  - eapply res_models_forall_full_world_impl_map; [| |exact Hall].
    + pose proof (res_models_scoped _ _ Hall) as Hsc.
      rewrite formula_scoped_forall_iff, formula_scoped_impl_iff in Hsc |- *.
      destruct Hsc as [HA _]. split; [exact HA|].
      unfold formula_scoped_in_world.
      rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
      pose proof (qual_only_nu_dom q2 Hq2) as Hdom2. unfold qual_dom in Hdom2.
      pose proof (lvars_fv_mono (qual_vars q2 ∖ {[LVBound 0]}) (qual_vars q2)
        ltac:(set_solver)).
      set_solver.
    + exists ∅. intros y _ my Hdom Hres. split; [tauto|].
      assert (Hy1 : LVFree y ∉ qual_vars q1) by (intros Hb; apply Hq1 in Hb; discriminate).
      assert (Hy2 : LVFree y ∉ qual_vars q2) by (intros Hb; apply Hq2 in Hb; discriminate).
      rewrite !formula_open_over_self_body_normalize by assumption.
      assert (Hym : y ∈ world_dom (my : WorldT)) by (rewrite Hdom; set_solver).
      rewrite !over_open_body_store_iff by assumption.
      intros Hall1 σ Hσ.
      eapply qual_open_holds_entails; [exact Hent| | |exact (Hall1 σ Hσ)].
      * apply qual_only_nu_open_lc. exact Hq2.
      * pose proof (qual_only_nu_open_fv q2 y Hq2).
        rewrite (wfworld_store_dom my σ Hσ). set_solver.
Qed.

Lemma lstore_on_lift_store_pi D (σ : StoreT) Hlc Hlc' Hsub Hsub' :
  lstore_on_lift_store D σ Hlc Hsub = lstore_on_lift_store D σ Hlc' Hsub'.
Proof. apply lstore_on_ext. reflexivity. Qed.

Lemma lstore_in_lworld_on_lift_inv
    (D : lvset) (m : WfWorldT) Hlc Hsub (s : LStoreOn (V := value) D) :
  lstore_in_lworld_on s (lworld_on_lift D m Hlc Hsub) ->
  exists σ (Hσ : (m : WorldT) σ) Hsubσ,
    s = lstore_on_lift_store D σ Hlc Hsubσ.
Proof.
  unfold lstore_in_lworld_on, lworld_on_lift.
  cbn [lw lraw_world raw_worldA worldA_stores].
  intros Hmem.
  destruct Hmem as [ρ Hmem].
  destruct Hmem as [Hlift Hρeq].
  unfold res_lift_free in Hlift.
  cbn [raw_worldA worldA_stores] in Hlift.
  destruct Hlift as [store_restricted [Hrestricted Hρeq_lift]].
  destruct Hrestricted as [σ [Hσ Hrestrict_src]].
  assert (Hsubσ : lvars_fv D ⊆ dom (σ : StoreT)).
  { pose proof (wfworld_store_dom m σ Hσ) as Hd.
    change (dom (σ : gmap atom value) = world_dom (m : WorldT)) in Hd.
    change (lvars_fv D ⊆ dom (σ : gmap atom value)). rewrite Hd. exact Hsub. }
  exists σ, Hσ, Hsubσ.
  apply lstore_on_ext.
  unfold lstore_on_lift_store.
  cbn [lso_store storeAO_store].
  rewrite <- Hρeq.
  rewrite Hρeq_lift.
  rewrite <- Hrestrict_src.
  rewrite lstore_lift_free_restrict_fv_lvars_eq.
  reflexivity.
Qed.

(** Store-level characterisation of [FUnder (FAtom q)]: some store of the
    world satisfies [q], and every assignment accepted by [q] is realised by a
    store of the world. *)
Lemma res_models_under_FAtom_inv (m : WfWorldT) (D : lvset) P :
  m ⊨ FUnder (FAtom (tqual D P)) ->
  lc_lvars D /\
  lvars_fv D ⊆ world_dom (m : WorldT) /\
  (exists σ, (m : WorldT) σ /\ qualifier_holds_store (tqual D P) σ) /\
  (forall s, P s -> exists σ (Hσ : (m : WorldT) σ) Hlc Hsubσ,
      s = lstore_on_lift_store D σ Hlc Hsubσ).
Proof.
  intros Hunder.
  pose proof (res_models_scoped _ _ Hunder) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  rewrite formula_fv_under, formula_fv_atom in Hscope.
  unfold res_models in Hunder.
  cbn [formula_measure res_models_fuel] in Hunder.
  destruct Hunder as [_ [m' [[Hdom' Hst'] Hatom]]].
  assert (Hatom_m : m' ⊨ FAtom (tqual D P)).
  { unfold res_models. models_fuel_irrel Hatom. }
  pose proof Hatom as Hatom_raw.
  cbn [formula_measure res_models_fuel qualifier_exact_denote] in Hatom_raw.
  destruct Hatom_raw as [_ [Hlc [Hsub Hiff]]].
  split; [exact Hlc|]. split; [exact Hscope|]. split.
  - destruct (world_wf m') as [[σ0 Hσ0] _].
    exists σ0. split; [apply Hst'; exact Hσ0|].
    eapply res_models_FAtom_store_holds; [exact Hatom_m|exact Hσ0].
  - intros s Hs. apply Hiff in Hs.
    apply lstore_in_lworld_on_lift_inv in Hs as [σ [Hσ [Hsubσ ->]]].
    exists σ, (Hst' σ Hσ), Hlc, Hsubσ. reflexivity.
Qed.

Definition res_filter_raw (m : WorldT) (Q : StoreT -> Prop) : WorldT :=
  mk_worldA (world_dom m) (fun σ => (m : WorldT) σ /\ Q σ).

Definition res_filter (m : WfWorldT) (Q : StoreT -> Prop)
    (σ0 : StoreT) (Hσ0 : (m : WorldT) σ0) (HQ0 : Q σ0) : WfWorldT.
Proof.
  refine (exist _ (res_filter_raw m Q) _).
  split.
  - exists σ0. split; assumption.
  - intros σ [Hσ _]. exact (wfworld_store_dom m σ Hσ).
Defined.

Lemma res_models_under_FAtom_intro (m : WfWorldT) (D : lvset) P :
  lc_lvars D ->
  lvars_fv D ⊆ world_dom (m : WorldT) ->
  (exists σ, (m : WorldT) σ /\ qualifier_holds_store (tqual D P) σ) ->
  (forall s, P s -> exists σ (Hσ : (m : WorldT) σ) Hlc Hsubσ,
      s = lstore_on_lift_store D σ Hlc Hsubσ) ->
  m ⊨ FUnder (FAtom (tqual D P)).
Proof.
  intros Hlc Hsub [σ0 [Hσ0 Hq0]] Hcov.
  set (m' := res_filter m (qualifier_holds_store (tqual D P)) σ0 Hσ0 Hq0).
  assert (Hsub' : lvars_fv D ⊆ world_dom (m' : WorldT)) by exact Hsub.
  unfold res_models. cbn [formula_measure res_models_fuel].
  split.
  { unfold formula_scoped_in_world. rewrite formula_fv_under, formula_fv_atom.
    exact Hsub. }
  exists m'. split.
  { split; [reflexivity|]. intros σ [Hσ _]. exact Hσ. }
  cbn [res_models_fuel qualifier_exact_denote].
  split.
  { unfold formula_scoped_in_world. rewrite formula_fv_atom. exact Hsub. }
  exists Hlc, Hsub'. intros s. split.
  - intros Hs.
    destruct (Hcov s Hs) as [σ [Hσ [Hlcσ [Hsubσ Heq]]]].
    assert (Hm'σ : (m' : WorldT) σ).
    { split; [exact Hσ|]. exists Hlcσ, Hsubσ. rewrite <- Heq. exact Hs. }
    rewrite Heq, (lstore_on_lift_store_pi D σ Hlcσ Hlc Hsubσ Hsubσ).
    apply lstore_in_lworld_on_lift_store_of_world. exact Hm'σ.
  - intros Hmem.
    apply lstore_in_lworld_on_lift_inv in Hmem as [σ [[Hσ Hqσ] [Hsubσ ->]]].
    destruct Hqσ as [Hlc' [Hsub'' HP]].
    rewrite (lstore_on_lift_store_pi D σ Hlc Hlc' Hsubσ Hsub''). exact HP.
Qed.

Lemma lstore_on_restrict_open_back_lift D E (HD : D ⊆ E) (y : atom)
    (σ : StoreT) HlcE HsubE HlcD HsubD :
  lstore_on_restrict D
    (lstore_on_open_back 0 y E
      (lstore_on_lift_store (lvars_open 0%nat y E) σ HlcE HsubE)) HD =
  lstore_on_open_back 0 y D
    (lstore_on_lift_store (lvars_open 0%nat y D) σ HlcD HsubD).
Proof.
  apply lstore_on_ext.
  unfold lstore_on_restrict, storeA_on_restrict, lstore_on_open_back,
    lstore_on_lift_store, lso_store.
  cbn [storeAO_store].
  unfold lstore_swap, lstore_rekey. apply storeA_map_eq. intros z.
  pose proof (swap_inj (LVBound 0) (LVFree y)) as Hinj.
  rewrite (storeA_restrict_lookup (V:=value)).
  set (w := swap (LVBound 0) (LVFree y) z).
  assert (Hz : z = swap (LVBound 0) (LVFree y) w)
    by (subst w; symmetry; apply swap_involutive).
  rewrite Hz. rewrite !(lookup_kmap (swap (LVBound 0) (LVFree y))).
  rewrite !(storeA_restrict_lookup (lstore_lift_free σ)).
  subst w. rewrite swap_involutive in *.
  destruct (decide (z ∈ D)) as [HzD|HzD]; repeat destruct decide;
    try reflexivity; exfalso;
    rewrite ?elem_of_set_swap, ?swap_involutive in *; set_solver.
Qed.

Lemma lstore_on_empty_dom_eq D (s1 s2 : LStoreOn (V := value) D) :
  D = ∅ -> s1 = s2.
Proof.
  intros HD. apply lstore_on_ext.
  pose proof (lso_dom s1) as H1. pose proof (lso_dom s2) as H2.
  rewrite HD in H1, H2.
  change (dom (lso_store s1 : gmap logic_var value) = ∅) in H1.
  change (dom (lso_store s2 : gmap logic_var value) = ∅) in H2.
  apply dom_empty_inv_L in H1. apply dom_empty_inv_L in H2.
  change ((lso_store s1 : gmap logic_var value) = lso_store s2).
  rewrite H1, H2. reflexivity.
Qed.

Lemma only_nu_cases q :
  qual_only_nu q ->
  qual_vars q = ∅ \/ qual_vars q = {[LVBound 0]}.
Proof.
  intros Honly.
  destruct (decide (LVBound 0 ∈ qual_vars q)) as [Hin|Hnin].
  - right. apply set_eq. intros v. split.
    + intros Hv. apply Honly in Hv. set_solver.
    + intros Hv. apply elem_of_singleton in Hv. subst. exact Hin.
  - left. apply set_eq. intros v. split; [|set_solver].
    intros Hv. pose proof (Honly v Hv). subst. contradiction.
Qed.

(** Under-approximation is antitone in the qualifier only when the target
    qualifier is satisfiable and does not mention more variables than the
    source qualifier (see the counterexamples in the report). *)
Lemma under_atom_open_closed (q1 q2 : type_qualifier) (y : atom) (my : WfWorldT) :
  qual_only_nu q1 -> qual_only_nu q2 ->
  qual_vars q2 ⊆ qual_vars q1 ->
  qualifier_entails q2 q1 ->
  (exists s, qual_prop q2 s) ->
  y ∈ world_dom (my : WorldT) ->
  my ⊨ FUnder (FAtom (qual_open_atom 0%nat y q1)) ->
  my ⊨ FUnder (FAtom (qual_open_atom 0%nat y q2)).
Proof.
  intros Hq1 Hq2 Hvars Hent [s0 Hs0] Hy Hunder.
  pose proof (qual_only_nu_open_lc q2 y Hq2) as Hlc2.
  pose proof (qual_only_nu_open_fv q2 y Hq2) as Hfv2.
  destruct (only_nu_cases q2 Hq2) as [Hempty|Hfull].
  - (* q2 does not mention ν: it is a satisfiable constant *)
    destruct q2 as [D2 P2]. cbn [qual_vars qual_lvars qual_prop] in *.
    cbn [qual_open_atom].
    destruct (world_wf my) as [[σ0 Hσ0] _].
    assert (Hsub0 : lvars_fv (lvars_open 0%nat y D2) ⊆ dom (σ0 : StoreT)).
    { pose proof (wfworld_store_dom my σ0 Hσ0) as Hd.
      change (dom (σ0 : gmap atom value) = world_dom (my : WorldT)) in Hd.
      change (lvars_fv (lvars_open 0%nat y D2) ⊆ dom (σ0 : gmap atom value)).
      rewrite Hd. set_solver. }
    assert (Hopen_empty : lvars_open 0%nat y D2 = ∅).
    { rewrite Hempty. apply set_eq. intros v. rewrite elem_of_set_swap. set_solver. }
    apply res_models_under_FAtom_intro.
    + exact Hlc2.
    + set_solver.
    + exists σ0. split; [exact Hσ0|]. exists Hlc2, Hsub0.
      replace (lstore_on_open_back 0 y D2
        (lstore_on_lift_store (lvars_open 0%nat y D2) σ0 Hlc2 Hsub0)) with s0;
        [exact Hs0|].
      apply lstore_on_empty_dom_eq. exact Hempty.
    + intros s _. exists σ0, Hσ0, Hlc2, Hsub0.
      apply lstore_on_empty_dom_eq. exact Hopen_empty.
  - (* q2 mentions ν, hence so does q1 and both live on {ν} *)
    destruct (only_nu_cases q1 Hq1) as [Hempty1|Hfull1].
    { exfalso. rewrite Hfull, Hempty1 in Hvars. set_solver. }
    destruct q1 as [D1 P1], q2 as [D2 P2].
    cbn [qual_vars qual_lvars qual_prop] in *.
    subst D1 D2.
    unfold qualifier_entails in Hent. cbn [qual_vars qual_lvars qual_prop] in Hent.
    cbn [qual_open_atom] in *.
    apply res_models_under_FAtom_inv in Hunder
      as [_ [_ [_ Hcov1]]].
    assert (Hcov2 : forall s, P2 (lstore_on_open_back 0 y {[LVBound 0]} s) ->
      exists σ (Hσ : (my : WorldT) σ) Hlc Hsubσ,
        s = lstore_on_lift_store _ σ Hlc Hsubσ).
    {
      intros s Hs. apply Hcov1.
      set (t := lstore_on_open_back 0 y {[LVBound 0]} s) in *.
      assert (Hsubj : ({[LVBound 0]} ∪ {[LVBound 0]} : lvset) ⊆ {[LVBound 0]})
        by set_solver.
      set (j := lstore_on_restrict _ t Hsubj).
      specialize (Hent j).
      assert (Hj : forall H, lstore_on_restrict {[LVBound 0]} j H = t).
      { intros H. apply lstore_on_ext.
        unfold j, lstore_on_restrict, storeA_on_restrict.
        destruct t as [st Hst]. cbn [lso_store storeAO_store].
        rewrite storeA_restrict_twice_subset by set_solver.
        apply storeA_restrict_idemp_eq. exact Hst. }
      rewrite !Hj in Hent. exact (Hent Hs).
    }
    apply res_models_under_FAtom_intro.
    + exact Hlc2.
    + set_solver.
    + set (s0' := lstore_on_open_front 0 y s0).
      assert (Hs0' : P2 (lstore_on_open_back 0 y {[LVBound 0]} s0')).
      { unfold s0'. rewrite lstore_on_open_back_front. exact Hs0. }
      destruct (Hcov2 s0' Hs0') as [σ [Hσ [Hlc [Hsubσ Heq]]]].
      exists σ. split; [exact Hσ|]. exists Hlc, Hsubσ.
      rewrite <- Heq. exact Hs0'.
    + exact Hcov2.
Qed.

Lemma lstore_on_open_front_restrict_back_store D E (HD : D ⊆ E) (y : atom)
    (s : LStoreOn (V := value) (lvars_open 0%nat y E)) :
  E ⊆ D ->
  lso_store (lstore_on_open_front 0 y
    (lstore_on_restrict D (lstore_on_open_back 0 y E s) HD)) = lso_store s.
Proof.
  intros HED.
  destruct s as [st Hst].
  unfold lstore_on_open_front, lstore_on_restrict, storeA_on_restrict,
    lstore_on_open_back, lso_store.
  cbn [storeAO_store].
  unfold lstore_swap, lstore_rekey. apply storeA_map_eq. intros z.
  pose proof (swap_inj (LVBound 0) (LVFree y)) as Hinj.
  set (w := swap (LVBound 0) (LVFree y) z).
  assert (Hz : z = swap (LVBound 0) (LVFree y) w)
    by (subst w; symmetry; apply swap_involutive).
  rewrite Hz at 1. rewrite (lookup_kmap (swap (LVBound 0) (LVFree y))).
  unfold storeA_restrict, map_restrict; rewrite map_lookup_filter.
  unfold w. rewrite (lookup_kmap (swap (LVBound 0) (LVFree y))).
  destruct (st !! z) as [v|] eqn:Hsz; cbn; [|reflexivity].
  rewrite option_guard_True; [reflexivity|].
  apply elem_of_dom_2 in Hsz. rewrite Hst, elem_of_set_swap in Hsz. set_solver.
Qed.

Lemma under_atom_open_and (qo qu : type_qualifier) (y : atom) (my : WfWorldT) :
  qual_vars qo ⊆ qual_vars qu ->
  lc_lvars (lvars_open 0%nat y (qual_vars qo ∪ qual_vars qu)) ->
  lvars_fv (lvars_open 0%nat y (qual_vars qo ∪ qual_vars qu)) ⊆
    world_dom (my : WorldT) ->
  (forall σ, (my : WorldT) σ -> qualifier_holds_store (qual_open_atom 0%nat y qo) σ) ->
  my ⊨ FUnder (FAtom (qual_open_atom 0%nat y qu)) ->
  my ⊨ FUnder (FAtom (qual_open_atom 0%nat y (qual_and qo qu))).
Proof.
  destruct qo as [Do Po], qu as [Du Pu].
  cbn [qual_vars qual_lvars qual_and qual_open_atom qualifier_holds_store].
  intros Hvars Hlc Hsc Hover Hunder.
  apply res_models_under_FAtom_inv in Hunder
    as [HlcU [HscU [[σ0 [Hσ0 HholdsU]] HcovU]]].
  cbn [qualifier_holds_store] in HholdsU.
  apply res_models_under_FAtom_intro.
  - exact Hlc.
  - exact Hsc.
  - exists σ0. split; [exact Hσ0|].
    assert (Hsub0 : lvars_fv (lvars_open 0%nat y (Do ∪ Du)) ⊆ dom (σ0 : StoreT)).
    { pose proof (wfworld_store_dom my σ0 Hσ0) as Hd.
      change (dom (σ0 : gmap atom value) = world_dom (my : WorldT)) in Hd.
      change (lvars_fv (lvars_open 0%nat y (Do ∪ Du)) ⊆ dom (σ0 : gmap atom value)).
      rewrite Hd. exact Hsc. }
    exists Hlc, Hsub0.
    destruct (Hover σ0 Hσ0) as [HlcO [HsubO HPo]].
    destruct HholdsU as [HlcU' [HsubU HPu]].
    split.
    + erewrite lstore_on_restrict_open_back_lift. exact HPo.
    + erewrite lstore_on_restrict_open_back_lift. exact HPu.
  - intros s [_ HPu].
    match type of HPu with
    | Pu (lstore_on_restrict Du _ ?H) => set (HDu := H) in HPu; clearbody HDu
    end.
    set (su := lstore_on_open_front 0 y
      (lstore_on_restrict Du (lstore_on_open_back 0 y (Do ∪ Du) s) HDu)).
    assert (HPu' : Pu (lstore_on_open_back 0 y Du su)).
    { unfold su. rewrite lstore_on_open_back_front. exact HPu. }
    destruct (HcovU su HPu') as [σ [Hσ [HlcU' [HsubU' Heq]]]].
    assert (Hsubσ : lvars_fv (lvars_open 0%nat y (Do ∪ Du)) ⊆ dom (σ : StoreT)).
    { pose proof (wfworld_store_dom my σ Hσ) as Hd.
      change (dom (σ : gmap atom value) = world_dom (my : WorldT)) in Hd.
      change (lvars_fv (lvars_open 0%nat y (Do ∪ Du)) ⊆ dom (σ : gmap atom value)).
      rewrite Hd. exact Hsc. }
    exists σ, Hσ, Hlc, Hsubσ.
    apply lstore_on_ext.
    rewrite <- (lstore_on_open_front_restrict_back_store Du (Do ∪ Du)
      HDu y s ltac:(set_solver)).
    fold su. rewrite Heq.
    unfold lstore_on_lift_store, lso_store. cbn [storeAO_store].
    replace (Do ∪ Du) with Du by set_solver. reflexivity.
Qed.

Lemma under_open_body_empty_iff q y (my : WfWorldT) :
  qual_only_nu q ->
  my ⊨ under_open_body q y <-> my ⊨ FUnder (FAtom (qual_open_atom 0%nat y q)).
Proof.
  intros Honly. unfold under_open_body.
  rewrite (qual_only_nu_open_diff q y Honly).
  split; [apply res_models_fibvars_empty_elim|apply res_models_fibvars_empty_intro].
Qed.

Lemma qual_and_vars (qo qu : type_qualifier) :
  qual_vars (qual_and qo qu) = qual_vars qo ∪ qual_vars qu.
Proof. destruct qo, qu. reflexivity. Qed.

Lemma qual_only_nu_and qo qu :
  qual_only_nu qo -> qual_only_nu qu -> qual_only_nu (qual_and qo qu).
Proof.
  intros Ho Hu v. rewrite qual_and_vars. intros Hv.
  apply elem_of_union in Hv as [Hv|Hv]; [apply Ho|apply Hu]; exact Hv.
Qed.

Lemma ty_denote_base_forall_scope_transport (m : WfWorldT) A q1 (q2 : type_qualifier)
    (Ftgt : type_qualifier -> FormulaT) :
  qual_only_nu q2 ->
  (forall q, formula_fv (Ftgt q) = qual_dom q ∪ lvars_fv (qual_vars q ∖ {[LVBound 0]})) ->
  formula_scoped_in_world m (FForall (FImpl A q1)) ->
  formula_scoped_in_world m (FForall (FImpl A (Ftgt q2))).
Proof.
  intros Hq2 HF Hsc.
  rewrite formula_scoped_forall_iff, formula_scoped_impl_iff in Hsc |- *.
  destruct Hsc as [HA _]. split; [exact HA|].
  unfold formula_scoped_in_world. rewrite HF.
  pose proof (qual_only_nu_dom q2 Hq2) as Hdom2. unfold qual_dom in *.
  pose proof (lvars_fv_mono (qual_vars q2 ∖ {[LVBound 0]}) (qual_vars q2)
    ltac:(set_solver)).
  set_solver.
Qed.

Lemma formula_fv_under_body (q : type_qualifier) :
  formula_fv (FFibVars (qual_vars q ∖ {[LVBound 0]}) (FUnder (FAtom q))) =
  qual_dom q ∪ lvars_fv (qual_vars q ∖ {[LVBound 0]}).
Proof.
  rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
  unfold qual_dom. set_solver.
Qed.

(** Corrected version of [subtype_under_closed_by_qualifier]: the original
    statement is false (see report); we add that the target qualifier is
    satisfiable and mentions no variable the source qualifier does not. *)
Lemma subtype_under_closed_by_qualifier_corrected
    Σ Γ b q1 q2 :
  subtype_wf Σ Γ ([: b | q1 ]) ([: b | q2 ]) ->
  qual_dom q1 ## ctx_dom Γ ->
  qual_dom q2 ## ctx_dom Γ ->
  qualifier_entails q2 q1 ->
  qual_vars q2 ⊆ qual_vars q1 ->
  (exists s, qual_prop q2 s) ->
  extended_semantic_subtype Σ Γ
    ([: b | q1 ]) ([: b | q2 ]).
Proof.
  intros Hwf Hd1 Hd2 Hent Hvars Hsat.
  pose proof Hwf as [_ [Hwf1 [Hwf2 _]]].
  unfold under_ty in Hwf1, Hwf2. cbn [wf_context_ty_at] in Hwf1, Hwf2.
  pose proof (qual_only_nu_of_wf Γ q1 Hwf1 Hd1) as Hq1.
  pose proof (qual_only_nu_of_wf Γ q2 Hwf2 Hd2) as Hq2.
  apply ext_sub_type_of_pointwise; [exact Hwf|].
  intros e m _ Hm.
  unfold ty_denote, under_ty in *. cbn [cty_depth ty_denote_gas] in *.
  set (Σl := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hrel : relevant_env Σl (CTUnder b q2) e = relevant_env Σl (CTUnder b q1) e).
  { unfold relevant_env.
    rewrite (qual_only_nu_context_ty_lvars_under b q1 Hq1),
      (qual_only_nu_context_ty_lvars_under b q2 Hq2). reflexivity. }
  rewrite Hrel.
  apply res_models_and_iff in Hm as [Hg Hall].
  apply res_models_and_intro_from_models.
  - eapply ty_guard_transport; [reflexivity| |exact I|exact Hg].
    rewrite (qual_only_nu_context_ty_lvars_under b q2 Hq2). set_solver.
  - eapply res_models_forall_full_world_impl_map; [| |exact Hall].
    + eapply (ty_denote_base_forall_scope_transport m _ _ q2
        (fun q => FFibVars (qual_vars q ∖ {[LVBound 0]}) (FUnder (FAtom q))));
        [exact Hq2|apply formula_fv_under_body|].
      exact (res_models_scoped _ _ Hall).
    + exists ∅. intros y _ my Hdom Hres. split; [tauto|].
      assert (Hy1 : LVFree y ∉ qual_vars q1) by (intros Hb; apply Hq1 in Hb; discriminate).
      assert (Hy2 : LVFree y ∉ qual_vars q2) by (intros Hb; apply Hq2 in Hb; discriminate).
      rewrite !formula_open_under_self_body_normalize by assumption.
      assert (Hym : y ∈ world_dom (my : WorldT)) by (rewrite Hdom; set_solver).
      rewrite !under_open_body_empty_iff by assumption.
      apply under_atom_open_closed; assumption.
Qed.

(** Corrected version of [subtype_inter_over_under_to_under_and] (for
    context-independent qualifiers): the over qualifier must not mention [ν]
    unless the under qualifier does. *)
Lemma subtype_inter_over_under_to_under_and_corrected
    Σ Γ b q_over q_under :
  subtype_wf Σ Γ (({: b | q_over }) ⊓ ([: b | q_under ])) ([: b | qual_and q_over q_under ]) ->
  qual_dom q_over ## ctx_dom Γ ->
  qual_dom q_under ## ctx_dom Γ ->
  qual_vars q_over ⊆ qual_vars q_under ->
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ([: b | qual_and q_over q_under ]).
Proof.
  intros Hwf Hdo Hdu Hvars.
  pose proof Hwf as [_ [Hwfs [Hwft _]]].
  unfold over_ty, under_ty in Hwfs, Hwft. cbn [wf_context_ty_at] in Hwfs, Hwft.
  destruct Hwfs as [Hwfo [Hwfu _]].
  pose proof (qual_only_nu_of_wf Γ q_over Hwfo Hdo) as Hqo.
  pose proof (qual_only_nu_of_wf Γ q_under Hwfu Hdu) as Hqu.
  pose proof (qual_only_nu_and q_over q_under Hqo Hqu) as Hqa.
  apply ext_sub_type_of_pointwise; [exact Hwf|].
  intros e m _ Hm.
  pose proof (ty_denote_inter_elim_l _ _ _ _ _ Hm) as Hov.
  pose proof (ty_denote_inter_elim_r _ _ _ _ _ Hm) as Hun.
  clear Hm.
  unfold ty_denote, over_ty, under_ty in *. cbn [cty_depth ty_denote_gas] in *.
  set (Σl := atom_env_to_lty_env (erase_ctx Γ)) in *.
  set (qa := qual_and q_over q_under) in *.
  assert (Hrel_u : relevant_env Σl (CTUnder b q_under) e = relevant_env Σl (CTOver b q_over) e).
  { unfold relevant_env.
    rewrite (qual_only_nu_context_ty_lvars_over b q_over Hqo),
      (qual_only_nu_context_ty_lvars_under b q_under Hqu). reflexivity. }
  assert (Hrel_a : relevant_env Σl (CTUnder b qa) e = relevant_env Σl (CTOver b q_over) e).
  { unfold relevant_env.
    rewrite (qual_only_nu_context_ty_lvars_over b q_over Hqo),
      (qual_only_nu_context_ty_lvars_under b qa Hqa). reflexivity. }
  rewrite Hrel_u in Hun. rewrite Hrel_a.
  apply res_models_and_iff in Hov as [Hg Hallo].
  apply res_models_and_iff in Hun as [_ Hallu].
  apply res_models_and_intro_from_models.
  - eapply ty_guard_transport; [reflexivity| |exact I|exact Hg].
    rewrite (qual_only_nu_context_ty_lvars_under b qa Hqa). set_solver.
  - set (A := expr_result_formula_at
      (lvars_shift_from 0 (dom (relevant_env Σl (CTOver b q_over) e)))
      (tm_shift 0 e) (LVBound 0)) in *.
    assert (Hscope : formula_scoped_in_world m
      (FForall (FImpl A (FFibVars (qual_vars qa ∖ {[LVBound 0]}) (FUnder (FAtom qa)))))).
    { eapply (ty_denote_base_forall_scope_transport m _ _ qa
        (fun q => FFibVars (qual_vars q ∖ {[LVBound 0]}) (FUnder (FAtom q))));
        [exact Hqa|apply formula_fv_under_body|].
      exact (res_models_scoped _ _ Hallo). }
    destruct (res_models_forall_rev _ _ Hallo) as [Lo Hrevo].
    destruct (res_models_forall_rev _ _ Hallu) as [Lu Hrevu].
    eapply res_models_forall_rev_intro; [exact Hscope|].
    exists (Lo ∪ Lu). intros y Hy my Hdom Hres.
    pose proof (Hrevo y ltac:(clear - Hy; set_solver) my Hdom Hres) as Ho.
    pose proof (Hrevu y ltac:(clear - Hy; set_solver) my Hdom Hres) as Hu.
    assert (Hyo : LVFree y ∉ qual_vars q_over) by (intros Hb; apply Hqo in Hb; discriminate).
    assert (Hyu : LVFree y ∉ qual_vars q_under) by (intros Hb; apply Hqu in Hb; discriminate).
    assert (Hya : LVFree y ∉ qual_vars qa) by (intros Hb; apply Hqa in Hb; discriminate).
    rewrite formula_open_impl in Ho, Hu |- *.
    rewrite formula_open_over_self_body_normalize in Ho by exact Hyo.
    rewrite formula_open_under_self_body_normalize in Hu by exact Hyu.
    rewrite formula_open_under_self_body_normalize by exact Hya.
    assert (Hle : m ⊑ my) by (rewrite <- Hres; apply res_restrict_le).
    assert (Hymy : y ∈ world_dom (my : WorldT))
      by (rewrite Hdom; apply elem_of_union_r, elem_of_singleton; reflexivity).
    eapply res_models_impl_intro_future.
    + pose proof (formula_scoped_forall_open_res_le m my y _ Hscope Hle Hymy) as Hsc.
      rewrite formula_open_impl, formula_open_under_self_body_normalize in Hsc by exact Hya.
      exact Hsc.
    + intros my' Hle' HA.
      pose proof (res_models_impl_elim_future _ _ _ _ Hle' Ho HA) as Ho'.
      pose proof (res_models_impl_elim_future _ _ _ _ Hle' Hu HA) as Hu'.
      assert (Hym : y ∈ world_dom (my' : WorldT)).
      { apply (raw_le_dom _ _ Hle'). exact Hymy. }
      apply under_open_body_empty_iff; [exact Hqa|].
      apply under_open_body_empty_iff in Hu'; [|exact Hqu].
      pose proof (proj1 (over_open_body_store_iff q_over y my' Hqo Hym) Ho') as Ho''.
      unfold qa. apply under_atom_open_and.
      * exact Hvars.
      * rewrite <- qual_and_vars. apply qual_only_nu_open_lc. exact Hqa.
      * rewrite <- qual_and_vars.
        pose proof (qual_only_nu_open_fv qa y Hqa) as Hfv.
        clear - Hfv Hym. set_solver.
      * exact Ho''.
      * exact Hu'.
Qed.

Lemma subtype_inter_over_under_to_under_corrected
    Σ Γ b q_over q_under q_tgt :
  subtype_wf Σ Γ (({: b | q_over }) ⊓ ([: b | q_under ])) ([: b | q_tgt ]) ->
  qual_dom q_over ## ctx_dom Γ ->
  qual_dom q_under ## ctx_dom Γ ->
  qual_vars q_over ⊆ qual_vars q_under ->
  extended_semantic_subtype Σ Γ
    ([: b | qual_and q_over q_under ]) ([: b | q_tgt ]) ->
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ([: b | q_tgt ]).
Proof.
  intros Hwf Hdo Hdu Hvars Hsub.
  eapply extended_semantic_subtype_trans_proof; [|exact Hsub].
  apply subtype_inter_over_under_to_under_and_corrected; try assumption.
  destruct Hwf as [HΓ [Hsrc [_ _]]].
  destruct Hsub as [_ [Hand _]].
  split; [exact HΓ|]. split; [exact Hsrc|]. split; [exact Hand|].
  reflexivity.
Qed.

Lemma qual_only_nu_top : qual_only_nu qual_top.
Proof. intros v Hv. cbn in Hv. set_solver. Qed.

(** [FUnder (FAtom qual_top)] (after opening) holds in every world. *)
Lemma under_open_body_top_valid y (my : WfWorldT) :
  my ⊨ under_open_body qual_top y.
Proof.
  apply under_open_body_empty_iff; [exact qual_only_nu_top|].
  cbn [qual_top qual_open_atom].
  assert (Hopen : lvars_open 0%nat y (∅ : lvset) = ∅).
  { apply set_eq. intros v. rewrite elem_of_set_swap. set_solver. }
  assert (Hlc : lc_lvars (lvars_open 0%nat y (∅ : lvset))).
  { rewrite Hopen. intros v Hv. set_solver. }
  destruct (world_wf my) as [[σ0 Hσ0] _].
  assert (Hsub0 : lvars_fv (lvars_open 0%nat y (∅ : lvset)) ⊆ dom (σ0 : StoreT)).
  { rewrite Hopen. rewrite lvars_fv_empty. set_solver. }
  apply res_models_under_FAtom_intro.
  - exact Hlc.
  - rewrite Hopen, lvars_fv_empty. set_solver.
  - exists σ0. split; [exact Hσ0|]. exists Hlc, Hsub0. exact I.
  - intros s _. exists σ0, Hσ0, Hlc, Hsub0.
    apply lstore_on_empty_dom_eq. exact Hopen.
Qed.

(** FINDING (formal): in the Rocq denotation [U[b] = [: b | qual_top]] is
    the trivial under-approximate type: every over-approximate refinement of
    the same base type is a subtype of it.  In the paper, [[ν:b | ⊤]] is the
    strongest under type (all values reachable; "⊢ 1 : [ν:nat|⊤]" is ✗), so
    [{ν:nat | ν>0} <: [ν:nat | ⊤]] must fail there.  The paper's [[ν:nat|⊤]]
    corresponds to [[: ℕ | q_nonneg ν]] in the case-study vocabulary. *)
Lemma subtype_over_to_UTop_trivial Σ Γ b q :
  subtype_wf Σ Γ ({: b | q }) ([: b | qual_top ]) ->
  qual_dom q ## ctx_dom Γ ->
  extended_semantic_subtype Σ Γ ({: b | q }) ([: b | qual_top ]).
Proof.
  intros Hwf Hd.
  pose proof Hwf as [_ [Hwf1 _]].
  unfold over_ty in Hwf1. cbn [wf_context_ty_at] in Hwf1.
  pose proof (qual_only_nu_of_wf Γ q Hwf1 Hd) as Hq.
  apply ext_sub_type_of_pointwise; [exact Hwf|].
  intros e m _ Hm.
  unfold ty_denote, over_ty, under_ty in *. cbn [cty_depth ty_denote_gas] in *.
  set (Σl := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hrel : relevant_env Σl (CTUnder b qual_top) e = relevant_env Σl (CTOver b q) e).
  { unfold relevant_env.
    rewrite (qual_only_nu_context_ty_lvars_over b q Hq),
      (qual_only_nu_context_ty_lvars_under b qual_top qual_only_nu_top). reflexivity. }
  rewrite Hrel.
  apply res_models_and_iff in Hm as [Hg Hall].
  apply res_models_and_intro_from_models.
  - eapply ty_guard_transport; [reflexivity| |exact I|exact Hg].
    rewrite (qual_only_nu_context_ty_lvars_under b qual_top qual_only_nu_top). set_solver.
  - eapply res_models_forall_full_world_impl_map; [| |exact Hall].
    + eapply (ty_denote_base_forall_scope_transport m _ _ qual_top
        (fun q => FFibVars (qual_vars q ∖ {[LVBound 0]}) (FUnder (FAtom q))));
        [exact qual_only_nu_top|apply formula_fv_under_body|].
      exact (res_models_scoped _ _ Hall).
    + exists ∅. intros y _ my Hdom Hres. split; [tauto|].
      intros _.
      rewrite formula_open_under_self_body_normalize
        by (cbn; set_solver).
      apply under_open_body_top_valid.
Qed.

(** ** Public names of the proved generic checkpoints *)

Definition extended_semantic_subtype_trans := extended_semantic_subtype_trans_proof.
Definition subtype_vacuous_of_unmodelable_ctx := subtype_vacuous_of_unmodelable_ctx_proof.
Definition extended_semantic_subtype_inter_left := extended_semantic_subtype_inter_left_proof.
Definition extended_semantic_subtype_inter_right := extended_semantic_subtype_inter_right_proof.
Definition extended_semantic_subtype_inter_comm := extended_semantic_subtype_inter_comm_proof.
Definition subtype_inter_over_under_to_over_part := subtype_inter_over_under_to_over_part_proof.
Definition subtype_inter_over_under_to_over := subtype_inter_over_under_to_over_proof.
Definition subtype_over_closed_by_qualifier := subtype_over_closed_by_qualifier_proof.

(** The original statements of [subtype_under_closed_by_qualifier],
    [subtype_inter_over_under_to_under_and] and
    [subtype_inter_over_under_to_under] were FALSE (see the counterexamples in
    the header comment).  Use the [_corrected] versions above. *)

(** ** Figure 5.1 placeholder discipline

    Counterexample discipline:

    - Some tempting facts are false as [τsrc <: τtgt] rules.  For example,
      [O[Bool] <: {: Bool | false}] is false: a function that always returns
      [true] inhabits the source but not the target.
    - Whole-function shortcuts such as the May/May source type subsuming the
      paper target type are false.  The valid checkpoints are local,
      context-dependent operator/result subtypings.
    - The under-approximate examples rely on coverage produced by the concrete
      operator or branch result being typed.  Do not promote an arbitrary
      same-erasure function type to an under refinement. *)
