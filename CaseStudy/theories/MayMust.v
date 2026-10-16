(** * May/must case studies (paper §6, Figure 6) and Godefroid-style
      may/may, must/may programs

    For every program this file gives a [⊢ₓ] derivation (structural part
    fully proved) against the paper's intended context type, or — where that
    type is semantically false — documents a concrete counterexample
    (section FINDINGS) and derives the closest corrected type.  Semantic
    side conditions are separate lemmas named [<program>_obl_<what>]; the
    Admitted ones carry an informal semantic argument.  Paper [int] is
    translated to [ℕ].  The paper's angelic [[ν | ⊤]] is the shared
    [U[ℕ]] = [[ℕ | q_base_all ℕ]] ("every natural is reachable"); since
    round 2 the shared alias is faithful, so the round-1 workaround
    qualifier [q_nat_all] has been removed and every round-1 [_all] type is
    now an alias of the corresponding pre-existing [U[ℕ]]-based type.

    Round 2 also uses the new rules [EXT_CtxCase] (capability case split),
    which closes the "T-Match gap" of round 1: Figure 6(a) setting (2) and
    the pre-existing [must_inter_ref_ty] are now derived. *)

From Denotation Require Import Context TypeDenote TypeEquivCore TypePersistBase.
From ProofAutomation Require Import BasicTypeInfer ExtendedSubsumption ExtendedTypeInfer.
From ContextTyping Require Import Typing.
From ContextAlgebra Require Import ResourceInterface.
From ContextLogic Require Import FormulaSemantics FormulaConnectives.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

(** ** Generic semantic subtyping lemmas for [⊕] (fully proved, Qed)

    Proposed as shared helpers (ProofAutomation/ExtendedSubsumption.v).  They
    concern sums of closed over/under base types ("closed" = the qualifiers
    mention only [ν], i.e. are disjoint from the context):
    - [mm_sum_over_to_over]: [{b|q1} ⊕ {b|q2} <: {b|q}] if [q1 ⊨ q] and
      [q2 ⊨ q] (every result of each part satisfies [q]);
    - [mm_sum_over_under_to_under]: [{b|q1} ⊕ [b|q] <: [b|q]] (the second,
      non-empty part reaches all of [q]; [FUnder] is upward closed);
    - [mm_sum_over_comm]: [{b|q1} ⊕ {b|q2} <: {b|q2} ⊕ {b|q1}].
    The proofs open the [FForall] result binder, use the shared
    characterisations of [ret z] at closed over/under types
    ([ty_denote_gas_over/under_ret_fvar_self_body_iff],
    [over_open_body_store_iff], [res_models_under_FAtom_inv/intro]) and the
    store-level meaning of [res_sum]. *)

Section MayMustSumLemmas.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation StoreT := (Store (V := value)) (only parsing).

Lemma mm_ty_denote_gas_sum_eq gas Σ τ1 τ2 e :
  ty_denote_gas (S gas) Σ (CTSum τ1 τ2) e =
  FAnd (ty_guard_formula (relevant_env Σ (CTSum τ1 τ2) e) (CTSum τ1 τ2) e)
    (FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTSum τ1 τ2) e)))
          (tm_shift 0 e) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e) (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e) (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0)))))).
Proof. reflexivity. Qed.

Lemma mm_ty_denote_gas_over_eq gas Σ b φ e :
  ty_denote_gas (S gas) Σ (CTOver b φ) e =
  FAnd (ty_guard_formula (relevant_env Σ (CTOver b φ) e) (CTOver b φ) e)
    (FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b φ) e)))
          (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ))))).
Proof. reflexivity. Qed.

Lemma mm_ty_denote_gas_under_eq gas Σ b φ e :
  ty_denote_gas (S gas) Σ (CTUnder b φ) e =
  FAnd (ty_guard_formula (relevant_env Σ (CTUnder b φ) e) (CTUnder b φ) e)
    (FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTUnder b φ) e)))
          (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ))))).
Proof. reflexivity. Qed.

Lemma mm_lift_store_restrict_eq D (σ : StoreT) (X : aset) Hlc Hsub Hsub' :
  lvars_fv D ⊆ X ->
  lstore_on_lift_store D (store_restrict σ X) Hlc Hsub =
  lstore_on_lift_store D σ Hlc Hsub'.
Proof.
  intros HX.
  apply lstore_on_ext. unfold lstore_on_lift_store, lso_store. cbn [storeAO_store].
  rewrite <- (lstore_lift_free_restrict_fv_lvars_eq (store_restrict σ X) D).
  rewrite <- (lstore_lift_free_restrict_fv_lvars_eq σ D).
  rewrite storeA_restrict_twice_subset by exact HX. reflexivity.
Qed.

Lemma mm_qual_holds_store_restrict (q : type_qualifier) (σ : StoreT) (X : aset) :
  qualifier_holds_store q (store_restrict σ X) ->
  qualifier_holds_store q σ.
Proof.
  destruct q as [D P]. cbn [qualifier_holds_store].
  intros [Hlc [Hsub HP]].
  assert (Hsub' : lvars_fv D ⊆ dom (σ : StoreT)).
  { intros z Hz. pose proof (Hsub z Hz) as Hz'.
    change (z ∈ dom (storeA_restrict (σ : gmap atom value) X)) in Hz'.
    rewrite storeA_restrict_dom in Hz'. set_solver. }
  exists Hlc, Hsub'.
  assert (HX : lvars_fv D ⊆ X).
  { intros z Hz. pose proof (Hsub z Hz) as Hz'.
    change (z ∈ dom (storeA_restrict (σ : gmap atom value) X)) in Hz'.
    rewrite storeA_restrict_dom in Hz'. set_solver. }
  replace (lstore_on_lift_store D σ Hlc Hsub')
    with (lstore_on_lift_store D (store_restrict σ X) Hlc Hsub); [exact HP| ].
  apply lstore_on_ext. unfold lstore_on_lift_store, lso_store. cbn [storeAO_store].
  rewrite <- (lstore_lift_free_restrict_fv_lvars_eq (store_restrict σ X) D).
  rewrite <- (lstore_lift_free_restrict_fv_lvars_eq σ D).
  rewrite storeA_restrict_twice_subset by exact HX. reflexivity.
Qed.

Lemma mm_sum_over_to_over Σ Γ b q1 q2 q :
  subtype_wf Σ Γ (CTSum ({: b | q1 }) ({: b | q2 })) ({: b | q }) ->
  qual_dom q1 ## ctx_dom Γ ->
  qual_dom q2 ## ctx_dom Γ ->
  qual_dom q ## ctx_dom Γ ->
  qualifier_entails q1 q ->
  qualifier_entails q2 q ->
  extended_semantic_subtype Σ Γ (CTSum ({: b | q1 }) ({: b | q2 })) ({: b | q }).
Proof.
  intros Hwf Hd1 Hd2 Hd He1 He2.
  pose proof Hwf as [_ [Hwfs [Hwft _]]].
  unfold over_ty in Hwfs, Hwft. cbn [wf_context_ty_at] in Hwfs, Hwft.
  destruct Hwfs as [Hw1 [Hw2 _]].
  pose proof (qual_only_nu_of_wf Γ q1 Hw1 Hd1) as Hq1.
  pose proof (qual_only_nu_of_wf Γ q2 Hw2 Hd2) as Hq2.
  pose proof (qual_only_nu_of_wf Γ q Hwft Hd) as Hq.
  apply ext_sub_type_of_pointwise; [exact Hwf| ].
  intros e m _ Hm.
  unfold ty_denote, over_ty in *. cbn [cty_depth Nat.max] in *.
  rewrite mm_ty_denote_gas_sum_eq in Hm. rewrite mm_ty_denote_gas_over_eq.
  set (Σl := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hlv : context_ty_lvars (CTSum (CTOver b q1) (CTOver b q2)) = ∅).
  { pose proof (qual_only_nu_context_ty_lvars_over b q1 Hq1) as H1.
    pose proof (qual_only_nu_context_ty_lvars_over b q2 Hq2) as H2.
    unfold context_ty_lvars in *. cbn [context_ty_lvars_at] in *.
    rewrite H1, H2. set_solver. }
  assert (Hrel : relevant_env Σl (CTOver b q) e = relevant_env Σl (CTSum (CTOver b q1) (CTOver b q2)) e).
  { unfold relevant_env. rewrite Hlv, (qual_only_nu_context_ty_lvars_over b q Hq). reflexivity. }
  rewrite Hrel.
  apply res_models_and_iff in Hm as [Hg Hall].
  apply res_models_and_intro_from_models.
  { eapply ty_guard_transport; [reflexivity| |exact I|exact Hg].
    rewrite (qual_only_nu_context_ty_lvars_over b q Hq). set_solver. }
  eapply res_models_forall_full_world_impl_map; [ | |exact Hall].
  { pose proof (res_models_scoped _ _ Hall) as Hsc.
    rewrite formula_scoped_forall_iff, formula_scoped_impl_iff in Hsc |- *.
    destruct Hsc as [HA _]. split; [exact HA| ].
    unfold formula_scoped_in_world.
    rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    pose proof (qual_only_nu_dom q Hq) as Hdom2. unfold qual_dom in Hdom2.
    pose proof (lvars_fv_mono (qual_vars q ∖ {[LVBound 0]}) (qual_vars q)
      ltac:(set_solver)).
    set_solver. }
  set (Σg := relevant_env Σl (CTSum (CTOver b q1) (CTOver b q2)) e) in *.
  assert (HΣg : lty_env_closed Σg).
  { apply relevant_env_closed, atom_store_to_lvar_store_closed. }
  exists (lvars_fv (dom Σg)). intros y Hy my Hdom Hres. split; [tauto| ].
  assert (HyΣ : LVFree y ∉ dom Σg).
  { intros Hb. apply Hy. apply lvars_fv_elem. exact Hb. }
  assert (Hfv1 : y ∉ fv_cty (CTOver b q1)).
  { pose proof (qual_only_nu_context_ty_lvars_over b q1 Hq1) as H. unfold fv_cty. rewrite H, lvars_fv_empty. set_solver. }
  assert (Hfv2 : y ∉ fv_cty (CTOver b q2)).
  { pose proof (qual_only_nu_context_ty_lvars_over b q2 Hq2) as H. unfold fv_cty. rewrite H, lvars_fv_empty. set_solver. }
  assert (Hlc1 : lc_context_ty (CTOver b q1)).
  { eapply (wf_context_ty_at_lc 0 (dom (erase_ctx Γ))). cbn [wf_context_ty_at]. exact Hw1. }
  assert (Hlc2 : lc_context_ty (CTOver b q2)).
  { eapply (wf_context_ty_at_lc 0 (dom (erase_ctx Γ))). cbn [wf_context_ty_at]. exact Hw2. }
  rewrite formula_open_plus.
  rewrite (formula_open_ty_denote_gas_bind_ret_bvar0 y 1 Σg (CTOver b q1) HΣg HyΣ Hfv1 Hlc1).
  pose proof (formula_open_ty_denote_gas_bind_ret_bvar0 y 1 Σg (CTOver b q2) HΣg HyΣ Hfv2 Hlc2) as E2.
  change (erase_ty (CTOver b q2)) with (erase_ty (CTOver b q1)) in E2.
  rewrite E2.
  rewrite formula_open_over_self_body_normalize
    by (intros Hb; apply Hq in Hb; discriminate).
  intros Hplus.
  apply res_models_plus_iff in Hplus as (m1 & m2 & Hdef & Hle & H1 & H2).
  pose proof (ty_denote_gas_ret_fvar_world_dom _ _ _ _ _ H1) as Hy1.
  pose proof (ty_denote_gas_ret_fvar_world_dom _ _ _ _ _ H2) as Hy2.
  assert (HΣy : lty_env_closed (<[LVFree y := erase_ty (CTOver b q1)]> Σg)).
  { apply lty_env_closed_insert_free; exact HΣg. }
  assert (Hyq1 : y ∉ qual_dom q1) by (rewrite (qual_only_nu_dom q1 Hq1); apply not_elem_of_empty).
  assert (Hyq2 : y ∉ qual_dom q2) by (rewrite (qual_only_nu_dom q2 Hq2); apply not_elem_of_empty).
  destruct (proj1 (ty_denote_gas_over_ret_fvar_self_body_iff 0 _ b q1 y m1 HΣy Hyq1) H1)
    as [_ H1'].
  destruct (proj1 (ty_denote_gas_over_ret_fvar_self_body_iff 0 _ b q2 y m2 HΣy Hyq2) H2)
    as [_ H2'].
  clear H1 H2. rename H1' into H1. rename H2' into H2.
  assert (Hym : y ∈ world_dom (my : WorldT)) by (rewrite Hdom; clear; set_solver).
  rewrite over_open_body_store_iff in H1 by assumption.
  rewrite over_open_body_store_iff in H2 by assumption.
  apply over_open_body_store_iff; [exact Hq|exact Hym| ].
  intros σ Hσ.
  pose proof (res_restrict_eq_of_le _ _ Hle) as Hr.
  set (D := world_dom (res_sum m1 m2 Hdef : WorldT)) in *.
  assert (Hσ' : (res_sum m1 m2 Hdef : WorldT) (store_restrict σ D)).
  { rewrite <- Hr. cbn [res_restrict raw_world raw_worldA world_stores].
    exists σ. split; [exact Hσ|reflexivity]. }
  apply (mm_qual_holds_store_restrict _ σ D).
  destruct Hσ' as [Hσ'|Hσ'].
  - eapply qual_open_holds_entails; [exact He1| | |exact (H1 _ Hσ')].
    + apply qual_only_nu_open_lc. exact Hq.
    + pose proof (qual_only_nu_open_fv q y Hq) as Hf.
      rewrite (wfworld_store_dom m1 _ Hσ'). clear - Hf Hy1. set_solver.
  - eapply qual_open_holds_entails; [exact He2| | |exact (H2 _ Hσ')].
    + apply qual_only_nu_open_lc. exact Hq.
    + pose proof (qual_only_nu_open_fv q y Hq) as Hf.
      rewrite (wfworld_store_dom m2 _ Hσ'). clear - Hf Hy2. set_solver.
Qed.

Lemma mm_sum_over_under_to_under Σ Γ b q1 q :
  subtype_wf Σ Γ (CTSum ({: b | q1 }) ([: b | q ])) ([: b | q ]) ->
  qual_dom q1 ## ctx_dom Γ ->
  qual_dom q ## ctx_dom Γ ->
  extended_semantic_subtype Σ Γ (CTSum ({: b | q1 }) ([: b | q ])) ([: b | q ]).
Proof.
  intros Hwf Hd1 Hd.
  pose proof Hwf as [_ [Hwfs [Hwft _]]].
  unfold over_ty, under_ty in Hwfs, Hwft. cbn [wf_context_ty_at] in Hwfs, Hwft.
  destruct Hwfs as [Hw1 [Hw2 _]].
  pose proof (qual_only_nu_of_wf Γ q1 Hw1 Hd1) as Hq1.
  pose proof (qual_only_nu_of_wf Γ q Hwft Hd) as Hq.
  apply ext_sub_type_of_pointwise; [exact Hwf| ].
  intros e m _ Hm.
  unfold ty_denote, over_ty, under_ty in *. cbn [cty_depth Nat.max] in *.
  rewrite mm_ty_denote_gas_sum_eq in Hm. rewrite mm_ty_denote_gas_under_eq.
  set (Σl := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hlv : context_ty_lvars (CTSum (CTOver b q1) (CTUnder b q)) = ∅).
  { pose proof (qual_only_nu_context_ty_lvars_over b q1 Hq1) as H1.
    pose proof (qual_only_nu_context_ty_lvars_under b q Hq) as H2.
    unfold context_ty_lvars in *. cbn [context_ty_lvars_at] in *.
    rewrite H1, H2. set_solver. }
  assert (Hrel : relevant_env Σl (CTUnder b q) e = relevant_env Σl (CTSum (CTOver b q1) (CTUnder b q)) e).
  { unfold relevant_env. rewrite Hlv, (qual_only_nu_context_ty_lvars_under b q Hq). reflexivity. }
  rewrite Hrel.
  apply res_models_and_iff in Hm as [Hg Hall].
  apply res_models_and_intro_from_models.
  { eapply ty_guard_transport; [reflexivity| |exact I|exact Hg].
    rewrite (qual_only_nu_context_ty_lvars_under b q Hq). set_solver. }
  eapply res_models_forall_full_world_impl_map; [ | |exact Hall].
  { pose proof (res_models_scoped _ _ Hall) as Hsc.
    rewrite formula_scoped_forall_iff, formula_scoped_impl_iff in Hsc |- *.
    destruct Hsc as [HA _]. split; [exact HA| ].
    unfold formula_scoped_in_world.
    rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
    pose proof (qual_only_nu_dom q Hq) as Hdom2. unfold qual_dom in Hdom2.
    pose proof (lvars_fv_mono (qual_vars q ∖ {[LVBound 0]}) (qual_vars q)
      ltac:(set_solver)).
    set_solver. }
  set (Σg := relevant_env Σl (CTSum (CTOver b q1) (CTUnder b q)) e) in *.
  assert (HΣg : lty_env_closed Σg).
  { apply relevant_env_closed, atom_store_to_lvar_store_closed. }
  exists (lvars_fv (dom Σg)). intros y Hy my Hdom Hres. split; [tauto| ].
  assert (HyΣ : LVFree y ∉ dom Σg).
  { intros Hb. apply Hy. apply lvars_fv_elem. exact Hb. }
  assert (Hfv1 : y ∉ fv_cty (CTOver b q1)).
  { pose proof (qual_only_nu_context_ty_lvars_over b q1 Hq1) as H. unfold fv_cty. rewrite H, lvars_fv_empty. set_solver. }
  assert (Hfv2 : y ∉ fv_cty (CTUnder b q)).
  { pose proof (qual_only_nu_context_ty_lvars_under b q Hq) as H. unfold fv_cty. rewrite H, lvars_fv_empty. set_solver. }
  assert (Hlc1 : lc_context_ty (CTOver b q1)).
  { eapply (wf_context_ty_at_lc 0 (dom (erase_ctx Γ))). cbn [wf_context_ty_at]. exact Hw1. }
  assert (Hlc2 : lc_context_ty (CTUnder b q)).
  { eapply (wf_context_ty_at_lc 0 (dom (erase_ctx Γ))). cbn [wf_context_ty_at]. exact Hw2. }
  rewrite formula_open_plus.
  rewrite (formula_open_ty_denote_gas_bind_ret_bvar0 y 1 Σg (CTOver b q1) HΣg HyΣ Hfv1 Hlc1).
  pose proof (formula_open_ty_denote_gas_bind_ret_bvar0 y 1 Σg (CTUnder b q) HΣg HyΣ Hfv2 Hlc2) as E2.
  change (erase_ty (CTUnder b q)) with (erase_ty (CTOver b q1)) in E2.
  rewrite E2.
  rewrite formula_open_under_self_body_normalize
    by (intros Hb; apply Hq in Hb; discriminate).
  intros Hplus.
  apply res_models_plus_iff in Hplus as (m1 & m2 & Hdef & Hle & _ & H2).
  pose proof (ty_denote_gas_ret_fvar_world_dom _ _ _ _ _ H2) as Hy2.
  assert (HΣy : lty_env_closed (<[LVFree y := erase_ty (CTOver b q1)]> Σg)).
  { apply lty_env_closed_insert_free; exact HΣg. }
  assert (Hyq : y ∉ qual_dom q) by (rewrite (qual_only_nu_dom q Hq); apply not_elem_of_empty).
  destruct (proj1 (ty_denote_gas_under_ret_fvar_self_body_iff 0 _ b q y m2 HΣy Hyq) H2)
    as [_ H2'].
  clear H2. rename H2' into H2.
  assert (Hym : y ∈ world_dom (my : WorldT)) by (rewrite Hdom; clear; set_solver).
  apply under_open_body_empty_iff in H2; [ |exact Hq].
  apply under_open_body_empty_iff; [exact Hq| ].
  set (D := world_dom (res_sum m1 m2 Hdef : WorldT)) in *.
  assert (HD2 : world_dom (m2 : WorldT) = D).
  { subst D. cbn. symmetry. exact Hdef. }
  assert (Hlift : forall σ2, (m2 : WorldT) σ2 ->
     exists σ, (my : WorldT) σ /\ store_restrict σ D = σ2).
  { intros σ2 Hσ2. eapply res_le_store_lift; [exact Hle| ]. right. exact Hσ2. }
  assert (Hqfv : lvars_fv (qual_vars (qual_open_atom 0 y q)) ⊆ {[y]}).
  { rewrite qual_open_atom_vars. apply qual_only_nu_open_fv. exact Hq. }
  destruct (qual_open_atom 0 y q) as [Dq Pq] eqn:Eq.
  cbn [qual_vars] in Hqfv.
  apply res_models_under_FAtom_inv in H2 as (Hlcq & Hsubq & [σ0 [Hσ0 Hh0]] & Hcov).
  apply res_models_under_FAtom_intro.
  - exact Hlcq.
  - rewrite Hdom. intros z Hz. apply elem_of_union_r. apply Hqfv. exact Hz.
  - destruct (Hlift σ0 Hσ0) as [σ [Hσ Hr]]. exists σ. split; [exact Hσ| ].
    apply (mm_qual_holds_store_restrict _ σ D). rewrite Hr. exact Hh0.
  - intros s Hs. destruct (Hcov s Hs) as [σ2 [Hσ2 [Hlc' [Hsub2 ->]]]].
    destruct (Hlift σ2 Hσ2) as [σ [Hσ Hr]]. subst σ2.
    assert (Hsubσ : lvars_fv Dq ⊆ dom σ).
    { rewrite (wfworld_store_dom my σ Hσ), Hdom. intros z Hz. apply elem_of_union_r. apply Hqfv. exact Hz. }
    exists σ, Hσ, Hlc', Hsubσ.
    apply mm_lift_store_restrict_eq.
    rewrite <- HD2. intros z Hz. pose proof (Hqfv z Hz) as Hz'.
    apply elem_of_singleton in Hz'. subst z. exact Hy2.
Qed.

Lemma mm_sum_over_comm Σ Γ b q1 q2 :
  subtype_wf Σ Γ (CTSum ({: b | q1 }) ({: b | q2 })) (CTSum ({: b | q2 }) ({: b | q1 })) ->
  qual_dom q1 ## ctx_dom Γ ->
  qual_dom q2 ## ctx_dom Γ ->
  extended_semantic_subtype Σ Γ (CTSum ({: b | q1 }) ({: b | q2 }))
    (CTSum ({: b | q2 }) ({: b | q1 })).
Proof.
  intros Hwf Hd1 Hd2.
  pose proof Hwf as [_ [Hwfs [Hwft _]]].
  unfold over_ty in Hwfs, Hwft. cbn [wf_context_ty_at] in Hwfs, Hwft.
  destruct Hwfs as [Hw1 [Hw2 _]].
  pose proof (qual_only_nu_of_wf Γ q1 Hw1 Hd1) as Hq1.
  pose proof (qual_only_nu_of_wf Γ q2 Hw2 Hd2) as Hq2.
  apply ext_sub_type_of_pointwise; [exact Hwf| ].
  intros e m _ Hm.
  unfold ty_denote, over_ty in *. cbn [cty_depth Nat.max] in *.
  rewrite mm_ty_denote_gas_sum_eq in Hm |- *.
  set (Σl := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hrel : relevant_env Σl (CTSum (CTOver b q2) (CTOver b q1)) e =
                 relevant_env Σl (CTSum (CTOver b q1) (CTOver b q2)) e).
  { unfold relevant_env, context_ty_lvars. cbn [context_ty_lvars_at]. f_equal. set_solver. }
  rewrite Hrel.
  apply res_models_and_iff in Hm as [Hg Hall].
  apply res_models_and_intro_from_models.
  { eapply ty_guard_transport; [reflexivity| |cbn [context_ty_shape_ok erase_ty]; repeat split|exact Hg].
    unfold context_ty_lvars. cbn [context_ty_lvars_at]. set_solver. }
  eapply res_models_forall_full_world_impl_map; [ | |exact Hall].
  { pose proof (res_models_scoped _ _ Hall) as Hsc.
    rewrite formula_scoped_forall_iff, formula_scoped_impl_iff in Hsc |- *.
    destruct Hsc as [HA HB]. split; [exact HA| ].
    unfold formula_scoped_in_world in *.
    rewrite formula_fv_plus in HB |- *. set_solver. }
  exists ∅. intros y _ my Hdom Hres. split; [tauto| ].
  rewrite !formula_open_plus.
  intros Hplus.
  apply res_models_plus_iff in Hplus as (m1 & m2 & Hdef & Hle & H1 & H2).
  destruct (res_sum_comm_eq m1 m2 Hdef) as [Hdef' Heq].
  apply res_models_plus_iff. exists m2, m1, Hdef'.
  rewrite <- Heq. split; [exact Hle| ]. split; assumption.
Qed.

End MayMustSumLemmas.

Section MayMustExamples.

Definition g : atom := 1%positive.
Definition x : atom := 2%positive.
Definition y : atom := 3%positive.
Definition gx : atom := 4%positive.
Definition gy : atom := 5%positive.
Definition px : atom := 6%positive.
Definition py : atom := 7%positive.
Definition cond : atom := 8%positive.
Definition a : atom := 9%positive.

(** The paper examples use arithmetic and boolean binary operators.  These are
    core binary-operation terms in the case-study syntax layer. *)

Definition may_may_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let gx := g @ x in
        let gy := g @ y in
        let px := gx ⟨ < ⟩ vnat 0 in
        let py := gy ⟨ < ⟩ vnat 0 in
        px ⟨ || ⟩ py))).

Definition must_may_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let gx := g @ x in
        let gy := g @ y in
        let px := vnat 0 ⟨ ≤ ⟩ gx in
        let py := vnat 0 ⟨ ≤ ⟩ gy in
        px ⟨ && ⟩ py))).

Definition may_reach_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let cond := y ⟨ > ⟩ vnat 10 in
        if cond then
          let gx := g @ x in
          gx ⟨ + ⟩ vnat 1
        else
          x ⟨ + ⟩ vnat 1))).

Definition must_inter_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let a := g @ x in
        let cond := a ⟨ > ⟩ vnat 10 in
        if cond then
          ret vnat 3
        else
          ret a))).

(** Figure 6(b), paper-faithful: [f x = let a = g x in if a > 3 then 5 else 2].
    (The pre-existing [must_inter_program] above is a different program and
    is kept unchanged.) *)
Definition fig6b_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      let a := g @ x in
      let cond := a ⟨ > ⟩ vnat 3 in
      if cond then
        ret (vnat 5)
      else
        ret (vnat 2))).

Definition may_must_guard_program := may_may_program.

Definition may_may_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition may_reach_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ ℕ.

Lemma may_may_program_basic_type :
  ∅ ⊢ₑ may_may_program ⋮ may_may_basic_ty.
Proof.
  unfold may_may_program, may_may_basic_ty.
  basic_check.
Qed.

Lemma may_may_after_g_basic_type :
  <[g := nat_unary_fun_ty]> ∅ ⊢ₑ
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let gx := g @ x in
        let gy := g @ y in
        let px := gx ⟨ < ⟩ vnat 0 in
        let py := gy ⟨ < ⟩ vnat 0 in
        px ⟨ || ⟩ py)) ⋮ (ℕ →ᵦ ℕ →ᵦ 𝔹).
Proof. basic_check. Qed.

Lemma must_may_program_basic_type :
  ∅ ⊢ₑ must_may_program ⋮ may_may_basic_ty.
Proof.
  unfold must_may_program, may_may_basic_ty.
  basic_check.
Qed.

Lemma may_reach_program_basic_type :
  ∅ ⊢ₑ may_reach_program ⋮ may_reach_basic_ty.
Proof.
  unfold may_reach_program, may_reach_basic_ty.
  basic_check.
Qed.

Lemma fig6b_program_basic_type :
  ∅ ⊢ₑ fig6b_program ⋮ ((ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ).
Proof.
  unfold fig6b_program.
  basic_check.
Qed.

Lemma must_inter_program_basic_type :
  ∅ ⊢ₑ must_inter_program ⋮ may_reach_basic_ty.
Proof.
  unfold must_inter_program, may_reach_basic_ty.
  basic_check.
Qed.

(** Figure 5.1 context types, translated literally.  The programs above are
    closed functions taking [g] as their first argument, so each full program
    type is [g_summary -> f_summary]. *)

Definition q_nat_ge0 : type_qualifier :=
  q_nat_pred ν (fun n => 0%nat <= n).

Definition q_nat_gt0 : type_qualifier :=
  q_nat_pred ν (fun n => 0%nat < n).

Definition q_nat_ne0 : type_qualifier :=
  q_nat_pred ν (fun n => n <> 0%nat).

Definition q_nat_eq1 : type_qualifier :=
  q_nat_pred ν (fun n => n = 1%nat).

(** The paper's angelic [[ν : int | ⊤]] is the shared [U[ℕ]]
    ([under_ty ℕ (q_base_all ℕ)], CaseTypes): its qualifier mentions [ν], so
    [U[ℕ]] says that every natural number is reachable.  (In round 1 the
    shared [U[b]] was the TRIVIAL [under_ty b qual_top], finding F7, and this
    file used a local workaround [q_nat_all]; both are gone.) *)

Definition q_bin_lt_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_lt v1 v2.

Definition q_bin_le_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_le v1 v2.

Definition q_bin_or_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_or v1 v2.

Definition q_bin_and_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_and v1 v2.

Definition q_bin_plus_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_plus v1 v2.

Definition may_may_g_ty : context_ty :=
  O[ ℕ ] → {: ℕ | q_nat_ge0 }.

Definition may_may_f_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → {: 𝔹 | q_false }.

Definition may_may_ref_ty : context_ty :=
  may_may_g_ty → may_may_f_ty.

Definition must_may_g_ty : context_ty :=
  U[ ℕ ] → [: ℕ | q_nat_ge0 ].

Definition must_may_f_ty : context_ty :=
  U[ ℕ ] → U[ ℕ ] → [: 𝔹 | q_true ].

Definition must_may_ref_ty : context_ty :=
  must_may_g_ty → must_may_f_ty.

Definition may_reach_g_ty : context_ty :=
  O[ ℕ ] → {: ℕ | q_nat_ne0 }.

Definition may_reach_f_ty : context_ty :=
  U[ ℕ ] → U[ ℕ ] → [: ℕ | q_nat_eq1 ].

Definition may_reach_ref_ty : context_ty :=
  may_reach_g_ty → may_reach_f_ty.

Definition must_inter_g_ty : context_ty :=
  (O[ ℕ ] → {: ℕ | q_nat_gt0 }) ⊓
  (U[ ℕ ] → [: ℕ | q_nat_gt0 ]).

Definition must_inter_f_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → {: ℕ | q_nat_ge0 }.

Definition must_inter_ref_ty : context_ty :=
  must_inter_g_ty → must_inter_f_ty.

Definition comprehensive_inter_f_ty : context_ty :=
  (O[ ℕ ] ⊓ U[ ℕ ]) →
  (O[ ℕ ] ⊓ U[ ℕ ]) →
  (O[ ℕ ] ⊓ [: ℕ | q_nat_eq1 ]).

Lemma may_may_g_ty_wf :
  basic_context_ty ∅ may_may_g_ty.
Proof.
  unfold may_may_g_ty, q_nat_ge0.
  case_type_wf_syntax.
Qed.

Lemma may_may_ref_ty_wf :
  basic_context_ty ∅ may_may_ref_ty.
Proof.
  unfold may_may_ref_ty, may_may_g_ty, may_may_f_ty,
    q_nat_ge0, q_false.
  case_type_wf_syntax.
Qed.

Lemma must_may_ref_ty_wf :
  basic_context_ty ∅ must_may_ref_ty.
Proof.
  unfold must_may_ref_ty, must_may_g_ty, must_may_f_ty,
    q_nat_ge0, q_true.
  case_type_wf_syntax.
Qed.

Lemma may_reach_ref_ty_wf :
  basic_context_ty ∅ may_reach_ref_ty.
Proof.
  unfold may_reach_ref_ty, may_reach_g_ty, may_reach_f_ty,
    q_nat_ne0, q_nat_eq1.
  case_type_wf_syntax.
Qed.

Lemma must_inter_ref_ty_wf :
  basic_context_ty ∅ must_inter_ref_ty.
Proof.
  unfold must_inter_ref_ty, must_inter_g_ty, must_inter_f_ty,
    q_nat_gt0, q_nat_ge0.
  case_type_wf_syntax.
Qed.

Lemma comprehensive_inter_f_ty_wf :
  basic_context_ty ∅ comprehensive_inter_f_ty.
Proof.
  unfold comprehensive_inter_f_ty, q_nat_eq1.
  case_type_wf_syntax.
Qed.

(** ** Figure 6(a) types: the three "must-analysis settings"

    Paper (int):  g : x:{⊤} → {ν ≠ 0}
                  f : x:[ν = 0] → y:[0 ≤ ν ≤ 10] → [ν = 1].
    Translation to ℕ: [0 ≤ ν ≤ 10] becomes [ν ≤ 10]; [ν ≠ 0], [ν = 0],
    [ν = 1] are kept literally; the result of the then-branch, [g x + 1]
    with [g x ≠ 0], is [ν ≠ 1] (equivalently [ν ≥ 2] in ℕ). *)

Definition q_nat_eq0 : type_qualifier := q_nat_pred ν (fun n => n = 0%nat).
Definition q_nat_le10 : type_qualifier := q_nat_pred ν (fun n => n <= 10).
Definition q_nat_ne1 : type_qualifier := q_nat_pred ν (fun n => n <> 1%nat).
Definition q_nat_ge2 : type_qualifier := q_nat_pred ν (fun n => 2 <= n).

(** y ranges over exactly [0,10]: may and must at the same time. *)
Definition fig6a_y_exact_ty : context_ty :=
  {: ℕ | q_nat_le10 } ⊓ [: ℕ | q_nat_le10 ].

(** Setting (1), the paper's literal type (entangled [→] for [y]). *)
Definition fig6a_f_ty_1 : context_ty :=
  [: ℕ | q_nat_eq0 ] → [: ℕ | q_nat_le10 ] → [: ℕ | q_nat_eq1 ].
Definition fig6a_ref_ty_1 : context_ty := may_reach_g_ty → fig6a_f_ty_1.

(** Setting (2): [y] independent from [x].  Semantically valid; derived in
    round 2 with [EXT_CtxCase] ([fig6a_2_typing]). *)
Definition fig6a_f_ty_2 : context_ty :=
  [: ℕ | q_nat_eq0 ] → ([: ℕ | q_nat_le10 ] -∗ [: ℕ | q_nat_eq1 ]).
Definition fig6a_ref_ty_2 : context_ty := may_reach_g_ty → fig6a_f_ty_2.

(** Corrected variants of (1)/(2) where [y] is exactly [0..10]: the
    then-branch is definitely unreachable, so no match split is needed. *)
Definition fig6a_f_ty_1a : context_ty :=
  [: ℕ | q_nat_eq0 ] → (fig6a_y_exact_ty → [: ℕ | q_nat_eq1 ]).
Definition fig6a_ref_ty_1a : context_ty := may_reach_g_ty → fig6a_f_ty_1a.
Definition fig6a_f_ty_2a : context_ty :=
  [: ℕ | q_nat_eq0 ] → (fig6a_y_exact_ty -∗ [: ℕ | q_nat_eq1 ]).
Definition fig6a_ref_ty_2a : context_ty := may_reach_g_ty → fig6a_f_ty_2a.

(** Variant of (2) where both branches are definitely reachable
    ([y : [⊤]] = [U[ℕ]], every natural is reachable); the then-branch is
    typed with the may-summary of [g]. *)
Definition fig6a_f_ty_2c_sum : context_ty :=
  [: ℕ | q_nat_eq0 ] → (U[ ℕ ] -∗ ({: ℕ | q_nat_ne1 } ⊕ [: ℕ | q_nat_eq1 ])).
Definition fig6a_ref_ty_2c_sum : context_ty := may_reach_g_ty → fig6a_f_ty_2c_sum.
Definition fig6a_f_ty_2c : context_ty :=
  [: ℕ | q_nat_eq0 ] → (U[ ℕ ] -∗ [: ℕ | q_nat_eq1 ]).
Definition fig6a_ref_ty_2c : context_ty := may_reach_g_ty → fig6a_f_ty_2c.

(** Setting (3): precise dependency of [y] on [x] (the reviewer's
    counterexample): [(x = 0 ⟹ ν = 12) ∧ (x > 0 ⟹ 0 ≤ ν ≤ 10)].  In the
    type, [x] is the de Bruijn index 1 inside [y]'s refinement; [x:[⊤]] is
    the (now faithful) shared [U[ℕ]]. *)
Definition q_fig6a_y3 (vx : value) : type_qualifier :=
  tqual (lvar_value_keys ν ∪ lvar_value_keys vx)
    (fun σ => exists nx ny,
       denote_lvar_value (lso_store σ) vx = Some (vconst (cnat nx)) /\
       denote_lvar_value (lso_store σ) ν = Some (vconst (cnat ny)) /\
       (nx = 0%nat -> ny = 12%nat) /\ (0 < nx -> ny <= 10)).
Definition fig6a_res_ty_3 : context_ty :=
  {: ℕ | q_nat_ne1 } ⊕ [: ℕ | q_nat_ge2 ].
Definition fig6a_f_ty_3 : context_ty :=
  U[ ℕ ] → ([: ℕ | q_fig6a_y3 (vbvar 1) ] → fig6a_res_ty_3).
Definition fig6a_ref_ty_3 : context_ty := may_reach_g_ty → fig6a_f_ty_3.

(** ** Figure 6(b) and [must_inter_program] types

    Since round 2 the pre-existing summary [must_inter_g_ty]
    ([x:{⊤} → {ν>0} ⊓ x:[⊤] → [ν>0]]) is the paper's summary verbatim
    ([U[ℕ]] is faithful). *)

Definition q_eq_nat (n : nat) : type_qualifier := mk_q_eq ν (vconst (cnat n)).
Definition q_nat_1to10 : type_qualifier :=
  q_nat_pred ν (fun n => 1 <= n /\ n <= 10).

(** Paper (int): [x:{⊤} → {ν = 2} ⊕ {ν = 5}].  Literal translation.
    Semantically FALSE (F4). *)
Definition fig6b_f_ty_paper : context_ty :=
  O[ ℕ ] → ({: ℕ | q_eq_nat 2 } ⊕ {: ℕ | q_eq_nat 5 }).
Definition fig6b_ref_ty_paper : context_ty := must_inter_g_ty → fig6b_f_ty_paper.

(** Corrected: the argument must be angelic ([x:[⊤]] = [U[ℕ]]), otherwise
    [a = g x] need not reach both sides of [a > 3]. *)
Definition fig6b_f_ty : context_ty :=
  U[ ℕ ] → ({: ℕ | q_eq_nat 2 } ⊕ {: ℕ | q_eq_nat 5 }).
Definition fig6b_ref_ty : context_ty := must_inter_g_ty → fig6b_f_ty.

(** Strongest type produced by T-Match (branch order, precise constants). *)
Definition fig6b_f_ty_precise : context_ty :=
  U[ ℕ ] → (const_precise_ty (cnat 5) ⊕ const_precise_ty (cnat 2)).
Definition fig6b_ref_ty_precise : context_ty :=
  must_inter_g_ty → fig6b_f_ty_precise.

(** [must_inter_program] with a must-argument [x:[⊤]]: the then-branch is
    reachable ([a] reaches 11) and the else-branch returns exactly the
    values [1..10], all of them reachable. *)
Definition must_inter_f_ty_must : context_ty :=
  U[ ℕ ] → O[ ℕ ] →
    (const_precise_ty (cnat 3) ⊕ ({: ℕ | q_nat_1to10 } ⊓ [: ℕ | q_nat_1to10 ])).
Definition must_inter_ref_ty_must : context_ty :=
  must_inter_g_ty → must_inter_f_ty_must.

(** The pre-existing [may_reach_ref_ty] ([x:[⊤] → y:[⊤] → [ν = 1]]) is
    not sound (see the FINDINGS section); its independent version is: *)
Definition may_reach_f_ty_star : context_ty :=
  U[ ℕ ] → (U[ ℕ ] -∗ [: ℕ | q_nat_eq1 ]).
Definition may_reach_ref_ty_star : context_ty :=
  may_reach_g_ty → may_reach_f_ty_star.

(** ** Round-1 [_all] names (now aliases)

    In round 1 the shared [U[ℕ]] was trivial (F7) and this file added
    "faithful" copies of the [U[ℕ]]-based targets using a local qualifier
    [q_nat_all].  With the faithful shared [U[ℕ]] these copies coincide
    with the pre-existing definitions; the names are kept as aliases. *)
Definition must_may_g_ty_all : context_ty := must_may_g_ty.
Definition must_may_f_ty_all : context_ty := must_may_f_ty.
Definition must_may_ref_ty_all : context_ty := must_may_ref_ty.
Definition must_inter_g_ty_all : context_ty := must_inter_g_ty.
Definition fig6b_ref_ty_paper_all : context_ty := fig6b_ref_ty_paper.
Definition fig6b_f_ty_all : context_ty := fig6b_f_ty.
Definition fig6b_ref_ty_all : context_ty := fig6b_ref_ty.
Definition must_inter_f_ty_must_all : context_ty := must_inter_f_ty_must.
Definition must_inter_ref_ty_must_all : context_ty := must_inter_ref_ty_must.

(** The pre-existing [comprehensive_inter_f_ty]
    [x:({⊤} ⊓ [⊤]) → y:({⊤} ⊓ [⊤]) → ({⊤} ⊓ [ν = 1])] has two [ℕ]
    arguments and an [ℕ] result, so it fits [must_inter_program] (with
    [g : must_inter_g_ty]) and [may_reach_program] (with
    [g : may_reach_g_ty]).  With [must_inter_program] it is derivable
    (the else branch returns [a = g x], and [a] reaches [1]); with
    [may_reach_program] it is FALSE (F8). *)
Definition comprehensive_inter_ref_ty : context_ty :=
  must_inter_g_ty → comprehensive_inter_f_ty.
Definition comprehensive_inter_f_ty_all : context_ty := comprehensive_inter_f_ty.
Definition comprehensive_inter_ref_ty_all : context_ty := comprehensive_inter_ref_ty.
Definition comprehensive_reach_ref_ty : context_ty :=
  may_reach_g_ty → comprehensive_inter_f_ty.
Definition comprehensive_reach_ref_ty_all : context_ty := comprehensive_reach_ref_ty.

(** ** Local typing infrastructure

    Everything in this section is generic.  The structural helpers
    ([mm_var], [mm_var_sub], [mm_app]) are plain compositions of the
    [⊢ₓ] rules.  [mm_ctx_sub_proj] is a fully proved semantic lemma: a
    closed binding that occurs anywhere in a [,,]/[∗] tree can be projected
    out of the context by T-CtxSub.  [mm_subtype_over_entails] is the only
    local semantic principle that is assumed (see its comment); it is
    proposed for [ProofAutomation/ExtendedSubsumption.v]. *)

Inductive mm_binds (z : atom) (τ : context_ty) : ctx -> Prop :=
| mm_binds_here : mm_binds z τ (CtxBind z τ)
| mm_binds_comma_l Γ1 Γ2 : mm_binds z τ Γ1 -> mm_binds z τ (CtxComma Γ1 Γ2)
| mm_binds_comma_r Γ1 Γ2 : mm_binds z τ Γ2 -> mm_binds z τ (CtxComma Γ1 Γ2)
| mm_binds_star_l Γ1 Γ2 : mm_binds z τ Γ1 -> mm_binds z τ (CtxStar Γ1 Γ2)
| mm_binds_star_r Γ1 Γ2 : mm_binds z τ Γ2 -> mm_binds z τ (CtxStar Γ1 Γ2).

#[local] Hint Constructors mm_binds : core.

Lemma mm_ctx_denote_bind_closed_env Σ z τ :
  fv_cty τ = ∅ ->
  ctx_denote_under Σ (CtxBind z τ) = ctx_denote_under ∅ (CtxBind z τ).
Proof.
  intros Hfv.
  rewrite (ctx_denote_under_minimal Σ), (ctx_denote_under_minimal ∅).
  cbn [ctx_fv]. rewrite Hfv.
  rewrite !storeA_restrict_empty_set. reflexivity.
Qed.

Lemma mm_binds_denote z τ Γ :
  mm_binds z τ Γ -> fv_cty τ = ∅ ->
  forall Σ (m : WfWorld), m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ctx_denote_under ∅ (CtxBind z τ).
Proof.
  induction 1; intros Hfv Σ m Hm.
  - rewrite <- (mm_ctx_denote_bind_closed_env Σ); assumption.
  - eapply IHmm_binds; [exact Hfv| ].
    eapply ctx_denote_under_comma_left. exact Hm.
  - cbn [ctx_denote_under] in Hm.
    rewrite res_models_and_iff in Hm. destruct Hm as [_ Hm].
    rewrite res_models_and_iff in Hm. destruct Hm as [_ Hm].
    eapply IHmm_binds; [exact Hfv|exact Hm].
  - apply ctx_denote_under_star_elim in Hm as (m1 & m2 & Hc & Hle & H1 & _).
    eapply res_models_kripke; [ |eapply IHmm_binds; [exact Hfv|exact H1]].
    etransitivity; [apply res_product_le_l|exact Hle].
  - apply ctx_denote_under_star_elim in Hm as (m1 & m2 & Hc & Hle & _ & H2).
    eapply res_models_kripke; [ |eapply IHmm_binds; [exact Hfv|exact H2]].
    etransitivity; [apply res_product_le_r|exact Hle].
Qed.

Lemma mm_formula_fv_ctx_bind_closed z τ :
  fv_cty τ = ∅ ->
  formula_fv (ctx_denote_under ∅ (CtxBind z τ)) ⊆ {[z]}.
Proof.
  intros Hfv.
  cbn [ctx_denote_under ctx_fv erase_ctx].
  rewrite formula_fv_and, formula_fv_basic_world_formula.
  rewrite Hfv, storeA_restrict_empty_set.
  intros w Hw. apply elem_of_union in Hw as [Hw|Hw].
  - rewrite lvars_fv_atom_env_to_lty_env_dom in Hw.
    apply elem_of_dom in Hw as [T HT].
    apply map_lookup_union_Some_raw in HT as [HT|[_ HT]];
      [rewrite lookup_empty in HT; discriminate| ].
    apply (proj1 (lookup_singleton_Some z w (erase_ty τ) T)) in HT as [-> _].
    set_solver.
  - unfold ty_denote in Hw.
    apply ty_denote_gas_fv_subset in Hw.
    cbn [fv_tm fv_value] in Hw. rewrite Hfv in Hw. set_solver.
Qed.

(** Projection of a closed binding (fully proved). *)
Lemma mm_ctx_sub_proj Σ Γ z τ X :
  wf_ctx_under Σ Γ ->
  wf_ctx_under Σ (CtxBind z τ) ->
  mm_binds z τ Γ ->
  fv_cty τ = ∅ ->
  erase_ctx Γ !! z = Some (erase_ty τ) ->
  X ⊆ {[z]} ->
  ctx_sub_under Σ X Γ (CtxBind z τ).
Proof.
  intros HΓ Hz Hbinds Hfv Hlook HX.
  split; [exact HΓ| ]. split; [exact Hz| ]. split.
  - intros w Hw. assert (w = z) as -> by set_solver.
    cbn [erase_ctx]. rewrite Hlook. symmetry.
    apply (proj2 (lookup_singleton_Some z z (erase_ty τ) (erase_ty τ))).
    split; reflexivity.
  - intros r Hr.
    exists (res_restrict r {[z]}).
    split; [apply res_restrict_mono; exact HX| ].
    rewrite (mm_ctx_denote_bind_closed_env Σ z τ Hfv).
    assert (HS : formula_fv (ctx_denote_under ∅ (CtxBind z τ)) ⊆ {[z]}).
    { apply mm_formula_fv_ctx_bind_closed. exact Hfv. }
    apply (proj1 (res_models_minimal_on _ r _ HS)).
    eapply mm_binds_denote; [exact Hbinds|exact Hfv|exact Hr].
Qed.

Lemma mm_ctx_emp_models Σ (m : WfWorld) : m ⊨ ctx_denote_under Σ Emp.
Proof.
  cbn [ctx_denote_under ctx_fv erase_ctx].
  rewrite storeA_restrict_empty_set.
  replace ((∅ : gmap atom ty) ∪ ∅) with (∅ : gmap atom ty)
    by (symmetry; apply map_empty_union).
  rewrite atom_store_to_lvar_store_empty.
  apply res_models_and_intro_from_models;
    [apply basic_world_formula_empty|apply res_models_true].
Qed.

(** Dropping the whole context (fully proved): used to type constants,
    whose rule T-Const lives in the empty context. *)
Lemma mm_ctx_sub_emp Σ Γ X :
  wf_ctx_under Σ Γ -> X = ∅ -> ctx_sub_under Σ X Γ Emp.
Proof.
  intros HΓ ->.
  split; [exact HΓ| ]. split; [exact I| ]. split.
  - intros w Hw. set_solver.
  - intros r _. exists (res_restrict r ∅).
    split; [apply res_restrict_mono; set_solver| ].
    apply mm_ctx_emp_models.
Qed.

(** Monotonicity of [ctx_sub_under] in the observed variable set (Qed). *)
Lemma mm_ctx_sub_under_mono Σ (X Y : aset) Γ1 Γ2 :
  ctx_sub_under Σ X Γ1 Γ2 -> Y ⊆ X -> ctx_sub_under Σ Y Γ1 Γ2.
Proof.
  intros [H1 [H2 [Hagree Hsub]]] HYX.
  split; [exact H1| ]. split; [exact H2| ]. split.
  - intros z Hz. apply Hagree. set_solver.
  - intros r Hr. destruct (Hsub r Hr) as [r' [Hle Hr']].
    exists r'. split; [ |exact Hr'].
    etransitivity; [apply res_restrict_mono; exact HYX|exact Hle].
Qed.

(** Structural helper: a constant in an arbitrary context, then T-Sub. *)
Lemma mm_const_sub Σ Γ c τ :
  Σ; Γ ⊢wf ret (vconst c) ⋮ τ ->
  Σ; Emp ⊢wf ret (vconst c) ⋮ τ ->
  Σ; Emp ⊢wf ret (vconst c) ⋮ const_precise_ty c ->
  ctx_sub_under Σ (fv_tm (ret (vconst c)) ∪ fv_cty τ) Γ Emp ->
  sub_type_under Σ Emp (const_precise_ty c) τ ->
  Σ; Γ ⊢ₓ ret (vconst c) ⋮ τ.
Proof.
  intros HwfΓ Hwf Hwfc Hctx Hsub.
  eapply EXT_CtxSub; [exact HwfΓ| |exact Hctx].
  eapply EXT_Sub; [exact Hwf| |exact Hsub].
  apply EXT_Const. exact Hwfc.
Qed.

Lemma mm_const Σ Γ c :
  Σ; Γ ⊢wf ret (vconst c) ⋮ const_precise_ty c ->
  Σ; Emp ⊢wf ret (vconst c) ⋮ const_precise_ty c ->
  ctx_sub_under Σ (fv_tm (ret (vconst c)) ∪ fv_cty (const_precise_ty c)) Γ Emp ->
  Σ; Γ ⊢ₓ ret (vconst c) ⋮ const_precise_ty c.
Proof.
  intros HwfΓ Hwf Hctx.
  eapply EXT_CtxSub; [exact HwfΓ| |exact Hctx].
  apply EXT_Const. exact Hwf.
Qed.

(** Structural helper: variable lookup = T-CtxSub followed by T-Var. *)
Lemma mm_var Σ Γ (z : atom) τ :
  Σ; Γ ⊢wf ret (avar z) ⋮ τ ->
  Σ; (z ∷ τ) ⊢wf ret (avar z) ⋮ τ ->
  ctx_sub_under Σ (fv_tm (ret (avar z)) ∪ fv_cty τ) Γ (z ∷ τ) ->
  Σ; Γ ⊢ₓ ret (avar z) ⋮ τ.
Proof.
  intros HwfΓ Hwfz Hsub.
  eapply EXT_CtxSub; [exact HwfΓ| |exact Hsub].
  apply EXT_Var. exact Hwfz.
Qed.

(** Structural helper: lookup at the declared type, then T-Sub inside the
    singleton context. *)
Lemma mm_var_sub Σ Γ (z : atom) τ τ' :
  Σ; Γ ⊢wf ret (avar z) ⋮ τ' ->
  Σ; (z ∷ τ) ⊢wf ret (avar z) ⋮ τ ->
  Σ; (z ∷ τ) ⊢wf ret (avar z) ⋮ τ' ->
  ctx_sub_under Σ (fv_tm (ret (avar z)) ∪ fv_cty τ') Γ (z ∷ τ) ->
  sub_type_under Σ (z ∷ τ) τ τ' ->
  Σ; Γ ⊢ₓ ret (avar z) ⋮ τ'.
Proof.
  intros HwfΓ Hwfz Hwfz' Hctx Hsub.
  eapply EXT_CtxSub; [exact HwfΓ| |exact Hctx].
  eapply EXT_Sub; [exact Hwfz'| |exact Hsub].
  apply EXT_Var. exact Hwfz.
Qed.

(** Structural helper: T-AppFun when the result type does not mention the
    argument (so [{0 ~> z} τ = τ]). *)
Lemma mm_app Σ Γ (f z : atom) τx τ :
  Σ; Γ ⊢wf f @ z ⋮ τ ->
  z ∉ fv_value (avar f) ∪ fv_cty τx ∪ fv_cty τ ->
  Σ; Γ ⊢ₓ ret (avar f) ⋮ (τx → τ) ->
  Σ; Γ ⊢ₓ ret (avar z) ⋮ τx ->
  Σ; Γ ⊢ₓ f @ z ⋮ τ.
Proof.
  intros Hwf Hfresh Hf Hz.
  assert (Hopen : cty_open 0 z τ = τ).
  { eapply (cty_open_above_lc_fresh 0 0 z τ); [lia| |set_solver].
    eapply wf_context_ty_at_lc.
    exact (context_typing_wf_context_ty Σ Γ _ τ Hwf). }
  pose proof (EXT_AppFun Σ Γ τx τ (avar f) z) as H.
  change (@open_one atom context_ty open_cty_atom_inst 0 z τ)
    with (cty_open 0 z τ) in H.
  rewrite Hopen in H. apply H; assumption.
Qed.

(** Helper for qualifier-entailment proofs. *)
Lemma mm_denote_restrict (D' D : lvset) (s : LStoreOn D) (H : D' ⊆ D) (v : value) :
  lvar_value_keys v ⊆ D' ->
  denote_lvar_value (lso_store (lstore_on_restrict D' s H)) v =
  denote_lvar_value (lso_store s) v.
Proof.
  intros Hv. destruct s as [s Hdom].
  destruct v; cbn [denote_lvar_value lvar_value_keys] in *; try reflexivity.
  all: unfold lso_store, lstore_on_restrict, storeA_on_restrict; cbn;
    rewrite (storeA_restrict_lookup s D');
    rewrite decide_True by set_solver; reflexivity.
Qed.

Ltac mm_qual_entails :=
  let s := fresh "s" in let H := fresh "Hq" in
  intros s H;
  cbn [qual_prop qual_vars] in *;
  repeat rewrite mm_denote_restrict in * by (cbn [lvar_value_keys]; set_solver).

(** Assumed generic principle (proposed shared lemma).

    Over-approximate refinements are covariant in the qualifier
    *pointwise*, even when the qualifiers mention context variables.
    Semantic argument (Rocq denotation): [ty_denote {b|q1} e] says that for
    every result fiber [ν] of [e] and every fiber [σ] over
    [qual_vars q1 ∖ {ν}], the projection of the fiber is contained in the
    [q1]-satisfying stores (FOver/FAtom with exact atoms means "projection ⊆
    q1-set", the witness superset being the fiber extended by all
    [q1]-stores).  Every store of the result world therefore satisfies [q1]
    on its own coordinates, hence (by [qualifier_entails q1 q2]) satisfies
    [q2]; regrouping the same stores by the fibers over
    [qual_vars q2 ∖ {ν}] gives FOver (FAtom q2) on each such fiber.  The
    guard part of the denotation is unchanged ([subtype_wf] gives the same
    erasure and well-formedness).  The existing
    [subtype_over_closed_by_qualifier] is the special case where both
    qualifiers are disjoint from the context; dropping that side condition
    is sound precisely because [FOver] is downward closed under taking
    sub-fibers. *)
Lemma mm_subtype_over_entails Σ Γ b q1 q2 :
  subtype_wf Σ Γ ({: b | q1 }) ({: b | q2 }) ->
  qualifier_entails q1 q2 ->
  extended_semantic_subtype Σ Γ ({: b | q1 }) ({: b | q2 }).
Proof. Admitted.

(** ** Tactics for the well-formedness side conditions *)

Lemma mm_erase_dom_subset Γ : dom (erase_ctx Γ) ⊆ ctx_dom Γ.
Proof.
  induction Γ; cbn [erase_ctx ctx_dom]; intros w Hw;
    apply elem_of_dom in Hw as [T HT].
  - rewrite lookup_empty in HT; discriminate.
  - apply (proj1 (lookup_singleton_Some _ w _ T)) in HT as [-> _]. set_solver.
  - apply map_lookup_union_Some_raw in HT as [HT|[_ HT]];
      apply elem_of_dom_2 in HT; set_solver.
  - apply map_lookup_union_Some_raw in HT as [HT|[_ HT]];
      apply elem_of_dom_2 in HT; set_solver.
  - apply elem_of_dom_2 in HT; set_solver.
Qed.

Lemma mm_erase_comma_bind Γ z τ :
  z ∉ ctx_dom Γ ->
  erase_ctx (Γ ,, (z ∷ τ)) = <[z := erase_ty τ]> (erase_ctx Γ).
Proof.
  intros Hz. apply erase_ctx_comma_bind_fresh.
  pose proof (mm_erase_dom_subset Γ). set_solver.
Qed.

Lemma mm_erase_star_bind Γ z τ :
  z ∉ ctx_dom Γ ->
  erase_ctx (Γ ∗ (z ∷ τ)) = <[z := erase_ty τ]> (erase_ctx Γ).
Proof.
  intros Hz.
  change (erase_ctx (Γ ∗ (z ∷ τ))) with (erase_ctx (Γ ,, (z ∷ τ))).
  apply mm_erase_comma_bind. exact Hz.
Qed.

Lemma mm_erase_emp_comma Γ : erase_ctx (Emp ,, Γ) = erase_ctx Γ.
Proof. cbn [erase_ctx]. apply map_empty_union. Qed.

Lemma mm_erase_bind z τ : erase_ctx (z ∷ τ) = <[z := erase_ty τ]> ∅.
Proof. cbn [erase_ctx]. symmetry. apply insert_empty. Qed.

Lemma mm_erase_sum Γ1 Γ2 : erase_ctx (Γ1 ⊕ Γ2) = erase_ctx Γ1.
Proof. reflexivity. Qed.

Ltac mm_unfold_tys :=
  unfold comprehensive_inter_ref_ty, comprehensive_inter_f_ty,
    comprehensive_inter_ref_ty_all, comprehensive_inter_f_ty_all,
    comprehensive_reach_ref_ty, comprehensive_reach_ref_ty_all,
    must_may_ref_ty_all, must_may_g_ty_all, must_may_f_ty_all,
    fig6b_ref_ty_paper_all, fig6b_ref_ty_all, fig6b_f_ty_all,
    must_inter_ref_ty_must_all, must_inter_f_ty_must_all,
    must_inter_g_ty_all in *;
  unfold may_may_ref_ty, may_may_g_ty, may_may_f_ty,
    must_may_ref_ty, must_may_g_ty, must_may_f_ty,
    may_reach_ref_ty, may_reach_g_ty, may_reach_f_ty,
    must_inter_ref_ty, must_inter_g_ty, must_inter_f_ty,
    fig6a_ref_ty_1, fig6a_f_ty_1, fig6a_ref_ty_2, fig6a_f_ty_2,
    fig6a_ref_ty_1a, fig6a_f_ty_1a, fig6a_ref_ty_2a, fig6a_f_ty_2a,
    fig6a_ref_ty_2c_sum, fig6a_f_ty_2c_sum, fig6a_ref_ty_2c, fig6a_f_ty_2c,
    fig6a_ref_ty_3, fig6a_f_ty_3, fig6a_res_ty_3, fig6a_y_exact_ty,
    q_nat_ge0, q_nat_gt0, q_nat_ne0, q_nat_eq1,
    q_bin_lt_result, q_bin_le_result, q_bin_or_result,
    q_bin_and_result, q_bin_plus_result,
    fig6b_ref_ty_paper, fig6b_f_ty_paper, fig6b_ref_ty, fig6b_f_ty,
    fig6b_ref_ty_precise, fig6b_f_ty_precise,
    must_inter_ref_ty_must, must_inter_f_ty_must,
    may_reach_ref_ty_star, may_reach_f_ty_star,
    q_nat_eq0, q_nat_le10, q_nat_ne1, q_nat_ge2, q_fig6a_y3,
    q_eq_nat, q_nat_1to10 in *.

Ltac mm_atoms := unfold g, x, y, gx, gy, px, py, cond, a in *.


Ltac mm_unfold_quals :=
  unfold primop_precise_ty, binop_precise_ty, binop_top_ty,
    precise_const, const_precise_ty, bool_precise_ty,
    precise_ty, over_ty, under_ty, primop_result_qual, binop_result_qual,
    q_nat_pred, q_base_all, q_const_pred, q_true, q_false, bool_qual, mk_q_eq, qual_top,
    vnu, avar, vnat, vbool in *.

Ltac mm_fv_norm :=
  mm_unfold_tys; mm_unfold_quals;
  unfold fv_cty, context_ty_lvars in *;
  cbn [context_ty_lvars_at qual_vars qual_lvars lvar_value_keys fv_value
       bin_op_type fv_tm Ret] in *;
  repeat first
    [ rewrite lvars_fv_lvars_at_depth in *
    | rewrite lvars_fv_union in *
    | rewrite lvars_fv_empty in *
    | rewrite lvars_fv_singleton_bound in *
    | rewrite lvars_fv_singleton_free in * ].

Ltac mm_fresh :=
  first [ solve [cbn [ctx_dom]; mm_atoms; set_solver]
        | solve [mm_fv_norm; mm_atoms; set_solver] ].

Ltac mm_erase_norm :=
  repeat first
    [ rewrite mm_erase_sum
    | rewrite mm_erase_emp_comma
    | rewrite mm_erase_comma_bind by mm_fresh
    | rewrite mm_erase_star_bind by mm_fresh
    | rewrite mm_erase_bind
    | change (erase_ctx Emp) with (∅ : gmap atom ty) ];
  cbn [erase_ty] in *.

Ltac mm_lvar_mem :=
  repeat match goal with
  | H : _ ∈ _ ∪ _ |- _ => apply elem_of_union in H as [H|H]
  | H : _ ∈ {[_]} |- _ => apply elem_of_singleton in H
  end;
  try solve [set_solver];
  try congruence;
  try solve [match goal with H : LVBound _ = LVBound _ |- _ => inversion H; subst end; lia];
  try solve [match goal with H : LVFree _ = LVFree _ |- _ => inversion H; subst end;
             apply elem_of_dom; eexists; basic_lookup].

Ltac mm_wf_type :=
  unfold primop_precise_ty, binop_precise_ty, binop_top_ty,
    precise_const, const_precise_ty, bool_precise_ty,
    precise_ty, over_ty, under_ty, primop_result_qual, binop_result_qual,
    q_nat_pred, q_base_all, q_const_pred, q_true, q_false, bool_qual, mk_q_eq, qual_top,
    vnu, avar, vnat, vbool in *;
  mm_erase_norm; mm_atoms;
  cbn [bin_op_type] in *;
  unfold basic_context_ty;
  cbn [wf_context_ty_at erase_ty qual_vars qual_lvars lvar_value_keys];
  repeat split; try reflexivity;
  intros [k|w] Hw; cbn [lvar_wf_at] in *; try lia;
  first [ solve [set_solver] | solve [mm_lvar_mem] ].

Ltac mm_wf_goal :=
  lazymatch goal with
  | |- _ ⊢ₑ _ ⋮ _ =>
      solve [mm_erase_norm;
             unfold over_ty, under_ty, precise_ty, bool_precise_ty,
               binop_precise_ty, const_precise_ty, precise_const in *;
             cbn [erase_ty bin_op_type] in *; basic_check]
  | |- wf_context_ty_at _ _ _ => solve [mm_wf_type]
  | |- basic_context_ty _ _ => solve [mm_wf_type]
  | |- erase_ctx _ = erase_ctx _ => solve [mm_erase_norm; reflexivity]
  | |- _ => solve [cbn [ctx_dom]; mm_atoms; set_solver]
  end.

Ltac mm_wf :=
  unfold context_typing_wf, wf_ctx_under; mm_unfold_tys;
  repeat split; try solve [mm_wf_goal].

Lemma mm_ctx_sub_proj' Σ Γ (z : atom) τ τ' :
  wf_ctx_under Σ Γ ->
  wf_ctx_under Σ (CtxBind z τ) ->
  mm_binds z τ Γ ->
  fv_cty τ = ∅ ->
  fv_cty τ' = ∅ ->
  erase_ctx Γ !! z = Some (erase_ty τ) ->
  ctx_sub_under Σ (fv_tm (ret (avar z)) ∪ fv_cty τ') Γ (CtxBind z τ).
Proof.
  intros HΓ Hz Hb Hfv Hfv' Hl.
  apply mm_ctx_sub_proj; try assumption.
  rewrite Hfv'. cbn [fv_tm fv_value Ret avar]. set_solver.
Qed.

Ltac mm_fv0 := mm_fv_norm; set_solver.

Ltac mm_lookup :=
  first [ vm_compute; reflexivity
        | mm_erase_norm; basic_lookup ].

Ltac mm_proj :=
  apply mm_ctx_sub_proj';
  [ mm_wf | mm_wf | solve [mm_unfold_tys; eauto 20] | mm_fv0 | mm_fv0 | mm_lookup ].

Ltac mm_var := eapply mm_var; [mm_wf | mm_wf | mm_proj].

Ltac mm_var_sub τdecl :=
  eapply (mm_var_sub _ _ _ τdecl); [mm_wf | mm_wf | mm_wf | mm_proj | ].

Ltac mm_const :=
  eapply mm_const; [mm_wf | mm_wf | apply mm_ctx_sub_emp; [mm_wf | mm_fv0]].

Ltac mm_subtype_wf :=
  unfold subtype_wf, wf_ctx_under; mm_unfold_tys;
  repeat split; try solve [mm_wf_goal].

(** ** Earlier local subtyping checkpoints (repaired)

    These standalone checkpoints predate the full derivations below and are
    not used by them.  They were repaired after the removal of
    [qual_and_idempotent] and the addition of [subtype_wf] premises.
    [p ≠ q] premises were added where two binders appear: for [p = q] the
    context is ill formed and [sub_type_under] is false. *)

Lemma may_may_lt_false_subtype z :
  extended_semantic_subtype ∅ (z ∷ {: ℕ | q_nat_ge0 })
    (({: 𝔹 | q_bin_lt_result (avar z) (vnat 0) }) ⊓
     ([: 𝔹 | q_bin_lt_result (avar z) (vnat 0) ]))
    ({: 𝔹 | q_false }).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ({: 𝔹 | q_bin_lt_result (avar z) (vnat 0) })).
  - apply subtype_inter_over_under_to_over_part. mm_subtype_wf.
  - apply mm_subtype_over_entails; [mm_subtype_wf| ].
    unfold q_bin_lt_result, binop_result_qual, q_false, bool_qual, mk_q_eq, avar, vnat.
    mm_qual_entails.
    destruct Hq as (c1 & c2 & c' & H1 & H2 & H3 & Hstep).
    rewrite H3. cbn [denote_lvar_value] in H2. inversion H2; subst.
    inversion Hstep; subst. destruct n; reflexivity.
Qed.

(** Context-dependent (same argument as [may_may_program_obl_result]). *)
Lemma may_may_or_false_false_subtype p q :
  p ≠ q ->
  extended_semantic_subtype ∅
    ((p ∷ {: 𝔹 | q_false }) ,, (q ∷ {: 𝔹 | q_false }))
    (({: 𝔹 | q_bin_or_result (avar p) (avar q) }) ⊓
     ([: 𝔹 | q_bin_or_result (avar p) (avar q) ]))
    ({: 𝔹 | q_false }).
Proof. Admitted.

(** Context-dependent: [z ∷ [ν ≥ 0]] is only used for non-emptiness; in ℕ
    [0 ≤ z] is always [true], and some [z]-fiber exists, so [true] is
    reached. *)
Lemma must_may_le_true_subtype z :
  extended_semantic_subtype ∅ (z ∷ [: ℕ | q_nat_ge0 ])
    (({: 𝔹 | q_bin_le_result (vnat 0) (avar z) }) ⊓
     ([: 𝔹 | q_bin_le_result (vnat 0) (avar z) ]))
    ([: 𝔹 | q_true ]).
Proof. Admitted.

(** FINDING: the earlier checkpoint
      [(p ∷ [𝔹 | ν = true]) ,, (q ∷ [𝔹 | ν = true]) ⊢
         {p && q} ⊓ [p && q] <: [𝔹 | ν = true]]
    is FALSE and has been removed: in the entangled context the world
    [{(p = true, q = false), (p = false, q = true)}] satisfies both
    bindings ([true] is reachable for [p] and for [q]) but [p && q] is
    always [false].  It holds with the independent context [∗], where the
    product world contains the pair [(true, true)]: *)
Lemma must_may_and_true_true_subtype_star p q :
  p ≠ q ->
  extended_semantic_subtype ∅
    ((p ∷ [: 𝔹 | q_true ]) ∗ (q ∷ [: 𝔹 | q_true ]))
    (({: 𝔹 | q_bin_and_result (avar p) (avar q) }) ⊓
     ([: 𝔹 | q_bin_and_result (avar p) (avar q) ]))
    ([: 𝔹 | q_true ]).
Proof. Admitted.

(** Context-dependent: [z ∷ U[ℕ]] (every natural reachable, faithful since
    round 2) makes the [z = 0] fiber inhabited, and on it the under part of
    the precise [+]-type reaches [1].  (In round 1, with the then-trivial
    [U[ℕ]], this checkpoint was FALSE: [{z = 5}] only gives [6].) *)
Lemma may_reach_else_plus_one_eq1_subtype z :
  extended_semantic_subtype ∅ (z ∷ U[ ℕ ])
    (({: ℕ | q_bin_plus_result (avar z) (vnat 1) }) ⊓
     ([: ℕ | q_bin_plus_result (avar z) (vnat 1) ]))
    ([: ℕ | q_nat_eq1 ]).
Proof. Admitted.

Lemma must_inter_g_over_projection_subtype :
  extended_semantic_subtype ∅ Emp
    ((O[ ℕ ] → {: ℕ | q_nat_gt0 }) ⊓
     (U[ ℕ ] → [: ℕ | q_nat_gt0 ]))
    (O[ ℕ ] → {: ℕ | q_nat_gt0 }).
Proof.
  apply extended_semantic_subtype_inter_left. mm_subtype_wf.
Qed.

Lemma must_inter_then_three_ge0_subtype :
  extended_semantic_subtype ∅ Emp
    (({: ℕ | mk_q_eq ν (vnat 3) }) ⊓
     ([: ℕ | mk_q_eq ν (vnat 3) ]))
    ({: ℕ | q_nat_ge0 }).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ({: ℕ | mk_q_eq ν (vnat 3) })).
  - apply subtype_inter_over_under_to_over_part. mm_subtype_wf.
  - apply subtype_over_closed_by_qualifier.
    + mm_subtype_wf.
    + unfold qual_dom, mk_q_eq, vnu, lvar_value_keys; cbn. set_solver.
    + unfold qual_dom, q_nat_ge0, q_nat_pred, q_const_pred,
        vnu, lvar_value_keys; cbn. set_solver.
    + unfold q_nat_ge0, q_nat_pred, q_const_pred, mk_q_eq, vnat.
      mm_qual_entails. rewrite Hq. exists (cnat 3). split; [reflexivity|cbn; lia].
Qed.

Lemma must_inter_else_gt0_ge0_subtype z :
  extended_semantic_subtype ∅ (z ∷ {: ℕ | q_nat_gt0 })
    ({: ℕ | q_nat_gt0 })
    ({: ℕ | q_nat_ge0 }).
Proof.
  apply subtype_over_closed_by_qualifier.
  - mm_subtype_wf.
  - unfold qual_dom; mm_fv_norm; cbn [ctx_dom]; set_solver.
  - unfold qual_dom; mm_fv_norm; cbn [ctx_dom]; set_solver.
  - unfold q_nat_gt0, q_nat_ge0, q_nat_pred, q_const_pred.
    mm_qual_entails. destruct Hq as [c [Hc Hp]]. exists c. split; [exact Hc| ].
    destruct c; try contradiction. lia.
Qed.

(** ** May/May (Godefroid-style): all-demonic summaries *)

Local Notation mm_may_may_ctx3 := (((Emp ,, (g ∷ may_may_g_ty)) ,, (x ∷ O[ ℕ ])) ,, (y ∷ O[ ℕ ])) (only parsing).

Local Notation mm_may_may_ctx4 := (mm_may_may_ctx3 ,, (gx ∷ {: ℕ | q_nat_ge0 })) (only parsing).
Local Notation mm_may_may_ctx5 := (mm_may_may_ctx4 ,, (gy ∷ {: ℕ | q_nat_ge0 })) (only parsing).
Local Notation mm_may_may_ctx6 := (mm_may_may_ctx5 ,, (px ∷ {: 𝔹 | q_false })) (only parsing).

Lemma may_may_program_obl_px :
  sub_type_under ∅ mm_may_may_ctx5
    (binop_precise_ty bop_lt (avar gx) (vnat 0)) ({: 𝔹 | q_false }).
Proof.
  unfold binop_precise_ty; cbn [bin_op_type].
  eapply extended_semantic_subtype_trans.
  - apply subtype_inter_over_under_to_over_part. mm_subtype_wf.
  - apply mm_subtype_over_entails; [mm_subtype_wf| ].
    unfold binop_result_qual, q_false, bool_qual, mk_q_eq, avar, vnat.
    mm_qual_entails.
    destruct Hq as (c1 & c2 & c' & H1 & H2 & H3 & Hstep).
    rewrite H3. cbn [denote_lvar_value] in H2. inversion H2; subst.
    inversion Hstep; subst. destruct n; reflexivity.
Qed.

Lemma may_may_program_obl_py :
  sub_type_under ∅ mm_may_may_ctx6
    (binop_precise_ty bop_lt (avar gy) (vnat 0)) ({: 𝔹 | q_false }).
Proof.
  unfold binop_precise_ty; cbn [bin_op_type].
  eapply extended_semantic_subtype_trans.
  - apply subtype_inter_over_under_to_over_part. mm_subtype_wf.
  - apply mm_subtype_over_entails; [mm_subtype_wf| ].
    unfold binop_result_qual, q_false, bool_qual, mk_q_eq, avar, vnat.
    mm_qual_entails.
    destruct Hq as (c1 & c2 & c' & H1 & H2 & H3 & Hstep).
    rewrite H3. cbn [denote_lvar_value] in H2. inversion H2; subst.
    inversion Hstep; subst. destruct n; reflexivity.
Qed.

(** Context-dependent obligation, stated for an arbitrary (well-formed)
    prefix [Γ0] since it only uses the last two bindings.  Informal
    argument: in every world [m] of the context the bindings
    [px ∷ {𝔹 | ν = false}] and [py ∷ {𝔹 | ν = false}] are
    over-approximations with closed qualifiers, so every store of [m] maps
    [px] and [py] to [false].  The over part of
    [binop_precise_ty bop_or px py] is fibered over [{px, py}]; the only
    inhabited fiber is [px = py = false], on which the result is
    [false || false = false].  Hence every result is [false], which is the
    denotation of [{𝔹 | ν = false}] (guards coincide: same erasure, both
    types well formed). *)
Lemma may_may_program_obl_result Γ0 :
  wf_ctx_under ∅ ((Γ0 ,, (px ∷ {: 𝔹 | q_false })) ,, (py ∷ {: 𝔹 | q_false })) ->
  sub_type_under ∅ ((Γ0 ,, (px ∷ {: 𝔹 | q_false })) ,, (py ∷ {: 𝔹 | q_false }))
    (binop_precise_ty bop_or (avar px) (avar py)) ({: 𝔹 | q_false }).
Proof. Admitted.

Theorem may_may_program_typing :
  ∅; Emp ⊢ₓ may_may_program ⋮ may_may_ref_ty.
Proof.
  unfold may_may_program, may_may_ref_ty, may_may_f_ty.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := {: ℕ | q_nat_ge0 }); [mm_wf| | ].
  { eapply mm_app with (τx := O[ ℕ ]); [mm_wf|mm_fresh| mm_var | mm_var]. }
  eapply EXT_LetNamed with (τ1 := {: ℕ | q_nat_ge0 }); [mm_wf| | ].
  { eapply mm_app with (τx := O[ ℕ ]); [mm_wf|mm_fresh| mm_var | mm_var]. }
  eapply EXT_LetNamed with (τ1 := {: 𝔹 | q_false }); [mm_wf| | ].
  { eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | exact may_may_program_obl_px]. }
  eapply EXT_LetNamed with (τ1 := {: 𝔹 | q_false }); [mm_wf| | ].
  { eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | exact may_may_program_obl_py]. }
  eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | ].
  apply may_may_program_obl_result. mm_wf.
Qed.


(** ** Must/May (Godefroid-style): angelic summaries

    Target [must_may_ref_ty] = [g:(x:[⊤] → [ν ≥ 0]) → x:[⊤] → y:[⊤] →
    [ν = true]], faithful since round 2.  The contexts are parameterised by
    the summary [τg] of [g] and the argument type [τa]. *)

Local Notation mm_must_may_ctx3 τg τa :=
  (((Emp ,, (g ∷ τg)) ,, (x ∷ τa)) ,, (y ∷ τa)) (only parsing).
Local Notation mm_must_may_ctx4 τg τa :=
  (mm_must_may_ctx3 τg τa ,, (gx ∷ [: ℕ | q_nat_ge0 ])) (only parsing).
Local Notation mm_must_may_ctx5 τg τa :=
  (mm_must_may_ctx4 τg τa ,, (gy ∷ [: ℕ | q_nat_ge0 ])) (only parsing).
Local Notation mm_must_may_ctx6 τg τa :=
  (mm_must_may_ctx5 τg τa ,, (px ∷ {: 𝔹 | q_true })) (only parsing).

Lemma must_may_program_obl_px :
  sub_type_under ∅ (mm_must_may_ctx5 must_may_g_ty U[ ℕ ])
    (binop_precise_ty bop_le (vnat 0) (avar gx)) ({: 𝔹 | q_true }).
Proof.
  unfold binop_precise_ty; cbn [bin_op_type].
  eapply extended_semantic_subtype_trans.
  - apply subtype_inter_over_under_to_over_part. mm_subtype_wf.
  - apply mm_subtype_over_entails; [mm_subtype_wf| ].
    unfold binop_result_qual, q_true, bool_qual, mk_q_eq, avar, vnat.
    mm_qual_entails.
    destruct Hq as (c1 & c2 & c' & H1 & H2 & H3 & Hstep).
    rewrite H3. cbn [denote_lvar_value] in H1. inversion H1; subst.
    inversion Hstep; subst. reflexivity.
Qed.

Lemma must_may_program_obl_py :
  sub_type_under ∅ (mm_must_may_ctx6 must_may_g_ty U[ ℕ ])
    (binop_precise_ty bop_le (vnat 0) (avar gy)) ({: 𝔹 | q_true }).
Proof.
  unfold binop_precise_ty; cbn [bin_op_type].
  eapply extended_semantic_subtype_trans.
  - apply subtype_inter_over_under_to_over_part. mm_subtype_wf.
  - apply mm_subtype_over_entails; [mm_subtype_wf| ].
    unfold binop_result_qual, q_true, bool_qual, mk_q_eq, avar, vnat.
    mm_qual_entails.
    destruct Hq as (c1 & c2 & c' & H1 & H2 & H3 & Hstep).
    rewrite H3. cbn [denote_lvar_value] in H1. inversion H1; subst.
    inversion Hstep; subst. reflexivity.
Qed.

(** Context-dependent obligation (arbitrary well-formed prefix [Γ0]).
    Informal argument: [px] and [py] are bound with the closed over-types
    [{𝔹 | ν = true}], so every store of a world [m] of the context maps
    both to [true].  [m] is non-empty (worlds are non-empty), so the fiber
    [px = py = true] of the precise [&&]-type is inhabited and its under
    part makes [true && true = true] reachable; the over part rules out
    every other value.  Therefore the result world reaches [true], i.e.
    [[𝔹 | ν = true]] holds.

    Remark (paper, int version): in ℕ, [0 ≤ g x] is trivially [true]; with
    the paper's [int] the must-summary [g : x:[⊤] → [ν ≥ 0]] only gives
    [px : [ν = true]] and [py : [ν = true]] separately, and with the
    entangled context [x:[⊤], y:[⊤]] the pair [px = py = true] need not be
    reachable (a capability may pair every [x] with [g x ≥ 0] only with
    [y]s such that [g y < 0]).  The int version needs [y : [⊤] -∗ ...]. *)
Lemma must_may_program_obl_result Γ0 :
  wf_ctx_under ∅ ((Γ0 ,, (px ∷ {: 𝔹 | q_true })) ,, (py ∷ {: 𝔹 | q_true })) ->
  sub_type_under ∅ ((Γ0 ,, (px ∷ {: 𝔹 | q_true })) ,, (py ∷ {: 𝔹 | q_true }))
    (binop_precise_ty bop_and (avar px) (avar py)) ([: 𝔹 | q_true ]).
Proof. Admitted.

(** Paper-faithful target (Godefroid must/may, ℕ version). *)
Theorem must_may_program_typing :
  ∅; Emp ⊢ₓ must_may_program ⋮ must_may_ref_ty.
Proof.
  unfold must_may_program, must_may_ref_ty, must_may_f_ty.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := [: ℕ | q_nat_ge0 ]); [mm_wf| | ].
  { eapply mm_app with (τx := U[ ℕ ]); [mm_wf|mm_fresh| mm_var | mm_var]. }
  eapply EXT_LetNamed with (τ1 := [: ℕ | q_nat_ge0 ]); [mm_wf| | ].
  { eapply mm_app with (τx := U[ ℕ ]); [mm_wf|mm_fresh| mm_var | mm_var]. }
  eapply EXT_LetNamed with (τ1 := {: 𝔹 | q_true }); [mm_wf| | ].
  { eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | exact must_may_program_obl_px]. }
  eapply EXT_LetNamed with (τ1 := {: 𝔹 | q_true }); [mm_wf| | ].
  { eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | exact must_may_program_obl_py]. }
  eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | ].
  apply must_may_program_obl_result. mm_wf.
Qed.

(** Round-1 name; identical target since round 2. *)
Theorem must_may_program_typing_all :
  ∅; Emp ⊢ₓ must_may_program ⋮ must_may_ref_ty_all.
Proof. exact must_may_program_typing. Qed.

(** ** Figure 6(a): may-analysis helps must-analysis

    [may_reach_program] is literally the program of Figure 6(a):
      λg. λx. λy. let cond = y > 10 in
                  if cond then (let gx = g x in gx + 1) else x + 1. *)

Local Notation fig6a_then := (let gx := g @ x in gx ⟨ + ⟩ vnat 1) (only parsing).
Local Notation fig6a_else := (x ⟨ + ⟩ vnat 1) (only parsing).
Local Notation fig6a_body :=
  (if cond then fig6a_then else fig6a_else) (only parsing).

Local Notation fig6a_cond_ty :=
  (binop_precise_ty bop_gt (avar y) (vnat 10)) (only parsing).

(** Branch contexts.  Both summands bind [g], [x], [cond] with the same
    erasure, as required by [basic_ctx] for [⊕]. *)
Local Notation fig6a_ctx_true :=
  (((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ O[ ℕ ])) ,,
     (cond ∷ bool_precise_ty true)) (only parsing).
Local Notation fig6a_ctx_false :=
  (((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ [: ℕ | q_nat_eq0 ])) ,,
     (cond ∷ bool_precise_ty false)) (only parsing).

(** Else branch: [x : [ν = 0]] makes [x + 1] reach [1].
    Informal argument: the precise [+]-type is fibered over [x]; the
    binding [x ∷ [ν = 0]] (closed under-type) guarantees that the
    [x = 0] fiber is inhabited in every world of [fig6a_ctx_false], and on
    that fiber the under part of [binop_precise_ty bop_plus x 1] makes the
    result [0 + 1 = 1] reachable; hence the whole result world reaches
    [1], which is [[ℕ | ν = 1]]. *)
Lemma may_reach_program_obl_else_eq1_x0 :
  sub_type_under ∅ fig6a_ctx_false
    (binop_precise_ty bop_plus (avar x) (vnat 1)) ([: ℕ | q_nat_eq1 ]).
Proof. Admitted.

(** Then branch: the may-summary [g x ≠ 0] gives [g x + 1 ≠ 1].
    Stated for an arbitrary well-formed prefix [Γ0] (used for settings
    (2c), (3) and the [-∗] version).  Informal argument: [gx ∷ {ν ≠ 0}] is
    a closed over-binding, so every store maps [gx] to a non-zero number;
    the over part of the precise [+]-type says that on every [gx]-fiber the
    result is [gx + 1], hence never [1]: every result store satisfies
    [ν ≠ 1], which is [{ℕ | ν ≠ 1}] (closed qualifier, FFibVars over ∅). *)
Lemma may_reach_program_obl_then_ne1 Γ0 :
  wf_ctx_under ∅ (Γ0 ,, (gx ∷ {: ℕ | q_nat_ne0 })) ->
  sub_type_under ∅ (Γ0 ,, (gx ∷ {: ℕ | q_nat_ne0 }))
    (binop_precise_ty bop_plus (avar gx) (vnat 1)) ({: ℕ | q_nat_ne1 }).
Proof. Admitted.

Lemma fig6a_else_typing :
  ∅; fig6a_ctx_false ⊢ₓ fig6a_else ⋮ [: ℕ | q_nat_eq1 ].
Proof.
  eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | exact may_reach_program_obl_else_eq1_x0].
Qed.

Lemma fig6a_then_typing :
  ∅; fig6a_ctx_true ⊢ₓ fig6a_then ⋮ {: ℕ | q_nat_ne1 }.
Proof.
  eapply EXT_LetNamed with (τ1 := {: ℕ | q_nat_ne0 }); [mm_wf| | ].
  { eapply mm_app with (τx := O[ ℕ ]); [mm_wf|mm_fresh| mm_var | mm_var]. }
  eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | ].
  apply may_reach_program_obl_then_ne1. mm_wf.
Qed.

(** *** Setting (1a): [x:[ν=0] → y:(exactly [0,10]) → [ν=1]] *)

Local Notation fig6a_1a_ctx :=
  ((((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ [: ℕ | q_nat_eq0 ])) ,,
     (y ∷ fig6a_y_exact_ty)) ,, (cond ∷ fig6a_cond_ty)) (only parsing).

(** Informal argument: [y ∷ {ν ≤ 10} ⊓ [ν ≤ 10]] forces every store to
    have [y ≤ 10], so [cond = (y > 10)] is [false] in every store (and,
    worlds being non-empty, [false] is reached): [cond ∷ bool_precise_ty
    false] holds on the restriction.  The bindings of [g] and [x] are
    copied unchanged (the restriction to [{g, x, cond}] does not remove any
    store, so the [x = 0] witness survives). *)
Lemma may_reach_program_obl_ctx_1a :
  ctx_sub_under ∅ (fv_tm fig6a_body ∪ fv_cty ([: ℕ | q_nat_eq1 ]))
    fig6a_1a_ctx fig6a_ctx_false.
Proof. Admitted.

Theorem fig6a_1a_typing :
  ∅; Emp ⊢ₓ may_reach_program ⋮ fig6a_ref_ty_1a.
Proof.
  unfold may_reach_program, fig6a_ref_ty_1a, fig6a_f_ty_1a.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := fig6a_cond_ty); [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_CtxSub; [mm_wf| |exact may_reach_program_obl_ctx_1a].
  eapply EXT_MatchFalseOnly; [mm_wf|mm_var|exact fig6a_else_typing].
Qed.

(** *** Setting (2a): [x:[ν=0] → y:(exactly [0,10]) -∗ [ν=1]] *)

Local Notation fig6a_2a_ctx :=
  ((((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ [: ℕ | q_nat_eq0 ])) ∗
     (y ∷ fig6a_y_exact_ty)) ,, (cond ∷ fig6a_cond_ty)) (only parsing).

(** Same argument as [may_reach_program_obl_ctx_1a]; the star only adds
    independence, which is not needed here. *)
Lemma may_reach_program_obl_ctx_2a :
  ctx_sub_under ∅ (fv_tm fig6a_body ∪ fv_cty ([: ℕ | q_nat_eq1 ]))
    fig6a_2a_ctx fig6a_ctx_false.
Proof. Admitted.

Theorem fig6a_2a_typing :
  ∅; Emp ⊢ₓ may_reach_program ⋮ fig6a_ref_ty_2a.
Proof.
  unfold may_reach_program, fig6a_ref_ty_2a, fig6a_f_ty_2a.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamDNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := fig6a_cond_ty); [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_CtxSub; [mm_wf| |exact may_reach_program_obl_ctx_2a].
  eapply EXT_MatchFalseOnly; [mm_wf|mm_var|exact fig6a_else_typing].
Qed.

(** *** Setting (2c): [x:[ν=0] → y:[⊤] -∗ {ν≠1} ⊕ [ν=1]] ([y:[⊤]] = [U[ℕ]]) *)

Local Notation fig6a_2c_ctx :=
  ((((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ [: ℕ | q_nat_eq0 ])) ∗
     (y ∷ U[ ℕ ])) ,, (cond ∷ fig6a_cond_ty)) (only parsing).

(** The key obligation where independence ([∗]) is used.
    Informal argument: a world [r] of [fig6a_2c_ctx] contains a product
    [A × B ⊑ r|{g,x,y}] with [A ⊨ g, x:[ν=0]] and [B ⊨ y:[⊤]], and [cond]
    is determined by [y].  Take [r' = r|{g,x,cond}] and split it into
    [r_t = r' ∩ {cond = true}] and [r_f = r' ∩ {cond = false}].  Both are
    non-empty because [B] contains [y = 11] and [y = 0] (the under-type
    [U[ℕ]] makes the [y]-projection of [B] all of ℕ; with the round-1
    trivial [U[ℕ]] the obligation was FALSE: [B = {y = 0}] gives an empty
    [r_t]).  Since [r|{g,x,y} = A × B] and every [a ∈ A] is paired with
    both [y = 11] and [y = 0], [r_t|{g,x} = r_f|{g,x} = A], so the [g]
    and [x] bindings are preserved verbatim (no sub-world argument is
    needed).  [r_t] satisfies
    [fig6a_ctx_true] ([g] keeps its over-arrow type on any sub-world, [x]
    is unconstrained, [cond] is exactly [true]).  [r_f] satisfies
    [fig6a_ctx_false]: for the store [a ∈ A] with [x = 0], the pair
    [(a, y = 0)] is in the product, so [x = 0] is still reachable in
    [r_f]; [cond] is exactly [false].  [r_t ∪ r_f = r'], hence
    [r' ⊨ fig6a_ctx_true ⊕ fig6a_ctx_false].
    With the entangled [,] instead of [∗] this step is FALSE (see the
    discussion of setting (1) below). *)
Lemma may_reach_program_obl_ctx_split_2c :
  ctx_sub_under ∅
    (fv_tm fig6a_body ∪ fv_cty ({: ℕ | q_nat_ne1 } ⊕ [: ℕ | q_nat_eq1 ]))
    fig6a_2c_ctx (fig6a_ctx_true ⊕ fig6a_ctx_false).
Proof. Admitted.

Theorem fig6a_2c_sum_typing :
  ∅; Emp ⊢ₓ may_reach_program ⋮ fig6a_ref_ty_2c_sum.
Proof.
  unfold may_reach_program, fig6a_ref_ty_2c_sum, fig6a_f_ty_2c_sum.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamDNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := fig6a_cond_ty); [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_CtxSub; [mm_wf| |exact may_reach_program_obl_ctx_split_2c].
  eapply EXT_MatchBoth;
    [mm_wf|mm_var|mm_var|exact fig6a_then_typing|exact fig6a_else_typing].
Qed.

(** Final weakening (any context [Γ]; both types are closed): the second,
    non-empty part of the [⊕] reaches [1], and a closed [FUnder] is upward
    closed.  Proved (round 2) from the generic [mm_sum_over_under_to_under]. *)
Lemma may_reach_program_obl_sum_weaken Γ :
  subtype_wf ∅ Γ ({: ℕ | q_nat_ne1 } ⊕ [: ℕ | q_nat_eq1 ]) ([: ℕ | q_nat_eq1 ]) ->
  sub_type_under ∅ Γ
    ({: ℕ | q_nat_ne1 } ⊕ [: ℕ | q_nat_eq1 ]) ([: ℕ | q_nat_eq1 ]).
Proof.
  intros Hwf.
  apply mm_sum_over_under_to_under; [exact Hwf| | ];
    unfold qual_dom; mm_fv_norm; set_solver.
Qed.

Theorem fig6a_2c_typing :
  ∅; Emp ⊢ₓ may_reach_program ⋮ fig6a_ref_ty_2c.
Proof.
  unfold may_reach_program, fig6a_ref_ty_2c, fig6a_f_ty_2c.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamDNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := fig6a_cond_ty); [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_Sub; [mm_wf| |apply may_reach_program_obl_sum_weaken; mm_subtype_wf].
  eapply EXT_CtxSub; [mm_wf| |exact may_reach_program_obl_ctx_split_2c].
  eapply EXT_MatchBoth;
    [mm_wf|mm_var|mm_var|exact fig6a_then_typing|exact fig6a_else_typing].
Qed.


(** *** Setting (2), the paper's type: [x:[ν=0] → y:[0≤ν≤10] -∗ [ν=1]]

    Round 2: derived with the capability case split [EXT_CtxCase].  The
    capability of [y:[0 ≤ ν ≤ 10]] reaches all of [0..10] but may or may not
    contain values [> 10]; we split on that:
    - no [y > 10] reachable: [cond] is [false] everywhere, only the
      else-branch is taken ([fig6a_ctx_false], T-MatchFalseOnly);
    - some [y > 10] reachable: both branches are reachable and, thanks to
      [∗], the [x = 0] store is paired with [y = 0] in the [cond = false]
      part ([fig6a_ctx_true ⊕ fig6a_ctx_false], T-MatchBoth, then the
      [⊕]-weakening to [[ν = 1]] as in setting (2c)). *)

Local Notation fig6a_2_ctx :=
  ((((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ [: ℕ | q_nat_eq0 ])) ∗
     (y ∷ [: ℕ | q_nat_le10 ])) ,, (cond ∷ fig6a_cond_ty)) (only parsing).

(** Informal argument.  [X = fv body ∪ fv [ν=1] = {cond, g, x}].  Let [r]
    be a world of [fig6a_2_ctx].  By the [∗] there are [A ⊨ g, x:[ν=0]]
    (domain [{g,x}]) and [B ⊨ y:[ν ≤ 10]] (domain [{y}]) with
    [A × B ⊑ r], i.e. [r|{g,x,y} = A × B]; [B]'s [y]-projection contains
    every [n ≤ 10] (exact under-atom); the comma binding of [cond] makes
    [cond = (y > 10)] in every store of [r].  Let [r' = r|X].
    - Case all [y ∈ B] are [≤ 10]: [cond] is [false] in every store, so
      [r'] satisfies [cond ∷ {ν = false} ⊓ [ν = false]] (worlds are
      non-empty); [r'|{g,x} = A] satisfies [g ∷ may_reach_g_ty] and
      [x ∷ [ν = 0]] (closed types, the [A]-part is unchanged).  So
      [r' ⊨ fig6a_ctx_false].
    - Case some [y₁ ∈ B] with [y₁ > 10]: split [r'] into
      [r_t = r' ∩ {cond = true}] and [r_f = r' ∩ {cond = false}].  Every
      [a ∈ A] is paired with [y₁] (cond true) and with [y = 0] (cond false),
      so [r_t|{g,x} = r_f|{g,x} = A]; hence [r_t ⊨ fig6a_ctx_true]
      ([x ∷ O[ℕ]] is trivial for ℕ values) and [r_f ⊨ fig6a_ctx_false]
      ([x = 0] stays reachable).  Both are non-empty, have the same domain
      [X], and [res_sum r_t r_f = r'], so [r' ⊨ fig6a_ctx_true ⊕
      fig6a_ctx_false] ([FPlus]).
    In both cases [res_restrict r X ⊑ r'] (equality).  With the entangled
    [,] instead of [∗] the second case fails (F1). *)
Lemma may_reach_program_obl_case_2 :
  ctx_case_under ∅ (fv_tm fig6a_body ∪ fv_cty ([: ℕ | q_nat_eq1 ]))
    fig6a_2_ctx fig6a_ctx_false (fig6a_ctx_true ⊕ fig6a_ctx_false).
Proof. Admitted.

Theorem fig6a_2_typing :
  ∅; Emp ⊢ₓ may_reach_program ⋮ fig6a_ref_ty_2.
Proof.
  unfold may_reach_program, fig6a_ref_ty_2, fig6a_f_ty_2.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamDNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := fig6a_cond_ty); [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_CtxCase; [mm_wf| | |exact may_reach_program_obl_case_2].
  - eapply EXT_MatchFalseOnly; [mm_wf|mm_var|exact fig6a_else_typing].
  - eapply EXT_Sub; [mm_wf| |apply may_reach_program_obl_sum_weaken; mm_subtype_wf].
    eapply EXT_MatchBoth;
      [mm_wf|mm_var|mm_var|exact fig6a_then_typing|exact fig6a_else_typing].
Qed.

(** *** Setting (3): precise dependency
    [x:[⊤] → y:[(x = 0 ⟹ ν = 12) ∧ (x > 0 ⟹ ν ≤ 10)] → {ν ≠ 1} ⊕ [ν ≥ 2]]

    Result type.  The authors elided it; the strongest sound type obtained
    by the T-Match discipline is [{ν ≠ 1} ⊕ [ν ≥ 2]]:
    - the then-branch is reachable ([x = 0] forces [y = 12 > 10]); by the
      may-summary of [g] it never returns [1] — this is where the
      may-analysis is used;
    - the else-branch is reachable and, for every [x ≥ 1], [y = 0 ≤ 10]
      is reachable, so [x + 1] reaches every [n ≥ 2];
    - [1] is NOT reachable in general (the reviewer's capability pairs
      [x = 0] only with [y = 12]), so no type containing [[ν = 1]] is
      sound; and the else-branch may also contain stores with [x = 0] (the
      angelic refinement of [y] does not exclude extra values), so it has
      no non-trivial over-approximation in ℕ.
    Since [x] is referenced by [y]'s refinement, the [x]-abstraction uses
    the locally nameless rule [EXT_Lam]; the body is checked for an
    arbitrary fresh [xa]. *)

Lemma q_fig6a_y3_open (xa : atom) :
  qual_open_atom 1 xa (q_fig6a_y3 (vbvar 1)) = q_fig6a_y3 (avar xa).
Proof.
  unfold q_fig6a_y3. cbn [qual_open_atom].
  apply qual_ext.
  - cbn [qual_lvars]. unfold vnu, avar. cbn [lvar_value_keys].
    apply set_eq. intros v. rewrite elem_of_set_swap.
    unfold swap. repeat destruct decide; subst; set_solver.
  - intros s1 s2 Hs. cbn [qual_prop].
    unfold lstore_on_open_back. cbn [lso_store storeAO_store] in *.
    unfold vnu, avar. cbn [denote_lvar_value].
    assert (E1 : forall S : LStore,
      (lstore_swap (LVBound 1) (LVFree xa) S : gmap logic_var value) !! LVBound 1 =
      (S : gmap logic_var value) !! LVFree xa).
    { intros S. unfold lstore_swap, lstore_rekey.
      assert (Hs1 : swap (LVBound 1) (LVFree xa) (LVFree xa) = LVBound 1)
        by (unfold swap; repeat destruct decide; congruence).
      pose proof (storeA_rekey_lookup (swap (LVBound 1) (LVFree xa))
        (swap_inj _ _) S (LVFree xa)) as H.
      rewrite Hs1 in H. exact H. }
    assert (E0 : forall S : LStore,
      (lstore_swap (LVBound 1) (LVFree xa) S : gmap logic_var value) !! LVBound 0 =
      (S : gmap logic_var value) !! LVBound 0).
    { intros S. unfold lstore_swap, lstore_rekey.
      assert (Hs1 : swap (LVBound 1) (LVFree xa) (LVBound 0) = LVBound 0)
        by (unfold swap; repeat destruct decide; congruence).
      pose proof (storeA_rekey_lookup (swap (LVBound 1) (LVFree xa))
        (swap_inj _ _) S (LVBound 0)) as H.
      rewrite Hs1 in H. exact H. }
    rewrite E1, E0.
    destruct s1 as [st1 d1], s2 as [st2 d2]. unfold lso_store in *.
    cbn in *. subst. reflexivity.
Qed.

Lemma fig6a_3_open_body (xa : atom) :
  xa ≠ g -> xa ≠ y -> xa ≠ cond -> xa ≠ gx ->
  open_tm 0 (vfvar xa)
    (close_tm x 0 (ret (ƛ y : ℕ => let cond := y ⟨ > ⟩ vnat 10 in fig6a_body))) =
  ret (ƛ y : ℕ =>
        let cond := y ⟨ > ⟩ vnat 10 in
        if cond then (let gx := g @ xa in gx ⟨ + ⟩ vnat 1) else xa ⟨ + ⟩ vnat 1).
Proof.
  intros H1 H2 H3 H4.
  unfold Ret, lam_named, let_named, if_named, case_app, avar, vnat.
  unfold g, x, y, cond, gx in *.
  repeat (cbn [open_tm open_value close_tm close_value] in *; crush_binders).
  all: reflexivity.
Qed.

Local Notation fig6a_3_ctx xa :=
  ((((Emp ,, (g ∷ may_reach_g_ty)) ,, (xa ∷ U[ ℕ ])) ,,
     (y ∷ [: ℕ | q_fig6a_y3 (avar xa) ])) ,, (cond ∷ fig6a_cond_ty)) (only parsing).
Local Notation fig6a_3_ctx_true xa :=
  (((Emp ,, (g ∷ may_reach_g_ty)) ,, (xa ∷ O[ ℕ ])) ,,
     (cond ∷ bool_precise_ty true)) (only parsing).
Local Notation fig6a_3_ctx_false xa :=
  (((Emp ,, (g ∷ may_reach_g_ty)) ,, (xa ∷ [: ℕ | q_nat_gt0 ])) ,,
     (cond ∷ bool_precise_ty false)) (only parsing).
Local Notation fig6a_3_body xa :=
  (if cond then (let gx := g @ xa in gx ⟨ + ⟩ vnat 1) else xa ⟨ + ⟩ vnat 1)
  (only parsing).

(** Informal argument (match split).  Let [r] be a world of
    [fig6a_3_ctx xa].  [xa ∷ U[ℕ]] makes every [n ∈ ℕ] a value
    of [xa] in [r] (with the round-1 trivial [U[ℕ]] it was FALSE:
    [xa = 5] only gives [y ≤ 10] everywhere and an empty [cond = true]
    part); the dependent under-refinement of [y] is fibered over [xa]: in
    the [xa = 0] fiber [y = 12] is reachable, in every [xa = n ≥ 1] fiber
    all [y ∈ [0,10]] are reachable.  [cond = (y > 10)].  Take
    [r' = r|{g, xa, cond}] and split it by [cond]:
    - [r_t = r' ∩ {cond = true}] is non-empty (it contains the
      [xa = 0, y = 12] store) and satisfies [fig6a_3_ctx_true xa]:
      [xa ∷ O[ℕ]] and [cond ∷ bool_precise_ty true] are immediate;
    - [r_f = r' ∩ {cond = false}] contains, for every [n ≥ 1], the store
      [xa = n, y = 0]; hence [xa ∷ [ν > 0]] holds, and [cond] is exactly
      [false].
    [r_t ∪ r_f = r'], so [r' ⊨ fig6a_3_ctx_true xa ⊕ fig6a_3_ctx_false xa].
    The [g] binding (auditor's concern).  Because [y] is entangled with
    [xa], [r_t|{g}] and [r_f|{g}] may be strict subsets of [r|{g}], so we
    need: [g ∷ O[ℕ] → {ν ≠ 0}] is preserved by passing to a non-empty
    subset [m_s ⊆ m] of the stores (same domain).  This holds because the
    arrow is purely demonic: its denotation is, for every result extension
    and every argument extension [m_s'] of [m_s] with [m_s' ⊨ O[ℕ] z],
    [m_s' ⊨ {ν ≠ 0} (g z)].  Given such [m_s'], build an extension [m']
    of the whole [m] by adding the stores of [m ∖ m_s] extended with the
    argument [z = 0] (any value works: [O[ℕ]] only needs basic typing,
    which every natural satisfies, and [g z] is total for every store of
    [m] by the guard).  Then [m' ⊨ O[ℕ] z], hence
    [m' ⊨ {ν ≠ 0} (g z)], i.e. every result of [g z] in [m'] is non-zero;
    [FOver (FAtom q)] with the closed qualifier [ν ≠ 0] is downward closed
    under taking subsets of stores, so it also holds on [m_s' ⊆ m']. *)
Lemma may_reach_program_obl_ctx_split_3 (xa : atom) :
  xa ≠ g -> xa ≠ y -> xa ≠ cond -> xa ≠ gx ->
  ctx_sub_under ∅ (fv_tm (fig6a_3_body xa) ∪ fv_cty fig6a_res_ty_3)
    (fig6a_3_ctx xa) (fig6a_3_ctx_true xa ⊕ fig6a_3_ctx_false xa).
Proof. Admitted.

(** Informal argument: [xa ∷ [ν > 0]] makes every [n ≥ 1] reachable; the
    precise [+]-type is fibered over [xa] and its under part makes
    [n + 1] reachable in the [xa = n] fiber; so every [m ≥ 2] is reached. *)
Lemma may_reach_program_obl_else_ge2_3 (xa : atom) :
  xa ≠ g -> xa ≠ y -> xa ≠ cond -> xa ≠ gx ->
  sub_type_under ∅ (fig6a_3_ctx_false xa)
    (binop_precise_ty bop_plus (avar xa) (vnat 1)) ([: ℕ | q_nat_ge2 ]).
Proof. Admitted.

Theorem fig6a_3_typing :
  ∅; Emp ⊢ₓ may_reach_program ⋮ fig6a_ref_ty_3.
Proof.
  unfold may_reach_program, fig6a_ref_ty_3, fig6a_f_ty_3.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  change (ret (ƛ x : ℕ => ret (ƛ y : ℕ => let cond := y ⟨ > ⟩ vnat 10 in fig6a_body)))
    with (tret (vlam (erase_ty (U[ ℕ ]))
      (close_tm x 0 (ret (ƛ y : ℕ => let cond := y ⟨ > ⟩ vnat 10 in fig6a_body))))).
  eapply EXT_Lam with (L := {[g]} ∪ {[x]} ∪ {[y]} ∪ {[cond]} ∪ {[gx]}).
  { unfold context_typing_wf, wf_ctx_under; mm_unfold_tys; repeat split;
      try solve [mm_wf_goal].
    match goal with
    | |- context [tret (vlam ?T (close_tm x 0 ?e))] =>
        change (tret (vlam T (close_tm x 0 e)))
          with (ret (lam_named x ℕ e))
    end.
    mm_wf_goal. }
  intros xa Hxa.
  assert (Hg : xa ≠ g) by set_solver.
  assert (Hy : xa ≠ y) by set_solver.
  assert (Hc : xa ≠ cond) by set_solver.
  assert (Hgx : xa ≠ gx) by set_solver.
  clear Hxa.
  change (@open_one atom tm _ 0 xa ?e) with (open_tm 0 (vfvar xa) e).
  rewrite (fig6a_3_open_body xa Hg Hy Hc Hgx).
  change (@open_one atom context_ty open_cty_atom_inst 0 xa
            ([: ℕ | q_fig6a_y3 (vbvar 1) ] → fig6a_res_ty_3))
    with (cty_open 0 xa ([: ℕ | q_fig6a_y3 (vbvar 1) ]) →
          cty_open 1 xa fig6a_res_ty_3).
  replace (cty_open 0 xa ([: ℕ | q_fig6a_y3 (vbvar 1) ]))
    with ([: ℕ | q_fig6a_y3 (avar xa) ])
    by (unfold under_ty; cbn [cty_open]; rewrite q_fig6a_y3_open; reflexivity).
  rewrite (cty_open_above_lc_fresh 0 1 xa fig6a_res_ty_3);
    [ |lia| eapply wf_context_ty_at_lc with (D := (∅ : aset)); mm_wf_type | mm_fresh].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := fig6a_cond_ty); [mm_wf| eapply EXT_BinOp; mm_wf | ].
  unfold fig6a_res_ty_3.
  eapply EXT_CtxSub; [mm_wf| |exact (may_reach_program_obl_ctx_split_3 xa Hg Hy Hc Hgx)].
  eapply EXT_MatchBoth; [mm_wf|mm_var|mm_var| | ].
  - eapply EXT_LetNamed with (τ1 := {: ℕ | q_nat_ne0 }); [mm_wf| | ].
    { eapply mm_app with (τx := O[ ℕ ]); [mm_wf|mm_fresh| mm_var | mm_var]. }
    eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | ].
    apply may_reach_program_obl_then_ne1. mm_wf.
  - eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf
                    | exact (may_reach_program_obl_else_ge2_3 xa Hg Hy Hc Hgx)].
Qed.


(** *** The pre-existing target, made independent:
    [x:[⊤] → y:[⊤] -∗ [ν = 1]] (same derivation as setting (2c)).  (With
    the round-1 trivial [U[ℕ]] the type was FALSE: capability [x = 5],
    [y = 0].) *)

Local Notation may_reach_star_ctx :=
  ((((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ U[ ℕ ])) ∗
     (y ∷ U[ ℕ ])) ,, (cond ∷ fig6a_cond_ty)) (only parsing).
Local Notation may_reach_ctx_false :=
  (((Emp ,, (g ∷ may_reach_g_ty)) ,, (x ∷ U[ ℕ ])) ,,
     (cond ∷ bool_precise_ty false)) (only parsing).

(** Same argument as [may_reach_else_plus_one_eq1_subtype]:
    [x ∷ U[ℕ]] makes the [x = 0] fiber inhabited, where
    [x + 1 = 1] is reached. *)
Lemma may_reach_program_obl_else_eq1_star :
  sub_type_under ∅ may_reach_ctx_false
    (binop_precise_ty bop_plus (avar x) (vnat 1)) ([: ℕ | q_nat_eq1 ]).
Proof. Admitted.

(** Same argument as [may_reach_program_obl_ctx_split_2c]: with [A × B],
    the [y]-projection of [B] is ℕ ([U[ℕ]]), so every store of [A] is
    paired with [y = 0] (cond false) and with [y = 11] (cond true); hence
    [r_t|{g,x} = r_f|{g,x} = A] and [x ∷ U[ℕ]] survives in the
    false part. *)
Lemma may_reach_program_obl_ctx_split_star :
  ctx_sub_under ∅
    (fv_tm fig6a_body ∪ fv_cty ({: ℕ | q_nat_ne1 } ⊕ [: ℕ | q_nat_eq1 ]))
    may_reach_star_ctx (fig6a_ctx_true ⊕ may_reach_ctx_false).
Proof. Admitted.

Theorem may_reach_program_typing_star :
  ∅; Emp ⊢ₓ may_reach_program ⋮ may_reach_ref_ty_star.
Proof.
  unfold may_reach_program, may_reach_ref_ty_star, may_reach_f_ty_star.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamDNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := fig6a_cond_ty); [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_Sub; [mm_wf| |apply may_reach_program_obl_sum_weaken; mm_subtype_wf].
  eapply EXT_CtxSub; [mm_wf| |exact may_reach_program_obl_ctx_split_star].
  eapply EXT_MatchBoth; [mm_wf|mm_var|mm_var|exact fig6a_then_typing| ].
  eapply EXT_Sub; [mm_wf| eapply EXT_BinOp; mm_wf | exact may_reach_program_obl_else_eq1_star].
Qed.

(** ** Figure 6(b): must-analysis helps may-analysis

    The context after [let a = g x] and [let cond = a > 3] is
    parameterised by the summary [τg] of [g] and the argument type [τx]. *)

Local Notation fig6b_ctx4 τg τx :=
  (((((Emp ,, (g ∷ τg)) ,, (x ∷ τx)) ,,
      (a ∷ [: ℕ | q_nat_gt0 ])) ,,
     (cond ∷ binop_precise_ty bop_gt (avar a) (vnat 3)))) (only parsing).
Local Notation fig6b_body :=
  (if cond then ret (vnat 5) else ret (vnat 2)) (only parsing).

(** Projection of the must-component of [g]'s intersection type (proved
    from the shared lemma [extended_semantic_subtype_inter_right]). *)
Lemma fig6b_program_obl_g_must :
  sub_type_under ∅ (g ∷ must_inter_g_ty) must_inter_g_ty
    (U[ ℕ ] → [: ℕ | q_nat_gt0 ]).
Proof.
  unfold must_inter_g_ty.
  apply extended_semantic_subtype_inter_right. mm_subtype_wf.
Qed.

(** Informal argument (match split), for any well-formed prefix [Γ0].  In
    every world [r] of the context the closed under-binding [a ∷ [ν > 0]]
    makes every [n ≥ 1] a value of [a]; [cond = (a > 3)] exactly.  So
    [r|{cond}] contains both [true] (from [a = 4]) and [false] (from
    [a = 1]); being a world over the single variable [cond] it is exactly
    [{true} ∪ {false}], the sum of the two non-empty worlds
    [{cond = true}] and [{cond = false}], which satisfy
    [cond ∷ bool_precise_ty true] resp. [false].  Nothing of [Γ0] is kept,
    so no sub-world argument is needed. *)
Lemma fig6b_program_obl_ctx_split Γ0 :
  wf_ctx_under ∅ ((Γ0 ,, (a ∷ [: ℕ | q_nat_gt0 ])) ,,
     (cond ∷ binop_precise_ty bop_gt (avar a) (vnat 3))) ->
  ctx_sub_under ∅ (fv_tm fig6b_body)
    ((Γ0 ,, (a ∷ [: ℕ | q_nat_gt0 ])) ,,
     (cond ∷ binop_precise_ty bop_gt (avar a) (vnat 3)))
    ((cond ∷ bool_precise_ty true) ⊕ (cond ∷ bool_precise_ty false)).
Proof. Admitted.

(** [⊕] is commutative on closed over-types (proved, Qed, from the generic
    [mm_sum_over_comm]).  Replaces the round-1 Admitted
    [fig6b_program_obl_sum_weaken]: the branches are now weakened from the
    precise constants to [{ν = n}] individually ([fig6b_const_over], Qed)
    before T-MatchBoth. *)
Lemma fig6b_program_obl_sum_comm Γ :
  subtype_wf ∅ Γ ({: ℕ | q_eq_nat 5 } ⊕ {: ℕ | q_eq_nat 2 })
    ({: ℕ | q_eq_nat 2 } ⊕ {: ℕ | q_eq_nat 5 }) ->
  sub_type_under ∅ Γ
    ({: ℕ | q_eq_nat 5 } ⊕ {: ℕ | q_eq_nat 2 })
    ({: ℕ | q_eq_nat 2 } ⊕ {: ℕ | q_eq_nat 5 }).
Proof.
  intros Hwf. apply mm_sum_over_comm; [exact Hwf| | ];
    unfold qual_dom, q_eq_nat; mm_fv_norm; set_solver.
Qed.

Lemma fig6b_const_over n :
  sub_type_under ∅ Emp (const_precise_ty (cnat n)) ({: ℕ | q_eq_nat n }).
Proof.
  unfold const_precise_ty, precise_ty, q_eq_nat.
  apply subtype_inter_over_under_to_over_part. mm_subtype_wf.
Qed.

(** Paper summary of [g], angelic argument [x : U[ℕ]], precise result. *)
Theorem fig6b_program_typing_precise :
  ∅; Emp ⊢ₓ fig6b_program ⋮ fig6b_ref_ty_precise.
Proof.
  unfold fig6b_program, fig6b_ref_ty_precise, fig6b_f_ty_precise.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := [: ℕ | q_nat_gt0 ]); [mm_wf| | ].
  { eapply mm_app with (τx := U[ ℕ ]); [mm_wf|mm_fresh| |mm_var].
    mm_var_sub must_inter_g_ty. exact fig6b_program_obl_g_must. }
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_gt (avar a) (vnat 3));
    [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_CtxSub;
    [mm_wf| |eapply mm_ctx_sub_under_mono;
              [apply fig6b_program_obl_ctx_split; mm_wf|mm_fv0]].
  eapply EXT_MatchBoth;
    [mm_wf| apply EXT_Var; mm_wf | apply EXT_Var; mm_wf | mm_const | mm_const].
Qed.

Theorem fig6b_program_typing :
  ∅; Emp ⊢ₓ fig6b_program ⋮ fig6b_ref_ty.
Proof.
  unfold fig6b_program, fig6b_ref_ty, fig6b_f_ty.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := [: ℕ | q_nat_gt0 ]); [mm_wf| | ].
  { eapply mm_app with (τx := U[ ℕ ]); [mm_wf|mm_fresh| |mm_var].
    mm_var_sub must_inter_g_ty. exact fig6b_program_obl_g_must. }
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_gt (avar a) (vnat 3));
    [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_Sub; [mm_wf| |apply fig6b_program_obl_sum_comm; mm_subtype_wf].
  eapply EXT_CtxSub;
    [mm_wf| |eapply mm_ctx_sub_under_mono;
              [apply fig6b_program_obl_ctx_split; mm_wf|mm_fv0]].
  eapply EXT_MatchBoth;
    [mm_wf| apply EXT_Var; mm_wf | apply EXT_Var; mm_wf
    | eapply mm_const_sub;
        [mm_wf|mm_wf|mm_wf|apply mm_ctx_sub_emp; [mm_wf|mm_fv0]|apply fig6b_const_over]
    | eapply mm_const_sub;
        [mm_wf|mm_wf|mm_wf|apply mm_ctx_sub_emp; [mm_wf|mm_fv0]|apply fig6b_const_over]].
Qed.

(** Round-1 name; identical target since round 2.  (The paper's literal
    [x:{⊤}] type [fig6b_ref_ty_paper] is FALSE, F4; in round 1 it was
    "derivable" only through the false-now [O[ℕ] <: U[ℕ]], which has been
    removed together with [fig6b_program_typing_paper_literal].) *)
Theorem fig6b_program_typing_all :
  ∅; Emp ⊢ₓ fig6b_program ⋮ fig6b_ref_ty_all.
Proof. exact fig6b_program_typing. Qed.

(** ** [must_inter_program] (pre-existing variant of Figure 6(b)) and the
       pre-existing [comprehensive_inter_f_ty] *)

Local Notation must_inter_body :=
  (if cond then ret (vnat 3) else ret a) (only parsing).
Local Notation must_inter_res_ty :=
  (const_precise_ty (cnat 3) ⊕ ({: ℕ | q_nat_1to10 } ⊓ [: ℕ | q_nat_1to10 ]))
  (only parsing).

(** Combining the may- and must-summaries of [g] (informal argument): a
    function value satisfying both [O[ℕ] → {ν > 0}] and
    [τa → [ν > 0]], applied to an argument world satisfying [τa]
    (which in particular satisfies the trivial over-type [O[ℕ]]: every
    natural satisfies [qual_top]), yields a result world satisfying both
    [{ν > 0}] and [[ν > 0]], i.e. their intersection.  In the denotation
    the three arrows are [FForall] over the result variable of the
    application with [FImpl] premises on argument extensions; all
    qualifiers are closed, so the formula free-variable sets (and thus the
    extension domains) of the three bodies coincide, and the same
    extension world can be fed to both conjuncts of the source; [⊓] is
    [FAnd] (with the same guard), so the two conclusions combine. *)
Lemma must_inter_program_obl_g_combined :
  sub_type_under ∅ (g ∷ must_inter_g_ty) must_inter_g_ty
    (U[ ℕ ] → ({: ℕ | q_nat_gt0 } ⊓ [: ℕ | q_nat_gt0 ])).
Proof. Admitted.

(** Informal argument (match split), for any well-formed prefix [Γ0].
    [a ∷ {ν > 0} ⊓ [ν > 0]] says the [a]-projection of every world is
    exactly the positive numbers.  [cond = (a > 10)] exactly.  Restricting
    to [{a, cond}]: the part with [cond = true] is non-empty ([a = 11]) and
    satisfies [a ∷ O[ℕ], cond ∷ bool_precise_ty true]; the part with
    [cond = false] has [a]-projection exactly [{1..10}], so it satisfies
    [a ∷ {1 ≤ ν ≤ 10} ⊓ [1 ≤ ν ≤ 10], cond ∷ bool_precise_ty false].
    Nothing of [Γ0] is kept. *)
Lemma must_inter_program_obl_ctx_split Γ0 :
  wf_ctx_under ∅ ((Γ0 ,, (a ∷ ({: ℕ | q_nat_gt0 } ⊓ [: ℕ | q_nat_gt0 ]))) ,,
     (cond ∷ binop_precise_ty bop_gt (avar a) (vnat 10))) ->
  ctx_sub_under ∅ (fv_tm must_inter_body ∪ fv_cty must_inter_res_ty)
    ((Γ0 ,, (a ∷ ({: ℕ | q_nat_gt0 } ⊓ [: ℕ | q_nat_gt0 ]))) ,,
     (cond ∷ binop_precise_ty bop_gt (avar a) (vnat 10)))
    (((a ∷ O[ ℕ ]) ,, (cond ∷ bool_precise_ty true)) ⊕
     ((a ∷ ({: ℕ | q_nat_1to10 } ⊓ [: ℕ | q_nat_1to10 ])) ,,
        (cond ∷ bool_precise_ty false))).
Proof. Admitted.

(** Informal argument (any [Γ]; closed types): the over part [O[ℕ]] holds
    for every ℕ-typed total term (closed trivial qualifier); for the under
    part, the second summand [{1..10} ⊓ [1..10]] of every result world
    reaches [1] (its under part reaches all of [1..10]), so the whole
    result world reaches [1] ([FUnder] with the closed qualifier [ν = 1]
    is upward closed in the world). *)
Lemma must_inter_program_obl_res_eq1 Γ :
  subtype_wf ∅ Γ must_inter_res_ty (O[ ℕ ] ⊓ [: ℕ | q_nat_eq1 ]) ->
  sub_type_under ∅ Γ must_inter_res_ty (O[ ℕ ] ⊓ [: ℕ | q_nat_eq1 ]).
Proof. Admitted.

Lemma must_inter_program_obl_x_inter_under :
  sub_type_under ∅ (x ∷ (O[ ℕ ] ⊓ U[ ℕ ])) (O[ ℕ ] ⊓ U[ ℕ ]) (U[ ℕ ]).
Proof. apply extended_semantic_subtype_inter_right. mm_subtype_wf. Qed.

(** [must_inter_program] with an angelic [x] (paper summary of [g]). *)
Theorem must_inter_program_typing_must :
  ∅; Emp ⊢ₓ must_inter_program ⋮ must_inter_ref_ty_must.
Proof.
  unfold must_inter_program, must_inter_ref_ty_must, must_inter_f_ty_must.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := {: ℕ | q_nat_gt0 } ⊓ [: ℕ | q_nat_gt0 ]); [mm_wf| | ].
  { eapply mm_app with (τx := U[ ℕ ]); [mm_wf|mm_fresh| |mm_var].
    mm_var_sub must_inter_g_ty. exact must_inter_program_obl_g_combined. }
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_gt (avar a) (vnat 10));
    [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_CtxSub; [mm_wf| |apply must_inter_program_obl_ctx_split; mm_wf].
  eapply EXT_MatchBoth; [mm_wf| mm_var | mm_var | mm_const | mm_var].
Qed.

(** Round-1 name; identical target since round 2. *)
Theorem must_inter_program_typing_must_all :
  ∅; Emp ⊢ₓ must_inter_program ⋮ must_inter_ref_ty_must_all.
Proof. exact must_inter_program_typing_must. Qed.

(** *** The pre-existing target [must_inter_ref_ty]
    [g → x:{⊤} → y:{⊤} → {ν ≥ 0}] (round 2: derived with T-CtxCase).

    Only the may-component of [g] is used: [a = g x : {ν > 0}].  Since [x]
    is demonic, whether [cond = (a > 10)] reaches [true] and/or [false] is
    not determined by the context.  Two nested capability case splits
    ([EXT_CtxCase]) cover all capabilities: "true only" vs. "[false]
    reachable", and then "false only" vs. "both reachable".  (In round 1
    this target was not derivable with the faithful summary — finding F5,
    the T-Match gap — and only "derivable" through the then-trivial
    [O[ℕ] <: U[ℕ]].) *)

Local Notation mi_ctx_t :=
  ((a ∷ {: ℕ | q_nat_gt0 }) ,, (cond ∷ bool_precise_ty true)) (only parsing).
Local Notation mi_ctx_f :=
  ((a ∷ {: ℕ | q_nat_gt0 }) ,, (cond ∷ bool_precise_ty false)) (only parsing).
Local Notation mi_ctx_nt :=
  ((a ∷ {: ℕ | q_nat_gt0 }) ,, (cond ∷ [: 𝔹 | q_false ])) (only parsing).

(** Projection of the may-component of [g]'s intersection type (Qed, from
    the shared [extended_semantic_subtype_inter_left]). *)
Lemma must_inter_program_obl_g_may :
  sub_type_under ∅ (g ∷ must_inter_g_ty) must_inter_g_ty
    (O[ ℕ ] → {: ℕ | q_nat_gt0 }).
Proof.
  unfold must_inter_g_ty.
  apply extended_semantic_subtype_inter_left. mm_subtype_wf.
Qed.

(** Informal argument (capability split 1, any well-formed prefix [Γ0]).
    [X = {cond, a}].  Let [r] be a world of the context and [r' = r|X].
    The closed over-binding [a ∷ {ν > 0}] makes every store of [r] (hence
    of [r']) map [a] to a positive number, and [cond = (a > 10)] in every
    store.  If every store of [r'] has [cond = true], then [r'] satisfies
    [mi_ctx_t] ([cond ∷ {ν = true} ⊓ [ν = true]]: all stores [true], and
    [true] is reached since worlds are non-empty).  Otherwise some store
    has [cond = false], so [r'] satisfies [mi_ctx_nt]
    ([cond ∷ [𝔹 | ν = false]]: closed under-type, [false] is reached).
    Nothing of [Γ0] is kept; [res_restrict r X ⊑ r'] is an equality. *)
Lemma must_inter_program_obl_case_true Γ0 :
  wf_ctx_under ∅ ((Γ0 ,, (a ∷ {: ℕ | q_nat_gt0 })) ,,
     (cond ∷ binop_precise_ty bop_gt (avar a) (vnat 10))) ->
  ctx_case_under ∅ (fv_tm must_inter_body ∪ fv_cty ({: ℕ | q_nat_ge0 }))
    ((Γ0 ,, (a ∷ {: ℕ | q_nat_gt0 })) ,,
     (cond ∷ binop_precise_ty bop_gt (avar a) (vnat 10)))
    mi_ctx_t mi_ctx_nt.
Proof. Admitted.

(** Informal argument (capability split 2).  Let [r ⊨ mi_ctx_nt] and
    [r' = r|{cond, a}]: every [a] is positive, [false] is a reachable value
    of [cond].  If every store has [cond = false], [r' ⊨ mi_ctx_f].
    Otherwise [true] is reachable as well; split [r'] by the value of
    [cond] into the non-empty, same-domain worlds [r_t] and [r_f] with
    [res_sum r_t r_f = r'].  [a ∷ {ν > 0}] is pointwise, hence holds on
    both parts; [cond] is exactly [true] on [r_t] and exactly [false] on
    [r_f].  So [r' ⊨ mi_ctx_t ⊕ mi_ctx_f]. *)
Lemma must_inter_program_obl_case_false :
  ctx_case_under ∅ (fv_tm must_inter_body ∪ fv_cty ({: ℕ | q_nat_ge0 }))
    mi_ctx_nt mi_ctx_f (mi_ctx_t ⊕ mi_ctx_f).
Proof. Admitted.

(** Proved from the generic [mm_sum_over_to_over]: both parts of the
    [⊕]-typed result world only produce results [≥ 0]. *)
Lemma must_inter_program_obl_sum_ge0 Γ :
  subtype_wf ∅ Γ ({: ℕ | q_nat_ge0 } ⊕ {: ℕ | q_nat_ge0 }) ({: ℕ | q_nat_ge0 }) ->
  sub_type_under ∅ Γ ({: ℕ | q_nat_ge0 } ⊕ {: ℕ | q_nat_ge0 }) ({: ℕ | q_nat_ge0 }).
Proof.
  intros Hwf.
  apply mm_sum_over_to_over; [exact Hwf| | | | | ];
    try solve [unfold qual_dom; mm_fv_norm; set_solver];
    unfold q_nat_ge0, q_nat_pred, q_const_pred; mm_qual_entails; exact Hq.
Qed.

Lemma must_inter_then_ge0_typing :
  ∅; mi_ctx_t ⊢ₓ ret (vnat 3) ⋮ {: ℕ | q_nat_ge0 }.
Proof.
  eapply mm_const_sub; [mm_wf|mm_wf|mm_wf|apply mm_ctx_sub_emp; [mm_wf|mm_fv0]| ].
  exact must_inter_then_three_ge0_subtype.
Qed.

Lemma must_inter_else_ge0_typing :
  ∅; mi_ctx_f ⊢ₓ ret a ⋮ {: ℕ | q_nat_ge0 }.
Proof.
  mm_var_sub ({: ℕ | q_nat_gt0 }).
  exact (must_inter_else_gt0_ge0_subtype a).
Qed.

Theorem must_inter_program_typing :
  ∅; Emp ⊢ₓ must_inter_program ⋮ must_inter_ref_ty.
Proof.
  unfold must_inter_program, must_inter_ref_ty, must_inter_f_ty.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := {: ℕ | q_nat_gt0 }); [mm_wf| | ].
  { eapply mm_app with (τx := O[ ℕ ]); [mm_wf|mm_fresh| |mm_var].
    mm_var_sub must_inter_g_ty. exact must_inter_program_obl_g_may. }
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_gt (avar a) (vnat 10));
    [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_CtxCase; [mm_wf| | |apply must_inter_program_obl_case_true; mm_wf].
  - eapply EXT_MatchTrueOnly; [mm_wf|mm_var|exact must_inter_then_ge0_typing].
  - eapply EXT_CtxCase; [mm_wf| | |exact must_inter_program_obl_case_false].
    + eapply EXT_MatchFalseOnly; [mm_wf|mm_var|exact must_inter_else_ge0_typing].
    + eapply EXT_Sub; [mm_wf| |apply must_inter_program_obl_sum_ge0; mm_subtype_wf].
      eapply EXT_MatchBoth;
        [mm_wf|mm_var|mm_var|exact must_inter_then_ge0_typing
        |exact must_inter_else_ge0_typing].
Qed.

(** The pre-existing [comprehensive_inter_f_ty] for [must_inter_program]
    with the paper summary [must_inter_g_ty]. *)
Theorem comprehensive_inter_typing :
  ∅; Emp ⊢ₓ must_inter_program ⋮ comprehensive_inter_ref_ty.
Proof.
  unfold must_inter_program, comprehensive_inter_ref_ty, comprehensive_inter_f_ty.
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LamNamedErased; [reflexivity|mm_wf| ].
  eapply EXT_LetNamed with (τ1 := {: ℕ | q_nat_gt0 } ⊓ [: ℕ | q_nat_gt0 ]); [mm_wf| | ].
  { eapply mm_app with (τx := U[ ℕ ]); [mm_wf|mm_fresh| | ].
    - mm_var_sub must_inter_g_ty. exact must_inter_program_obl_g_combined.
    - mm_var_sub (O[ ℕ ] ⊓ U[ ℕ ]). exact must_inter_program_obl_x_inter_under. }
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_gt (avar a) (vnat 10));
    [mm_wf| eapply EXT_BinOp; mm_wf | ].
  eapply EXT_Sub; [mm_wf| |apply must_inter_program_obl_res_eq1; mm_subtype_wf].
  eapply EXT_CtxSub; [mm_wf| |apply must_inter_program_obl_ctx_split; mm_wf].
  eapply EXT_MatchBoth; [mm_wf| mm_var | mm_var | mm_const | mm_var].
Qed.

(** Round-1 name; identical target since round 2. *)
Theorem comprehensive_inter_typing_all :
  ∅; Emp ⊢ₓ must_inter_program ⋮ comprehensive_inter_ref_ty_all.
Proof. exact comprehensive_inter_typing. Qed.

(** ** FINDINGS: semantically false targets / translation issues

    (F7, round 1 — FIXED in round 2) In round 1 the shared [U[b]] was
         [under_ty b qual_top]; [qual_top] does not mention [ν], so that
         under-type was TRIVIAL (it held for every total term), and did not
         mean the paper's [[ν : b | ⊤]].  Since round 2 the shared [U[b]] is
         [under_ty b (q_base_all b)] ("every value of [b] is reachable"),
         which is faithful.  Consequences in this file:
         - the local workaround [q_nat_all] is gone; every round-1 [_all]
           type is an alias of the pre-existing [U[ℕ]]-based type, and the
           [_all] theorems are one-line corollaries;
         - the pre-existing must-summaries [U[ℕ] → [ν ≥ 0]]
           ([must_may_g_ty]) and [U[ℕ] → [ν > 0]] (in [must_inter_g_ty])
           are now exactly the paper's summaries (e.g. [λn. n + 1]
           satisfies them), so [must_may_program_typing],
           [fig6b_program_typing], [must_inter_program_typing_must] and
           [comprehensive_inter_typing] are now the faithful results;
         - [O[ℕ] <: U[ℕ]] is now FALSE (a singleton argument world does not
           reach every natural).  The round-1 obligation
           [fig6b_program_obl_x_over_under] and the derivation
           [fig6b_program_typing_paper_literal] that used it were removed;
           [must_inter_program_typing] was re-derived with T-CtxCase.

    (F1) Figure 6(a), setting (1) — [fig6a_ref_ty_1], paper-literal
         [x:[ν=0] → y:[0≤ν≤10] → [ν=1]] — is semantically FALSE, hence not
         derivable (by any rule, the rules being sound).  In the entangled
         context [g, x:[ν=0], y:[ν≤10]] take the capability (for any [g]
         with [g n ≠ 0])
            [{(x=0, y=11)} ∪ {(x=1, y=n) | n ≤ 10}].
         [x = 0] is reachable and every [y ∈ [0,10]] is reachable, but the
         only store with [x = 0] takes the then-branch, which returns
         [g 0 + 1 ≠ 1]; the else-branch only returns [2].  So [1] is not
         reachable.  (In the arrow denotation the [y]-binding is quantified
         over all extensions of the [x]-world, which may correlate [y] with
         [x].)  The same counterexample (with [x = n ≥ 1] paired with all
         [y]) refutes the pre-existing [may_reach_ref_ty] =
         [x:[⊤] → y:[⊤] → [ν=1]].  [fig6a_setting1_counterexample] checks
         the arithmetic.

    (F2, round 2: RESOLVED) Figure 6(a), setting (2) — [fig6a_ref_ty_2],
         [x:[ν=0] → y:[0≤ν≤10] -∗ [ν=1]] — is semantically valid and is
         now DERIVED ([fig6a_2_typing]) with [EXT_CtxCase]: split on
         whether the capability of [y] reaches some value [> 10]
         (false-only branch vs. both branches; in the latter, [∗] pairs the
         [x = 0] store with [y = 0]).  In round 1 it was not derivable
         (T-Match cannot handle a guard with undetermined reachability).
         The corrected variants [fig6a_1a/2a/2c] remain derived.

    (F3) Figure 6(a), setting (3) — derivable ([fig6a_3_typing], with
         [x:[⊤]] = [U[ℕ]]) with the strongest sound result
         [{ν ≠ 1} ⊕ [ν ≥ 2]]; [ν = 1] is not reachable (reviewer's
         counterexample), the then-branch is the one taken by [x = 0] and
         the may-summary of [g] shows it never yields [1].  Here the
         may-analysis result is genuinely needed (the then-branch summand).

    (F4) Figure 6(b) — the paper's [x:{⊤} → {ν=2} ⊕ {ν=5}] with the
         paper's summary of [g] ([fig6b_ref_ty_paper], equal to the round-1
         [fig6b_ref_ty_paper_all]) is semantically FALSE: [g = λn. n + 1]
         satisfies both [x:{⊤}→{ν>0}] and [x:[⊤]→[ν>0]] (from all
         naturals it reaches all positives), and with the singleton
         capability [x = 0] the only result is [2], so the result world
         cannot be split into a non-empty [ν = 2] part and a non-empty
         [ν = 5] part ([FPlus] needs both summands non-empty).  No rule can
         derive it (the rules are sound).  The argument must be angelic,
         [x:[⊤]]: [fig6b_program_typing] (= [fig6b_program_typing_all]).
         [fig6b_paper_counterexample] checks the arithmetic.

    (F5, round 2: RESOLVED) [must_inter_program] at the pre-existing
         [must_inter_ref_ty] ([x:{⊤} → y:{⊤} → {ν ≥ 0}]) is now DERIVED
         with the paper summary ([must_inter_program_typing]) by two nested
         [EXT_CtxCase] splits on the reachable values of [cond = g x > 10].
         In round 1 it was not derivable with the faithful summary (T-Match
         gap) and only "derived" via the then-true [O[ℕ] <: U[ℕ]].

    (F6) [must_may_program] in the paper's int setting: with the entangled
         [x:[⊤], y:[⊤]] the result [[ν = true]] is not sound (pair every
         [x] with [g x ≥ 0] only with [y]s with [g y < 0]); it needs
         [y:[⊤] -∗ ...].  In ℕ the comparison [0 ≤ g x] is trivially true,
         so the ℕ version is derivable ([must_may_program_typing]).  The
         earlier checkpoint for [&&] in the entangled context was false and
         has been replaced by [must_may_and_true_true_subtype_star].

    (F8) The pre-existing [comprehensive_inter_f_ty]
         [x:({⊤}⊓[⊤]) → y:({⊤}⊓[⊤]) → ({⊤} ⊓ [ν = 1])] (no program was
         attached to it).  It fits the two-argument ℕ programs:
         - with [must_inter_program] and [g : must_inter_g_ty] it is
           derivable ([comprehensive_inter_typing]): [x] is exactly ℕ, so
           [a = g x] reaches every positive, the [cond = false] part has
           [a]-projection exactly [1..10] and the else branch returns [a],
           which reaches [1];
         - with [may_reach_program] and [g : may_reach_g_ty]
           ([comprehensive_reach_ref_ty]) it is FALSE (entangled [→], same
           mechanism as F1): the capability
           [{(x=0, y=11)} ∪ {(x=n, y=m) | n ≥ 1, m ∈ ℕ}] has [x]- and
           [y]-projections exactly ℕ, but [x = 0] is only paired with
           [y = 11] (then-branch, [g 0 + 1 ≠ 1]) and every other store
           returns [g n + 1 ≠ 1] or [n + 1 ≥ 2]; so [1] is unreachable
           ([comprehensive_reach_counterexample]). *)

(** Arithmetic sanity checks of the counterexamples (plain Coq sets of
    stores; they do not involve the Rocq denotation). *)

Definition fig6a_f_impl (gf : nat -> nat) (xv yv : nat) : nat :=
  (match 10 <? yv with true => gf xv + 1 | false => xv + 1 end)%nat.

Definition fig6a_counter_cap (p : nat * nat) : Prop :=
  ((fst p = 0 /\ snd p = 11) \/ (fst p = 1 /\ snd p <= 10))%nat.

Lemma fig6a_setting1_counterexample :
  ((exists p, fig6a_counter_cap p /\ fst p = 0) /\
   (forall n, n <= 10 -> exists p, fig6a_counter_cap p /\ snd p = n) /\
   (forall gf : nat -> nat, (forall n, gf n <> 0) ->
      forall p, fig6a_counter_cap p -> fig6a_f_impl gf (fst p) (snd p) <> 1))%nat.
Proof.
  split; [ |split].
  - exists (0%nat, 11%nat). unfold fig6a_counter_cap. cbn. split; [left; lia|reflexivity].
  - intros n Hn. exists (1%nat, n). unfold fig6a_counter_cap. cbn.
    split; [right; lia|reflexivity].
  - intros gf Hgf [xv yv] [[Hx Hy]|[Hx Hy]]; cbn in *; subst;
      unfold fig6a_f_impl.
    + cbn. specialize (Hgf 0%nat). lia.
    + destruct (10 <? yv) eqn:E.
      * apply Nat.ltb_lt in E. lia.
      * lia.
Qed.

Definition fig6b_counter_g (n : nat) : nat := (n + 1)%nat.

Lemma fig6b_paper_counterexample :
  ((forall n, 0 < fig6b_counter_g n) /\
   (forall m, 0 < m -> exists n, fig6b_counter_g n = m) /\
   (match 3 <? fig6b_counter_g 0 with true => 5 | false => 2 end) = 2)%nat.
Proof.
  unfold fig6b_counter_g. split; [ |split].
  - intros n. lia.
  - intros m Hm. exists (m - 1)%nat. lia.
  - reflexivity.
Qed.

(** (F8): [x]- and [y]-projections are all of ℕ, yet [1] is never
    returned by [may_reach_program]. *)
Definition comprehensive_counter_cap (p : nat * nat) : Prop :=
  ((fst p = 0 /\ snd p = 11) \/ (1 <= fst p))%nat.

Lemma comprehensive_reach_counterexample :
  ((forall n, exists p, comprehensive_counter_cap p /\ fst p = n) /\
   (forall n, exists p, comprehensive_counter_cap p /\ snd p = n) /\
   (forall gf : nat -> nat, (forall n, gf n <> 0) ->
      forall p, comprehensive_counter_cap p ->
        fig6a_f_impl gf (fst p) (snd p) <> 1))%nat.
Proof.
  split; [ |split].
  - intros n. destruct n as [ |n].
    + exists (0%nat, 11%nat). unfold comprehensive_counter_cap. cbn. split; [left; lia|reflexivity].
    + exists (S n, 0%nat). unfold comprehensive_counter_cap. cbn. split; [right; lia|reflexivity].
  - intros n. exists (1%nat, n). unfold comprehensive_counter_cap. cbn.
    split; [right; lia|reflexivity].
  - intros gf Hgf [xv yv] [[Hx Hy]|Hx]; cbn in *; unfold fig6a_f_impl.
    + subst. cbn. specialize (Hgf 0%nat). lia.
    + destruct (10 <? yv) eqn:E.
      * specialize (Hgf xv). lia.
      * lia.
Qed.

(** ** Basic-typing helpers (pre-existing) *)

Lemma basic_type_unary_nat_call Γ (f x : atom) :
  Γ !! f = Some nat_unary_fun_ty ->
  Γ !! x = Some (ℕ : ty) ->
  Γ ⊢ₑ tapp f x ⋮ ℕ.
Proof.
  intros Hf Hx.
  econstructor.
  - constructor. exact Hf.
  - constructor. exact Hx.
Qed.

Lemma basic_type_nat_cmp_first_call Γ (cmp x : atom) :
  Γ !! cmp = Some nat_cmp_ty ->
  Γ !! x = Some (ℕ : ty) ->
  Γ ⊢ₑ tapp cmp x ⋮ (ℕ →ᵦ 𝔹).
Proof.
  intros Hcmp Hx.
  econstructor.
  - constructor. exact Hcmp.
  - constructor. exact Hx.
Qed.

End MayMustExamples.
