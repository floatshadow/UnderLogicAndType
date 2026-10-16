(** * ProofAutomation.ExtendedRuleSoundness

    Semantic soundness of the extra rules of the extended judgment
    [has_extended_context_type] (see [ExtendedTyping]) against the core
    denotation, phrased exactly like the cases of the core
    [ContextTyping.Soundness.Fundamental] theorem:

      premises' semantic validity
        [ctx_denote_under Σ Γi ⊫ ty_denote_under Σ Γi τi ei]
      + the rule's side conditions
      ⟹ [ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e].

    Results (all proofs closed with [Qed]; no axioms beyond the ones already
    used by the core development):

    - [EXT_CtxCase]        : [ext_ctx_case_sound] (the CT_CtxSub argument,
                             once per disjunct of [ctx_case_under]).
    - [EXT_VarComma]       : [ext_var_comma_sound] (the [CtxBind] conjunct of
                             the comma context, transported to [⌊Γ ,, x∷τ⌋]
                             by environment agreement).
    - [EXT_FixUnrollNamed] : [ext_fix_unroll_named_sound], for target types
                             built from arrows (and the vacuous base types)
                             with [⊓]/[∪] ([ext_fix_unroll_shape]) and a
                             locally closed
                             body ([lc_tm body]).  Route: the arrow
                             denotation of a value is characterised without
                             its result variable ([ext_arrow_value_intro] /
                             [ext_arrow_value_elim]), and [fix v] and
                             [unfold v] are equivalent applications
                             ([ext_fix_unroll_tm_equiv]).
                             [ext_fix_unroll_named_sound_ext] extends this
                             to every target type, including top-level
                             [-∗], [⊕], [□] and their combinations with
                             [⊓]/[∪] ([fix_unroll_shape_ext], which holds
                             for all types), via the world-level value
                             transport [ext_vt_main] (swap of the result
                             column from the unfolding to the fix value).
    - Corrected (paper-form) match rules, where the branch context binds the
      pattern variables itself, are proved sound:
      [ext_list_match_cons_paper_rule_sound], [ext_list_match_nil_sound],
      [ext_list_match_both_paper_rule_sound],
      [ext_tree_match_node_paper_rule_sound], [ext_tree_match_leaf_sound],
      [ext_tree_match_both_paper_rule_sound] (scrutinee a variable).
    - [EXT_ListMatchConsOnlyNamed] (and, by the same mechanism, the other
      three named match rules [EXT_ListMatchBothNamed],
      [EXT_TreeMatchBothNamed], [EXT_TreeMatchNodeOnlyNamed]) is UNSOUND as
      stated:
      [ext_list_match_cons_only_named_unsound] derives
      [∅; Emp ⊢ₓ match [1] with nil => 0 | cons hd tl => 0 ⋮ {ν:ℕ | False}]
      whose semantics is false.  The rule never relates the models of [Γ] to
      the models of [Γ ,, Γpat]; with an unmodelable [Γpat] every branch
      premise is vacuous. *)

From Stdlib Require Import List.
From CoreLang Require Import BasicTyping BasicTypingProps SmallStep Sugar
  LocallyNamelessProps LocallyNamelessExtra InstantiationProps OperationalProps
  StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextLogic Require Import FormulaConnectives FormulaConnectivesHigher.
From ContextBasicDenotation Require Import BasicTypingFormula RelevantEnv TermExtension TermOpen TermEval.
From Denotation Require Import Context TypeEquivCore TypeEquiv TypeEquivTermBase DenotationSetMapFacts.
From ContextTyping Require Import PrimOpContext PrimOpConcreteContext Typing SoundnessFix
  Soundness SoundnessLam.
From ProofAutomation Require Import CaseSyntax ExtendedTyping ExtendedSubsumption
  ExtendedTypeInfer CaseBasicAutomation.

Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation StoreT := (gmap atom value) (only parsing).

From Denotation Require Import ResultFirstOpen TypeEquivArrow TypeEquivBody TypeEquivFiberBaseCore.

(** ** T-CtxCase *)

(** One-world version of the CT_CtxSub argument of
    [Soundness.fundamental_ctx_sub_case]. *)
Lemma ext_ctx_transfer_one (Σ : gmap atom ty) (Γ1 Γ2 : ctx)
    (e : tm) (τ : context_ty) (m m' : WfWorldT) :
  context_typing_wf Σ Γ1 e τ ->
  ty_env_agree_on (fv_tm e ∪ fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) ->
  m ⊨ ctx_denote_under Σ Γ1 ->
  res_restrict m (fv_tm e ∪ fv_cty τ) ⊑ m' ->
  m' ⊨ ty_denote_under Σ Γ2 τ e ->
  m ⊨ ty_denote_under Σ Γ1 τ e.
Proof.
  intros Hwf Hagree HΓ1 Hle Hden2.
  assert (Hden1_m' : m' ⊨ ty_denote_under Σ Γ1 τ e).
  {
    unfold ty_denote_under, ty_denote in Hden2 |- *.
    eapply res_models_ty_denote_gas_env_agree_on
      with (X := relevant_lvars τ e); [reflexivity | | exact Hden2].
    apply atom_env_to_lty_env_restrict_lvars_agree_on
      with (X := fv_tm e ∪ fv_cty τ).
    - intros x Hx. symmetry. apply Hagree. exact Hx.
    - relevant_lvars_norm. better_set_solver.
  }
  eapply res_models_from_restrict_extension_on_fv
    with (X := fv_tm e ∪ fv_cty τ) (n := m').
  - unfold ty_denote_under, ty_denote.
    apply formula_fv_ty_denote_gas_subset_relevant.
  - unfold ty_denote_under, ty_denote.
    pose proof (formula_fv_ty_denote_gas_subset_relevant
      (cty_depth τ) (atom_env_to_lty_env (erase_ctx Γ1)) τ e) as Hfvden.
    intros a Ha.
    pose proof (Hfvden a Ha) as Ha'.
    pose proof (context_typing_wf_fv_tm_subset Σ Γ1 e τ Hwf) as Htm.
    pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γ1 e τ Hwf) as Hτfv.
    pose proof (ctx_denote_under_basic_world Σ Γ1 m HΓ1) as Hworld.
    pose proof (basic_world_formula_atom_env_dom_subset
      (ctx_erasure_under Σ Γ1) m Hworld) as Hdom.
    apply Hdom.
    apply ctx_erasure_under_erase_ctx_dom_subset.
    apply elem_of_union in Ha' as [Ha' | Ha'].
    + exact (Htm a Ha').
    + exact (Hτfv a Ha').
  - exact Hle.
  - exact Hden1_m'.
Qed.

Lemma ext_ctx_case_sound (Σ : gmap atom ty) (Γ Γa Γb : ctx)
    (e : tm) (τ : context_ty) :
  context_typing_wf Σ Γ e τ ->
  ctx_case_under Σ (fv_tm e ∪ fv_cty τ) Γ Γa Γb ->
  (ctx_denote_under Σ Γa ⊫ ty_denote_under Σ Γa τ e) ->
  (ctx_denote_under Σ Γb ⊫ ty_denote_under Σ Γb τ e) ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
Proof.
  intros Hwf Hcase IHa IHb m HΓ.
  destruct Hcase as [_ [_ [_ [Hagreea [Hagreeb Hcase]]]]].
  destruct (Hcase m HΓ) as [m' [Hle [Ha | Hb]]].
  - eapply (ext_ctx_transfer_one Σ Γ Γa e τ m m'); eauto.
  - eapply (ext_ctx_transfer_one Σ Γ Γb e τ m m'); eauto.
Qed.

(** ** T-VarComma *)

Lemma ext_var_comma_sound (Σ : gmap atom ty) (Γ : ctx) (x : atom)
    (τ : context_ty) :
  context_typing_wf Σ (CtxComma Γ (CtxBind x τ)) (tret (vfvar x)) τ ->
  ctx_denote_under Σ (CtxComma Γ (CtxBind x τ)) ⊫
    ty_denote_under Σ (CtxComma Γ (CtxBind x τ)) τ (tret (vfvar x)).
Proof.
  intros Hwf m Hctx.
  pose proof (context_typing_wf_ctx _ _ _ _ Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic _ _ Hwfctx) as Hbasic.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf) as Hτfv.
  cbn [basic_ctx] in Hbasic.
  destruct Hbasic as [HbΓ [[Hxfresh Hτbasic] _]].
  pose proof (basic_ctx_erase_dom _ _ HbΓ) as HdomΓ.
  pose proof (basic_context_ty_fv_subset _ _ Hτbasic) as Hτfv2.
  cbn [ctx_denote_under] in Hctx.
  rewrite !res_models_and_iff in Hctx.
  destruct Hctx as [_ [_ [_ Hbind]]].
  unfold ty_denote_under, ty_denote in Hbind |- *.
  eapply res_models_ty_denote_gas_env_agree_on
    with (X := relevant_lvars τ (tret (vfvar x)));
    [reflexivity | | exact Hbind].
  apply atom_env_to_lty_env_restrict_lvars_agree_on
    with (X := fv_cty τ ∪ {[x]}).
  2:{ relevant_lvars_norm. better_set_solver. }
  intros y Hy.
  cbn [erase_ctx ctx_fv].
  destruct (decide (y = x)) as [->|Hyx].
  - transitivity (Some (erase_ty τ)); [apply map_lookup_insert| ].
    symmetry. apply map_lookup_union_Some_raw. right. split.
    + apply not_elem_of_dom. rewrite HdomΓ. set_solver.
    + apply map_lookup_singleton.
  - assert (HyΓ : y ∈ ctx_dom Γ).
    { cbn [erase_ctx] in Hτfv.
      assert (y ∈ fv_cty τ) by set_solver.
      pose proof (Hτfv y ltac:(assumption)) as Hy'.
      apply elem_of_dom in Hy' as [T' HT'].
      apply map_lookup_union_Some_raw in HT' as [HT'|[_ HT']].
      - rewrite <- HdomΓ. apply elem_of_dom. eauto.
      - change (({[x := erase_ty τ]} : gmap atom ty) !! y = Some T') in HT'.
        apply (proj1 (lookup_singleton_Some x y (erase_ty τ) T')) in HT' as [? _]. congruence. }
    assert (HΣy : Σ !! y = None).
    { apply not_elem_of_dom. intros HΣ.
      pose proof (basic_ctx_dom_fresh _ _ HbΓ). set_solver. }
    transitivity ((erase_ctx Γ : gmap atom ty) !! y).
    + etransitivity; [apply map_lookup_insert_ne; congruence| ].
      rewrite storeA_restrict_lookup.
      destruct (decide (y ∈ fv_cty τ)) as [Hyτ|Hyτ]; [ |set_solver].
      apply lookup_union_r.
      apply storeA_restrict_lookup_none_l. exact HΣy.
    + symmetry. apply lookup_union_l.
      apply map_lookup_singleton_ne. congruence.
Qed.

(** ** T-FixUnrollNamed *)

(** ** Syntax of the one-step unfolding *)

Lemma ext_lc_lam_named x T e :
  lc_tm e -> lc_value (lam_named x T e).
Proof.
  intros He. unfold lam_named.
  apply lc_lam_iff_body. exists (fv_tm e ∪ {[x]}). intros z Hz.
  change (lc_tm (open_tm 0 (vfvar z) (close_tm x 0 e))).
  rewrite <- (subst_intro_tm x (vfvar z) 0 (close_tm x 0 e))
    by (apply close_rm_fv_tm || constructor).
  rewrite open_close_var_tm by exact He.
  apply subst_lc_tm; [exact He|constructor].
Qed.

Lemma ext_fixfun_named_lc self arg sx t body :
  lc_tm body -> lc_value (fixfun_named self arg sx t body).
Proof.
  intros Hb. unfold fixfun_named.
  apply lc_fix_iff_body. exists (fv_tm body ∪ {[arg]}). intros z Hz.
  change (lc_value (open_value 0 (vfvar z)
    (close_value arg 0 (lam_named self (sx →ₜ t) body)))).
  rewrite <- (subst_intro_value arg (vfvar z) 0
    (close_value arg 0 (lam_named self (sx →ₜ t) body)))
    by (apply close_rm_fv_value || constructor).
  rewrite open_close_var_value by (apply ext_lc_lam_named; exact Hb).
  apply subst_lc_value; [apply ext_lc_lam_named; exact Hb|constructor].
Qed.

Lemma ext_fixfun_named_arg_fresh self arg sx t body :
  arg ∉ fv_value (fixfun_named self arg sx t body).
Proof.
  unfold fixfun_named. cbn [fv_value]. apply close_rm_fv_value.
Qed.

(** The fix step followed by the beta step of [fixfun_named] lands on the
    same term as the beta step of its unfolding. *)
Lemma ext_fixfun_unfold_open_eq self arg sx t body (y : atom) :
  lc_tm body ->
  y <> self ->
  y <> arg ->
  open_value 0 (vfvar y)
    (close_value arg 0 (lam_named self (sx →ₜ t) body)) =
  vlam (sx →ₜ t)
    (close_tm self 0
      (match decide (self = arg) with left _ => body | right _ => tm_subst arg (vfvar y) body end)) /\
  open_tm 0 (fixfun_named self arg sx t body)
    (close_tm self 0
      (match decide (self = arg) with left _ => body | right _ => tm_subst arg (vfvar y) body end)) =
  open_tm 0 (vfvar y)
    (close_tm arg 0 (tm_subst self (fixfun_named self arg sx t body) body)).
Proof.
  intros Hb Hyself Hyarg.
  set (fx := fixfun_named self arg sx t body).
  assert (Hfx_lc : lc_value fx) by (apply ext_fixfun_named_lc; exact Hb).
  assert (Hfx_arg : arg ∉ fv_value fx) by apply ext_fixfun_named_arg_fresh.
  split.
  - rewrite <- (subst_intro_value arg (vfvar y) 0
      (close_value arg 0 (lam_named self (sx →ₜ t) body)))
      by (apply close_rm_fv_value || constructor).
    rewrite open_close_var_value by (apply ext_lc_lam_named; exact Hb).
    unfold lam_named. cbn [value_subst].
    f_equal.
    destruct (decide (self = arg)) as [->|Hne].
    + apply subst_fresh_tm_proven. apply close_rm_fv_tm.
    + symmetry. apply subst_close_tm.
      * cbn [fv_value]. set_solver.
      * exact Hne.
  - assert (HS : lc_tm (tm_subst self fx body)).
    { apply subst_lc_tm; assumption. }
    rewrite <- (subst_intro_tm arg (vfvar y) 0
      (close_tm arg 0 (tm_subst self fx body)))
      by (apply close_rm_fv_tm || constructor).
    rewrite open_close_var_tm by exact HS.
    destruct (decide (self = arg)) as [->|Hne].
    + rewrite <- (subst_intro_tm arg fx 0 (close_tm arg 0 body))
        by (apply close_rm_fv_tm || exact Hfx_lc).
      rewrite open_close_var_tm by exact Hb.
      symmetry. apply subst_fresh_tm_proven.
      intros Hin. apply fv_of_subst_tm in Hin. set_solver.
    + assert (HS2 : lc_tm (tm_subst arg (vfvar y) body)).
      { apply subst_lc_tm; [exact Hb|constructor]. }
      rewrite <- (subst_intro_tm self fx 0
        (close_tm self 0 (tm_subst arg (vfvar y) body)))
        by (apply close_rm_fv_tm || exact Hfx_lc).
      rewrite open_close_var_tm by exact HS2.
      apply subst_commute_tm.
      * exact Hne.
      * cbn [fv_value]. set_solver.
      * exact Hfx_arg.
Qed.

(** ** Evaluation of a beta-redex with an arbitrary value argument *)

Lemma ext_body_msubst σ e :
  store_closed σ -> body_tm e -> body_tm (m{σ} e).
Proof.
  intros Hclosed Hbody.
  exists (fv_tm e ∪ dom σ). intros z Hz.
  change (lc_tm (open_tm 0 (vfvar z) (m{σ} e))).
  assert (Hfreshz : m{σ} (vfvar z) = vfvar z).
  { apply msubst_fvar_lookup_none_closed.
    - exact (proj1 Hclosed).
    - apply not_elem_of_dom. set_solver. }
  rewrite <- Hfreshz.
  change (lc_tm ({0 ~> m{σ} (vfvar z)} (m{σ} e))).
  rewrite <- (msubst_open e 0 (vfvar z) σ)
    by (exact (proj1 Hclosed) || exact (proj2 Hclosed) || constructor).
  apply msubst_lc; [exact (proj2 Hclosed)| ].
  apply body_open_tm; [exact Hbody|constructor].
Qed.

Lemma ext_tm_eval_in_store_tapp_tm_lam_value σ T e w v :
  store_closed σ ->
  body_tm e ->
  lc_value w ->
  tm_eval_in_store σ (tapp_tm (tret (vlam T e)) w) v <->
  tm_eval_in_store σ (open_tm 0 w e) v.
Proof.
  intros Hclosed Hbody Hw.
  assert (Hwσ : lc_value (m{σ} w)).
  { apply msubst_lc; [exact (proj2 Hclosed)|exact Hw]. }
  pose proof (ext_body_msubst σ e Hclosed Hbody) as Hbodyσ.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite msubst_tapp_tm_lc_arg by (exact Hw || exact (proj2 Hclosed)).
    rewrite msubst_ret, msubst_vlam.
    change (m{σ} (open_tm 0 w e)) with (m{σ} ({0 ~> w} e)).
    rewrite (msubst_open e 0 w σ)
      by (exact (proj1 Hclosed) || exact (proj2 Hclosed) || exact Hw).
    rewrite (steps_tapp_tm_ret_equiv (vlam T (m{σ} e)) (m{σ} w) v).
    + apply reduction_beta_iff; [exact Hbodyσ|exact Hwσ].
    + apply lc_lam_iff_body. exact Hbodyσ.
    + exact Hwσ.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma ext_tm_must_terminating_tapp_tm_lam_value σ T e w :
  store_closed σ ->
  body_tm e ->
  lc_value w ->
  must_terminating
    (lstore_instantiate_tm (lstore_lift_free σ)
      (tapp_tm (tret (vlam T e)) w)) <->
  must_terminating
    (lstore_instantiate_tm (lstore_lift_free σ) (open_tm 0 w e)).
Proof.
  intros Hclosed Hbody Hw.
  assert (Hwσ : lc_value (m{σ} w)).
  { apply msubst_lc; [exact (proj2 Hclosed)|exact Hw]. }
  pose proof (ext_body_msubst σ e Hclosed Hbody) as Hbodyσ.
  rewrite !lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite !lstore_free_part_lift_free.
  rewrite !subst_map_tm_eq_msubst.
  rewrite msubst_tapp_tm_lc_arg by (exact Hw || exact (proj2 Hclosed)).
  rewrite msubst_ret, msubst_vlam.
  change (m{σ} (open_tm 0 w e)) with (m{σ} ({0 ~> w} e)).
  rewrite (msubst_open e 0 w σ)
    by (exact (proj1 Hclosed) || exact (proj2 Hclosed) || exact Hw).
  rewrite must_terminating_tapp_tm_ret_equiv.
  - apply must_terminating_lam_app_equiv.
    apply LC_app; [ |exact Hwσ].
    apply lc_lam_iff_body. exact Hbodyσ.
  - apply lc_lam_iff_body. exact Hbodyσ.
  - exact Hwσ.
Qed.

(** ** [fix] and its one-step unfolding are applicatively equivalent *)

Definition ext_fix_unfolding (self arg : atom) (sx t : ty) (body : tm) : value :=
  lam_named arg sx
    (tm_subst self (fixfun_named self arg sx t body) body).

Lemma ext_fix_unroll_eval_store σ self arg sx t body y vy v :
  store_closed σ ->
  σ !! y = Some vy ->
  lc_tm body ->
  y <> self -> y <> arg ->
  y ∉ fv_value (ext_fix_unfolding self arg sx t body) ->
  tm_eval_in_store σ
    (tapp_tm (tret (fixfun_named self arg sx t body)) (vfvar y)) v <->
  tm_eval_in_store σ
    (tapp_tm (tret (ext_fix_unfolding self arg sx t body)) (vfvar y)) v.
Proof.
  intros Hclosed Hσy Hb Hyself Hyarg Hyunf.
  set (fx := fixfun_named self arg sx t body).
  assert (Hfx_lc : lc_value fx) by (apply ext_fixfun_named_lc; exact Hb).
  destruct (ext_fixfun_unfold_open_eq self arg sx t body y Hb Hyself Hyarg)
    as [Hopen Hbeta].
  fold fx in Hbeta.
  set (S := match decide (self = arg) with
            | left _ => body | right _ => tm_subst arg (vfvar y) body end)
    in Hopen, Hbeta.
  assert (Hbody_vf : body_val (close_value arg 0 (lam_named self (sx →ₜ t) body))).
  { apply lc_fix_iff_body with (Tf := sx →ₜ t). exact Hfx_lc. }
  assert (Hbody_e1 : body_tm (close_tm self 0 S)).
  {
    apply lc_lam_iff_body with (s := sx →ₜ t).
    rewrite <- Hopen.
    apply body_open_value; [exact Hbody_vf|constructor].
  }
  assert (Hunf_lc : lc_value (ext_fix_unfolding self arg sx t body)).
  { apply ext_lc_lam_named. apply subst_lc_tm; assumption. }
  assert (Hbody_e2 :
      body_tm (close_tm arg 0 (tm_subst self fx body))).
  { apply lc_lam_iff_body with (s := sx). exact Hunf_lc. }
  unfold fx.
  unfold fixfun_named at 1.
  rewrite (tm_eval_in_store_tapp_tm_fix_unfold σ (sx →ₜ t)
    (close_value arg 0 (lam_named self (sx →ₜ t) body)) y vy v Hclosed Hbody_vf Hσy).
  rewrite Hopen.
  change (vfix (sx →ₜ t) (close_value arg 0 (lam_named self (sx →ₜ t) body)))
    with fx.
  rewrite (ext_tm_eval_in_store_tapp_tm_lam_value σ (sx →ₜ t)
    (close_tm self 0 S) fx v Hclosed Hbody_e1 Hfx_lc).
  rewrite Hbeta.
  unfold ext_fix_unfolding, lam_named.
  fold fx.
  rewrite (tm_eval_in_store_tapp_tm_lam_body σ sx
    (close_tm arg 0 (tm_subst self fx body)) y vy v Hclosed Hbody_e2).
  - reflexivity.
  - exact Hyunf.
  - exact Hσy.
Qed.

Lemma ext_fix_unroll_total_store σ self arg sx t body y vy :
  store_closed σ ->
  σ !! y = Some vy ->
  lc_tm body ->
  y <> self -> y <> arg ->
  y ∉ fv_value (ext_fix_unfolding self arg sx t body) ->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
    (tapp_tm (tret (fixfun_named self arg sx t body)) (vfvar y))) <->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
    (tapp_tm (tret (ext_fix_unfolding self arg sx t body)) (vfvar y))).
Proof.
  intros Hclosed Hσy Hb Hyself Hyarg Hyunf.
  set (fx := fixfun_named self arg sx t body).
  assert (Hfx_lc : lc_value fx) by (apply ext_fixfun_named_lc; exact Hb).
  destruct (ext_fixfun_unfold_open_eq self arg sx t body y Hb Hyself Hyarg)
    as [Hopen Hbeta].
  fold fx in Hbeta.
  set (S := match decide (self = arg) with
            | left _ => body | right _ => tm_subst arg (vfvar y) body end)
    in Hopen, Hbeta.
  assert (Hbody_vf : body_val (close_value arg 0 (lam_named self (sx →ₜ t) body))).
  { apply lc_fix_iff_body with (Tf := sx →ₜ t). exact Hfx_lc. }
  assert (Hbody_e1 : body_tm (close_tm self 0 S)).
  {
    apply lc_lam_iff_body with (s := sx →ₜ t).
    rewrite <- Hopen.
    apply body_open_value; [exact Hbody_vf|constructor].
  }
  assert (Hunf_lc : lc_value (ext_fix_unfolding self arg sx t body)).
  { apply ext_lc_lam_named. apply subst_lc_tm; assumption. }
  assert (Hbody_e2 :
      body_tm (close_tm arg 0 (tm_subst self fx body))).
  { apply lc_lam_iff_body with (s := sx). exact Hunf_lc. }
  unfold fx.
  unfold fixfun_named at 1.
  rewrite (tm_must_terminating_tapp_tm_fix_unfold σ (sx →ₜ t)
    (close_value arg 0 (lam_named self (sx →ₜ t) body)) y vy Hclosed Hbody_vf Hσy).
  rewrite Hopen.
  change (vfix (sx →ₜ t) (close_value arg 0 (lam_named self (sx →ₜ t) body)))
    with fx.
  rewrite (ext_tm_must_terminating_tapp_tm_lam_value σ (sx →ₜ t)
    (close_tm self 0 S) fx Hclosed Hbody_e1 Hfx_lc).
  rewrite Hbeta.
  unfold ext_fix_unfolding, lam_named.
  fold fx.
  rewrite (tm_must_terminating_tapp_tm_lam_body σ sx
    (close_tm arg 0 (tm_subst self fx body)) y vy Hclosed Hbody_e2).
  - reflexivity.
  - exact Hyunf.
  - exact Hσy.
Qed.

Lemma ext_fix_unroll_tm_equiv (n : WfWorldT) self arg sx t body y :
  lc_tm body ->
  y <> self -> y <> arg ->
  y ∉ fv_value (ext_fix_unfolding self arg sx t body) ->
  y ∈ world_dom (n : WorldT) ->
  wfworld_closed_on
    (fv_value (fixfun_named self arg sx t body) ∪
     fv_value (ext_fix_unfolding self arg sx t body) ∪ {[y]}) n ->
  tm_equiv_on n
    (tapp_tm (tret (fixfun_named self arg sx t body)) (vfvar y))
    (tapp_tm (tret (ext_fix_unfolding self arg sx t body)) (vfvar y)) /\
  tm_total_equiv_on n
    (tapp_tm (tret (fixfun_named self arg sx t body)) (vfvar y))
    (tapp_tm (tret (ext_fix_unfolding self arg sx t body)) (vfvar y)).
Proof.
  intros Hb Hyself Hyarg Hyunf Hy_dom Hclosed.
  set (X := fv_value (fixfun_named self arg sx t body) ∪
     fv_value (ext_fix_unfolding self arg sx t body) ∪ {[y]}).
  assert (Hfv_fix :
      fv_tm (tapp_tm (tret (fixfun_named self arg sx t body)) (vfvar y)) ⊆ X).
  { subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    rewrite value_shift_fv. set_solver. }
  assert (Hfv_unf :
      fv_tm (tapp_tm (tret (ext_fix_unfolding self arg sx t body)) (vfvar y)) ⊆ X).
  { subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    rewrite value_shift_fv. set_solver. }
  assert (Hfx_lc : lc_value (fixfun_named self arg sx t body))
    by (apply ext_fixfun_named_lc; exact Hb).
  assert (Hunf_lc : lc_value (ext_fix_unfolding self arg sx t body)).
  { apply ext_lc_lam_named. apply subst_lc_tm; assumption. }
  split.
  - intros σ v Hσ.
    assert (HσX_closed : store_closed (store_restrict σ X)).
    { eapply wfworld_closed_on_store_restrict_closed; eauto. }
    pose proof (wfworld_store_dom n σ Hσ) as Hσdom.
    destruct (σ !! y) as [vy| ] eqn:Hσy.
    2:{ apply not_elem_of_dom in Hσy. set_solver. }
    assert (HσXy : store_restrict σ X !! y = Some vy).
    { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσy). subst X. set_solver. }
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ _ v X Hfv_fix).
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ _ v X Hfv_unf).
    apply ext_fix_unroll_eval_store with (vy := vy); assumption.
  - intros σ Hσ.
    assert (HσX_closed : store_closed (store_restrict σ X)).
    { eapply wfworld_closed_on_store_restrict_closed; eauto. }
    pose proof (wfworld_store_dom n σ Hσ) as Hσdom.
    destruct (σ !! y) as [vy| ] eqn:Hσy.
    2:{ apply not_elem_of_dom in Hσy. set_solver. }
    assert (HσXy : store_restrict σ X !! y = Some vy).
    { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσy). subst X. set_solver. }
    assert (Hlc_fix_app :
        lc_tm (tapp_tm (tret (fixfun_named self arg sx t body)) (vfvar y))).
    { apply lc_tapp_tm; [constructor; exact Hfx_lc|constructor]. }
    assert (Hlc_unf_app :
        lc_tm (tapp_tm (tret (ext_fix_unfolding self arg sx t body)) (vfvar y))).
    { apply lc_tapp_tm; [constructor; exact Hunf_lc|constructor]. }
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) _ Hlc_fix_app).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_fix]. }
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) _ Hlc_unf_app).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_unf]. }
    apply ext_fix_unroll_total_store with (vy := vy); assumption.
Qed.

Lemma ext_v_arrow_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ v
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret v) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret v) (vfvar y)).
Proof.
  intros Hwf Hy Hctx_comma.
  assert (Hwf_app :
      context_typing_wf Σ (CtxComma Γ (CtxBind y τx))
        (tapp_tm (tret v) (vfvar y))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ Γ
      (tret v) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret v) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx Hτ].
    split.
    + unfold wf_ctx_under. cbn [basic_ctx]. split; [exact HbasicΓ| ]. split.
      * apply basic_ctx_bind.
        -- ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ. better_set_solver.
        -- eapply (wf_context_ty_at_mono_env
             0 (dom (erase_ctx Γ)) (dom Σ ∪ ctx_dom Γ)).
           ++ rewrite HdomΓ. set_solver.
           ++ exact Hτx.
      * cbn [ctx_dom]. ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ.
        better_set_solver.
    + split.
      * eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxComma Γ (CtxBind y τx))))).
        -- rewrite erase_ctx_comma_bind_dom. reflexivity.
        -- apply wf_context_ty_at_open_at.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact Hτ.
      * rewrite cty_open_preserves_erasure.
        replace (erase_ctx (CtxComma Γ (CtxBind y τx)))
          with (<[y := erase_ty τx]> (erase_ctx Γ)).
        -- apply basic_typing_tapp_tm_fvar_insert.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact (context_typing_wf_basic_typing Σ Γ
                (tret v) (CTArrow τx τ) Hwf).
        -- symmetry. apply erase_ctx_comma_bind_fresh.
           ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  pose proof (context_typing_wf_denot_static_guard_full
    Σ (CtxComma Γ (CtxBind y τx)) (cty_open 0 y τ)
    (tapp_tm (tret v) (vfvar y))
    my Hwf_app Hctx_comma) as Hstatic.
  assert (Henv :
      atom_env_to_lty_env (erase_ctx (CtxComma Γ (CtxBind y τx))) =
      (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))).
  {
    rewrite erase_ctx_comma_bind_fresh.
    - apply atom_store_to_lvar_store_insert.
    - ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  rewrite Henv in Hstatic.
  exact Hstatic.
Qed.

Lemma ext_v_arrow_open_arg_mid_to_bind_denotation
    (Σ : tyctx) Γ τx τ v
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret v) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Hmid.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret v) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hτx_fv : fv_cty τx ⊆ dom (erase_ctx Γ)).
  {
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret v) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    eapply wf_context_ty_at_fv_subset. exact Hτx.
  }
  eapply ty_denote_gas_ret_fvar_insert_ctx_erasure_under; eauto.
Qed.

Lemma ext_v_arrow_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ v
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret v) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  rewrite ty_denote_gas_saturate in Harg by lia.
  eapply ext_v_arrow_open_arg_mid_to_bind_denotation; eauto.
Qed.

Lemma ext_v_arrow_open_arg_to_bind_ctx
    (Σ : tyctx) Γ τx τ v
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret v) (CTArrow τx τ) ->
  my ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
  intros Hwf Hctx_my Hdom Hrestrict Hy Harg.
  pose proof (ext_v_arrow_open_arg_to_bind_denotation
    Σ Γ τx τ v my y Hwf Hy Harg)
    as Hbind_den.
  eapply ctx_bind_from_inserted_erasure_arg_denotation.
  - ctx_erasure_under_norm_in Hy. better_set_solver.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret v) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret v) (CTArrow τx τ) Hwf) as Hτwf.
    cbn [wf_context_ty_at] in Hτwf.
    destruct Hτwf as [Hτx _].
    pose proof (wf_context_ty_at_fv_subset 0 (dom (erase_ctx Γ)) τx Hτx)
      as Hτxfv.
    unfold ty_env_agree_on. intros z Hz.
    assert (HzΓ : z ∈ dom (erase_ctx Γ)).
    { apply Hτxfv. exact Hz. }
    pose proof (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
      Σ Γ z HbasicΓ HzΓ) as Herase.
    assert (HΣnone : Σ !! z = None).
    { eapply basic_ctx_erase_dom_fresh_none; eauto. }
    transitivity ((erase_ctx Γ : gmap atom ty) !! z).
    + apply lookup_union_r. exact HΣnone.
    + exact Herase.
  - exact Hctx_my.
  - exact Hbind_den.
Qed.

Lemma ext_v_arrow_open_arg_to_comma_ctx
    (Σ : tyctx) Γ τx τ v
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret v) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros Hwf Hctx Hdom Hrestrict Hy Harg.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret v) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  assert (Hctx_my : my ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact Hctx_my| ].
  eapply ext_v_arrow_open_arg_to_bind_ctx; eauto.
Qed.

Lemma ext_v_result_first_outer_result_plain
    (Σ : tyctx) Γ τx τ v
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret v) (CTArrow τx τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret v))))
      (tm_shift 0 (tret v)) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret v) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v))))).
		  {
		    rewrite lvars_shift_from_fv.
		    intros Hzbad.
		    apply lvars_fv_elem in Hzbad.
		    pose proof (soundness_relevant_env_arrow_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      v z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver))
		      as Hnot.
		    exact (Hnot Hzbad).
		  }
  assert (Hlc_elam :
      lc_tm (tret v)).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret v) (CTArrow τx τ) Hwf).
  }
  assert (Hz_elam :
      z ∉ fv_tm (tret v)).
  {
    cbn [fv_tm fv_value].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_elam || exact Hz_elam).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret v)))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret v))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret v)))).
  - intros lv Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret v) (CTArrow τx τ) Hwf)
        as Hfv.
      destruct lv as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret v) (CTArrow τx τ) Hwf)
          as Hlc.
        exfalso.
        pose proof (tm_lvars_lc _ Hlc (LVBound k) Hv) as [].
	      * rewrite atom_store_to_lvar_store_dom.
	        apply elem_of_map. exists a. split; [reflexivity| ].
	        apply Hfv.
	        rewrite <- tm_lvars_fv.
	        apply (proj2 (lvars_fv_elem _ _)).
	        exact Hv.
    + unfold relevant_lvars. set_solver.
	  - set_solver.
		  - intros Hzbad.
		    pose proof (soundness_relevant_env_arrow_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      v z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
		    exact (Hnot Hzbad).
	  - exact Hres.
  Qed.
(** ** Arrow denotation of a value, without the result variable *)

Definition ext_arrow_app_prop (Σ : gmap atom ty) (Γ : ctx)
    (τx τ : context_ty) (v : value) (m : WfWorldT) : Prop :=
  exists L : aset, forall y (n : WfWorldT),
    y ∉ L ->
    world_dom (n : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
    res_restrict n (world_dom (m : WorldT)) = m ->
    n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ)))
      τx (tret (vfvar y)) ->
    n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ)))
      (cty_open 0 y τ) (tapp_tm (tret v) (vfvar y)).

Lemma ext_ctx_world_dom_fv (Σ : gmap atom ty) Γ e τ (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  dom (erase_ctx Γ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hwf Hctx a Ha.
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m Hworld) as Hdom.
  apply Hdom. apply ctx_erasure_under_erase_ctx_dom_subset. exact Ha.
Qed.

Lemma ext_v_result_first_arrow_value_denotation
    Σ Γ τx τ v (m mz : WfWorldT) z :
  context_typing_wf Σ Γ (tret v) (CTArrow τx τ) ->
  ext_arrow_app_prop Σ Γ τx τ v m ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ world_dom (m : WorldT) ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (arrow_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree z := erase_ty (CTArrow τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret v)))
      τx τ (tret (vfvar z))) ->
  mz ⊨ expr_result_formula (tret v) (LVFree z) ->
  mz ⊨ arrow_value_denote_gas_with ty_denote_gas
    (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree z := erase_ty (CTArrow τx τ)]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret v)))
    τx τ (tret (vfvar z)).
Proof.
  intros Hwf [LP HP] Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (efix := tret v).
  set (vself := v).
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTArrow τx τ) efix).
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (ext_ctx_world_dom_fv Σ Γ _ _ m Hwf Hctx) as HΓm.
  pose proof (context_typing_wf_context_ty
    Σ Γ efix (CTArrow τx τ) Hwf) as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  pose proof (wf_context_ty_at_fv_subset _ _ _ Hτx_wf) as Hτx_fv.
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  eapply res_models_forall_rev_intro; [exact Hscope_value| ].
  exists (LP ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪
    fv_cty τ ∪ {[z]}).
  intros y Hy my Hdomy Hrestricty.
  assert (Hle_mz_my : mz ⊑ my).
  { rewrite <- Hrestricty. apply res_restrict_le. }
  assert (Hy_world : y ∈ world_dom (my : WorldT)).
  { rewrite Hdomy. apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
  cbn [formula_open arrow_value_denote_gas_with] in Hscope_value |- *.
  pose proof (formula_scoped_forall_open_res_le
    mz my y _ Hscope_value Hle_mz_my Hy_world) as Hopened_scope.
  cbn [formula_open] in Hopened_scope |- *.
  eapply res_models_impl_intro; [exact Hopened_scope| ].
  intros Harg_raw.
  assert (Hy_fresh :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value v ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  { clear -Hy. better_set_solver. }
  assert (Hy_rest :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value v ∪ fv_cty τx ∪ fv_cty τ).
  { clear -Hy_fresh. better_set_solver. }
  assert (Harg_norm :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        τx (tret (vfvar y))).
  {
    change (my ⊨ formula_open 0 y
      (ty_denote_gas gas
        (typed_lty_env_bind
          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))))
      in Harg_raw.
    rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
      y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
      τx) in Harg_raw.
    2:{ apply lty_env_closed_insert_free.
        subst Σrel Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
    2:{
      rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      - apply elem_of_singleton in Hin. inversion Hin. subst.
        clear -Hy_fresh. set_solver.
      - exfalso.
        subst Σrel Δ efix.
        pose proof (soundness_relevant_env_arrow_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) τx τ v y
          ltac:(clear -Hy_fresh; better_set_solver))
          as Hnot.
        exact (Hnot Hin).
    }
    2:{ clear -Hy_fresh. better_set_solver. }
    2:{ exact Hτx_lc. }
    exact Harg_raw.
  }
  assert (Harg_old :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree y := erase_ty τx]>
        (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - rewrite lty_env_insert_free_commute by (clear -Hy_fresh; set_solver).
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy_fresh Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTArrow τx τ)) Hz_rel_arg).
      apply lam_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst efix vself. cbn [fv_tm].
        clear -Hy_fresh. better_set_solver.
    - exact Harg_norm.
  }
  (* The application, obtained from the z-free property [HP]. *)
  assert (Hzy : z <> y) by (clear -Hy; set_solver).
  set (n := res_restrict my (world_dom (m : WorldT) ∪ {[y]})).
  assert (Hdomn : world_dom (n : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
  { subst n. rewrite res_restrict_dom, Hdomy, Hdomz.
    clear -Hz Hzy. set_solver. }
  assert (Hrestrict_my_m : res_restrict my (world_dom (m : WorldT)) = m).
  {
    transitivity (res_restrict (res_restrict my (world_dom (mz : WorldT)))
      (world_dom (m : WorldT))).
    - rewrite res_restrict_restrict_eq. f_equal. rewrite Hdomz. clear. set_solver.
    - rewrite Hrestricty. exact Hrestrictz.
  }
  assert (Hrestrictn : res_restrict n (world_dom (m : WorldT)) = m).
  {
    subst n. rewrite res_restrict_restrict_eq.
    replace ((world_dom (m : WorldT) ∪ {[y]}) ∩ world_dom (m : WorldT))
      with (world_dom (m : WorldT)) by (clear; set_solver).
    exact Hrestrict_my_m.
  }
  assert (Harg_fv :
      formula_fv (ty_denote_gas gas (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))) ⊆ world_dom (m : WorldT) ∪ {[y]}).
  {
    intros a Ha.
    apply formula_fv_ty_denote_gas_subset_relevant in Ha.
    cbn [fv_tm fv_value] in Ha.
    apply elem_of_union in Ha as [Ha|Ha].
    - set_solver.
    - apply elem_of_union_l. apply HΓm. apply Hτx_fv. exact Ha.
  }
  assert (Harg_n :
      n ⊨ ty_denote_gas gas (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))).
  { subst n. apply (proj1 (res_models_minimal_on _ my _ Harg_fv)). exact Harg_old. }
  assert (HyLP : y ∉ LP) by (clear -Hy; set_solver).
  pose proof (HP y n HyLP Hdomn Hrestrictn Harg_n) as Happ_n.
  assert (Happ_src_mid :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        (cty_open 0 y τ)
        (tapp_tm efix (vfvar y))).
  { eapply res_models_kripke; [subst n; apply res_restrict_le|exact Happ_n]. }
  assert (Hres_my :
      my ⊨ expr_result_formula efix (LVFree z)).
  {
    eapply res_models_kripke; [exact Hle_mz_my|exact Hres_z].
  }
  assert (Harg_depth :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))) by exact Harg_old.
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (ext_v_arrow_open_arg_to_comma_ctx Σ Γ τx τ v mz my y).
    - exact Hwf.
    - exact Hctx_mz.
    - exact Hdomy.
    - exact Hrestricty.
    - exact Hy_rest.
    - exact Harg_old.
  }
  pose proof (ext_v_arrow_opened_app_static_guard_full
    Σ Γ τx τ v my y Hwf Hy_rest Hctx_comma) as Hstatic_app.
  assert (Hfun_basic :
      my ⊨ expr_basic_typing_formula
        (<[LVFree y := erase_ty τx]> Δ)
        efix (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
  {
    apply expr_basic_typing_formula_models_iff.
    split.
    - apply lty_env_closed_insert_free. apply atom_store_to_lvar_store_closed.
    - split.
      + pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_app)
          as Hworld_app.
        apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope _]].
        exact Hscope.
      + rewrite cty_open_preserves_erasure.
        eapply basic_tm_has_ltype_weaken.
        * subst Δ efix.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret v) (CTArrow τx τ) Hwf).
        * apply insert_subseteq. apply not_elem_of_dom.
          apply atom_env_to_lty_env_dom_free_notin.
          eapply (soundness_fresh_erase_ctx_from_context_union
            Σ Γ y (fv_value v) (fv_cty τx) (fv_cty τ)).
          clear -Hy_fresh. better_set_solver.
  }
  assert (Hlc_vself : lc_value vself).
  {
    subst vself efix.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret v) (CTArrow τx τ) Hwf).
  }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    subst Δ. apply
      (ctx_erasure_under_inserted_erase_ctx_lty_env_fresh
        Σ Γ z y (erase_ty τx)).
    - exact Hzy.
    - clear -Hz. better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value vself ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
  {
    apply value_open_result_alias_fresh.
    subst vself.
    clear -Hy_fresh Hz. better_set_solver.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
    vself y z (erase_ty τx) my
    Hz_insert_env Hz_alias_fresh
    ltac:(apply map_lookup_insert)
    Hlc_vself Hres_my Hfun_basic Hstatic_app Happ_src_mid) as Htarget_alias.
  change (my ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0)))).
  rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
      y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
      τ (erase_ty τx) (tret (vfvar z))).
  2:{ apply lty_env_closed_insert_free.
      subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst.
      clear -Hy_fresh. set_solver.
    - exfalso.
      subst Σrel efix Δ.
      pose proof (soundness_relevant_env_arrow_value_fresh
        (atom_env_to_lty_env (erase_ctx Γ)) τx τ v y
        ltac:(clear -Hy_fresh; better_set_solver))
        as Hnot.
      exact (Hnot Hin).
  }
  2:{ cbn [fv_tm fv_value]. clear -Hy_fresh. set_solver. }
  2:{ clear -Hy_fresh. better_set_solver. }
  2:{ apply lc_ret_iff_value. constructor. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (Σ1 := <[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
        (<[LVFree y := erase_ty τx]> Δ))
      (X := relevant_lvars (cty_open 0 y τ)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  - reflexivity.
  - apply lam_lty_env_restrict_result_first_result_eq.
    + apply atom_store_to_lvar_store_closed.
    + eapply cty_lvars_open_body_closed_no_fresh.
      * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
      * intros HyD.
        apply lvars_fv_elem in HyD.
        rewrite context_ty_lvars_fv_at in HyD.
        clear -Hy_fresh HyD. better_set_solver.
      * reflexivity.
    + clear -Hy_fresh. set_solver.
    + clear -Hy_fresh. better_set_solver.
    + subst vself. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.

Lemma ext_arrow_value_intro Σ Γ τx τ v (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  ext_arrow_app_prop Σ Γ τx τ v m ->
  m ⊨ ty_denote_under Σ Γ (CTArrow τx τ) (tret v).
Proof.
  intros Hwf Hctx HP.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (CTArrow τx τ) (tret v) m Hwf Hctx) as Hstatic.
  pose proof (ty_denote_gas_zero_tret_of_static_guard
    Δ (CTArrow τx τ) v m Hstatic) as Hzero.
  unfold ty_denote_under, ty_denote.
  change (m ⊨ ty_denote_gas (S gas) Δ (CTArrow τx τ) (tret v)).
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - eapply ty_denote_gas_guard_of_zero. exact Hzero.
  - pose proof (ty_denote_gas_scope_from_zero_any
      (S gas) Δ (CTArrow τx τ) (tret v) m Hzero)
      as Hscope_full.
    cbn [ty_denote_gas] in Hscope_full.
    apply (proj1 (formula_scoped_and_iff _ _ _)) in Hscope_full
      as [_ Hscope_body].
    eapply res_models_forall_rev_intro; [exact Hscope_body| ].
    exists (world_dom (m : WorldT) ∪ dom Σ ∪
      dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪
      fv_cty τx ∪ fv_cty τ).
    intros z Hz mz Hdomz Hrestrictz.
    assert (Hle_m_mz : m ⊑ mz).
    { rewrite <- Hrestrictz. apply res_restrict_le. }
    assert (Hz_world : z ∈ world_dom (mz : WorldT)).
    { rewrite Hdomz. apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
    pose proof (formula_scoped_forall_open_res_le
      m mz z _ Hscope_body Hle_m_mz Hz_world) as Hopened_scope.
    cbn [formula_open] in Hopened_scope |- *.
    eapply res_models_impl_intro; [exact Hopened_scope| ].
    intros Hres_raw.
    assert (Hzfresh :
        z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
          fv_value v ∪ fv_cty τx ∪ fv_cty τ).
    { clear -Hz. better_set_solver. }
    pose proof (ext_v_result_first_outer_result_plain
      Σ Γ τx τ v mz z Hwf Hzfresh Hres_raw) as Hres_plain.
    assert (Hτx_lc : lc_context_ty τx).
    { apply (context_typing_wf_arrow_arg_lc Σ Γ (tret v) τx τ). exact Hwf. }
    assert (Hτ_lc1 : cty_lc_at 1 τ).
    { apply (context_typing_wf_arrow_result_lc1 Σ Γ (tret v) τx τ). exact Hwf. }
    assert (Hvalue_scope :
        formula_scoped_in_world mz
          (arrow_value_denote_gas_with ty_denote_gas gas
            (<[LVFree z := erase_ty (CTArrow τx τ)]>
              (relevant_env Δ (CTArrow τx τ) (tret v)))
            τx τ (tret (vfvar z)))).
    {
      pose proof (formula_scoped_impl_r _ _ _ Hopened_scope) as Hraw.
      rewrite (formula_open_result_first_arrow_value_ret_bvar0
        gas (relevant_env Δ (CTArrow τx τ) (tret v))
        τx τ (erase_ty (CTArrow τx τ)) z) in Hraw.
      - exact Hraw.
      - subst Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
      - subst Δ.
        eapply relevant_env_arrow_fresh_free.
        + clear -Hzfresh. better_set_solver.
        + clear -Hzfresh. better_set_solver.
        + cbn [fv_tm]. clear -Hzfresh. better_set_solver.
      - exact Hτx_lc.
      - exact Hτ_lc1.
      - clear -Hzfresh. better_set_solver.
      - clear -Hzfresh. better_set_solver.
    }
    change (mz ⊨ formula_open 0 z
      (arrow_value_denote_gas_with ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Δ (CTArrow τx τ) (tret v))
          (erase_ty (CTArrow τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ)
        (tret (vbvar 0)))).
    rewrite (formula_open_result_first_arrow_value_ret_bvar0
      gas (relevant_env Δ (CTArrow τx τ) (tret v))
      τx τ (erase_ty (CTArrow τx τ)) z).
    2:{ subst Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
    2:{
      subst Δ.
      eapply relevant_env_arrow_fresh_free.
      - clear -Hzfresh. better_set_solver.
      - clear -Hzfresh. better_set_solver.
      - cbn [fv_tm]. clear -Hzfresh. better_set_solver.
    }
    2:{ exact Hτx_lc. }
    2:{ exact Hτ_lc1. }
    2:{ clear -Hzfresh. better_set_solver. }
    2:{ clear -Hzfresh. better_set_solver. }
    eapply (ext_v_result_first_arrow_value_denotation
      Σ Γ τx τ v m mz z).
    + exact Hwf.
    + exact HP.
    + exact Hctx.
    + exact Hdomz.
    + exact Hrestrictz.
    + clear -Hz. better_set_solver.
    + exact Hvalue_scope.
    + exact Hres_plain.
Qed.

(** A result world exists for any guarded term. *)
Lemma ext_result_world_exists (Σ : lty_env) τ e (m : WfWorldT) y :
  m ⊨ ty_guard_formula Σ τ e ->
  y ∉ world_dom (m : WorldT) ->
  exists my : WfWorldT,
    world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
    res_restrict my (world_dom (m : WorldT)) = m /\
    my ⊨ expr_result_formula_at (dom Σ) e (LVFree y) /\
    my ⊨ expr_result_formula e (LVFree y).
Proof.
  intros Hguard Hy.
  assert (Hfv : fv_tm e ⊆ world_dom (m : WorldT)).
  {
    pose proof Hguard as Hg.
    unfold ty_guard_formula in Hg.
    repeat rewrite res_models_and_iff in Hg.
    destruct Hg as [_ [Hworld [Hbasic _]]].
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Htm_lvars.
    apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
    intros a Ha.
    apply Hscope.
    apply lvars_fv_elem.
    apply Htm_lvars.
    unfold lvars_of_atoms.
    apply elem_of_map. exists a. split; [reflexivity|exact Ha].
  }
  destruct (expr_result_extension_witness_on_exists
    (world_dom (m : WorldT)) e y Hfv Hy) as [F HF].
  assert (Happ : extension_applicable F m).
  {
    destruct HF as [_ _ [Hin Hout] _].
    constructor.
    - change (ext_in F ⊆ world_dom (m : WorldT)). rewrite Hin. set_solver.
    - change (ext_out F ## world_dom (m : WorldT)). rewrite Hout. set_solver.
  }
  destruct (res_extend_by_exists m F Happ) as [my Hext].
  exists my. split; [ |split; [ |split]].
  - rewrite (res_extend_by_dom m F my Hext).
    destruct HF as [_ _ [_ Hout] _].
    change (world_dom (m : WorldT) ∪ ext_out F = world_dom (m : WorldT) ∪ {[y]}).
    rewrite Hout. reflexivity.
  - eapply res_extend_by_restrict_base. exact Hext.
  - eapply expr_result_formula_at_env_of_result_extends_from_ty_guard_on; eauto.
  - eapply expr_result_formula_of_result_extends_on_from_ty_guard; eauto.
Qed.


Lemma ext_open_result_shift0 (D : lvset) e y :
  lc_lvars D ->
  lc_tm e ->
  y ∉ lvars_fv D ->
  y ∉ fv_tm e ->
  formula_open 0 y
    (expr_result_formula_at (lvars_shift_from 0 D) (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula_at D e (LVFree y).
Proof.
  intros HlcD Hlc HyD Hye.
  rewrite formula_open_expr_result_formula_at_shift0.
  - rewrite (lvars_shift_from_lc_at_id 0 D); [reflexivity| ].
    apply soundness_lam_lvars_lc_at_zero_of_lc. exact HlcD.
  - apply soundness_lam_lc_lvars_shift_from. exact HlcD.
  - rewrite lvars_shift_from_fv. exact HyD.
  - exact Hlc.
  - exact Hye.
Qed.

Lemma ty_guard_lc_parts (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  lc_lvars (dom Σ) /\ lc_tm e.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [HlcΣ [_ Hty]].
  apply basic_world_formula_models_iff in Hworld as [HlcD _].
  split; [exact HlcD| ].
  exact (basic_tm_has_ltype_lc Σ e (erase_ty τ) HlcΣ Hty).
Qed.



Lemma ext_arrow_value_elim Σ Γ τx τ v (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ (CTArrow τx τ) (tret v) ->
  ext_arrow_app_prop Σ Γ τx τ v m.
Proof.
  intros Hwf Hctx Hden.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret v)).
  unfold ty_denote_under, ty_denote in Hden.
  change (m ⊨ ty_denote_gas (S gas) Δ (CTArrow τx τ) (tret v)) in Hden.
  pose proof (ty_denote_gas_guard_formula _ _ _ _ _ Hden) as Hguard.
  fold Σrel in Hguard.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hforall].
  fold Σrel in Hforall.
  pose proof (ext_ctx_world_dom_fv Σ Γ _ _ m Hwf Hctx) as HΓm.
  pose proof (context_typing_wf_fv_tm_subset Σ Γ _ _ Hwf) as Hvfv.
  cbn [fv_tm] in Hvfv.
  pose proof (context_typing_wf_context_ty
    Σ Γ (tret v) (CTArrow τx τ) Hwf) as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  pose proof (wf_context_ty_at_fv_subset _ _ _ Hτx_wf) as Hτx_fv.
  pose proof (wf_context_ty_at_fv_subset _ _ _ Hτ_wf) as Hτ_fv.
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  destruct (ty_guard_lc_parts _ _ _ _ Hguard) as [HlcD Hlcv].
  assert (HΣrel_m : lvars_fv (dom Σrel) ⊆ world_dom (m : WorldT)).
  {
    pose proof Hguard as Hg.
    unfold ty_guard_formula in Hg.
    repeat rewrite res_models_and_iff in Hg.
    destruct Hg as [_ [Hworld _]].
    apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
    exact Hscope.
  }
  exists (world_dom (m : WorldT) ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value v ∪ fv_cty τx ∪ fv_cty τ).
  intros y n Hy Hdomn Hrestrictn Harg.
  assert (Hy_rest :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value v ∪ fv_cty τx ∪ fv_cty τ).
  { clear -Hy. better_set_solver. }
  assert (Hym : y ∉ world_dom (m : WorldT)) by (clear -Hy; set_solver).
  assert (Hle_m_n : m ⊑ n).
  { rewrite <- Hrestrictn. apply res_restrict_le. }
  assert (Hguard_n : n ⊨ ty_guard_formula Σrel (CTArrow τx τ) (tret v)).
  { eapply res_models_kripke; [exact Hle_m_n|exact Hguard]. }
  set (z := fresh_for (world_dom (n : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪ fv_cty τ ∪
    lvars_fv (dom Σrel))).
  pose proof (fresh_for_not_in (world_dom (n : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_value v ∪ fv_cty τx ∪ fv_cty τ ∪
    lvars_fv (dom Σrel))) as Hz.
  fold z in Hz.
  assert (Hzy : z <> y).
  { intros ->. apply Hz. rewrite Hdomn. set_solver. }
  assert (Hzm : z ∉ world_dom (m : WorldT)).
  { intros Hzm. apply Hz. rewrite Hdomn. set_solver. }
  destruct (ext_result_world_exists Σrel (CTArrow τx τ) (tret v) n z
    Hguard_n ltac:(clear -Hz; set_solver))
    as [nz [Hdom_nz [Hrestr_nz [Hres_at_nz Hres_nz]]]].
  set (mz := res_restrict nz (world_dom (m : WorldT) ∪ {[z]})).
  assert (Hdom_mz : world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]}).
  { subst mz. rewrite res_restrict_dom, Hdom_nz, Hdomn.
    clear -Hym Hzy. set_solver. }
  assert (Hrestr_mz : res_restrict mz (world_dom (m : WorldT)) = m).
  {
    subst mz. rewrite res_restrict_restrict_eq.
    transitivity (res_restrict (res_restrict nz (world_dom (n : WorldT)))
      (world_dom (m : WorldT))).
    - rewrite res_restrict_restrict_eq. f_equal. rewrite Hdomn. clear. set_solver.
    - rewrite Hrestr_nz. exact Hrestrictn.
  }
  assert (Hle_mz_nz : mz ⊑ nz) by (subst mz; apply res_restrict_le).
  assert (Hres_fv :
      formula_fv (expr_result_formula_at (dom Σrel) (tret v) (LVFree z)) ⊆
        world_dom (m : WorldT) ∪ {[z]}).
  {
    rewrite formula_fv_expr_result_formula_at, lvars_fv_union.
    intros a Ha. apply elem_of_union in Ha as [Ha|Ha].
    - apply elem_of_union_l. apply HΣrel_m. exact Ha.
    - apply elem_of_union in Ha as [Ha|Ha].
      + rewrite tm_lvars_fv in Ha. cbn [fv_tm] in Ha.
        apply elem_of_union_l. apply HΓm. apply Hvfv. exact Ha.
      + apply lvars_fv_elem in Ha. apply elem_of_singleton in Ha.
        inversion Ha. subst. set_solver.
  }
  assert (Hres_mz :
      mz ⊨ expr_result_formula_at (dom Σrel) (tret v) (LVFree z)).
  { subst mz. apply (proj1 (res_models_minimal_on _ nz _ Hres_fv)). exact Hres_at_nz. }
  pose proof (res_models_forall_open_named_fresh m mz z _ Hforall Hzm
    Hdom_mz Hrestr_mz) as Hopen.
  rewrite formula_open_impl in Hopen.
  rewrite ext_open_result_shift0 in Hopen.
  2:{ exact HlcD. }
  2:{ exact Hlcv. }
  2:{ clear -Hz. set_solver. }
  2:{ cbn [fv_tm]. clear -Hz. set_solver. }
  pose proof (res_models_impl_elim _ _ _ Hopen Hres_mz) as HAV.
  change (mz ⊨ formula_open 0 z
    (arrow_value_denote_gas_with ty_denote_gas gas
      (typed_lty_env_bind Σrel (erase_ty (CTArrow τx τ)))
      (cty_shift 0 τx) (cty_shift 1 τ)
      (tret (vbvar 0)))) in HAV.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
    gas Σrel τx τ (erase_ty (CTArrow τx τ)) z) in HAV.
  2:{ subst Σrel Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    subst Σrel Δ.
    eapply relevant_env_arrow_fresh_free.
    - clear -Hz. better_set_solver.
    - clear -Hz. better_set_solver.
    - cbn [fv_tm]. clear -Hz. better_set_solver.
  }
  2:{ exact Hτx_lc. }
  2:{ exact Hτ_lc1. }
  2:{ clear -Hz. better_set_solver. }
  2:{ clear -Hz. better_set_solver. }
  cbn [arrow_value_denote_gas_with] in HAV.
  assert (Hrestr_nz_mz : res_restrict nz (world_dom (mz : WorldT)) = mz).
  { subst mz. apply res_restrict_self_dom. }
  assert (Hdom_nz_mz : world_dom (nz : WorldT) = world_dom (mz : WorldT) ∪ {[y]}).
  { rewrite Hdom_nz, Hdomn, Hdom_mz. clear. set_solver. }
  assert (Hy_mz : y ∉ world_dom (mz : WorldT)).
  { rewrite Hdom_mz. clear -Hym Hzy. set_solver. }
  pose proof (res_models_forall_open_named_fresh mz nz y _ HAV Hy_mz
    Hdom_nz_mz Hrestr_nz_mz) as Hopen_y.
  cbn [formula_open] in Hopen_y.
  assert (Hy_fresh :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value v ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  { clear -Hy_rest Hzy. set_solver. }
  (* the argument *)
  assert (Harg_nz :
      nz ⊨ formula_open 0 y
        (ty_denote_gas gas
          (typed_lty_env_bind
            (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))).
  {
    rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
      y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel) τx).
    2:{ apply lty_env_closed_insert_free.
        subst Σrel Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
    2:{
      rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      - apply elem_of_singleton in Hin. inversion Hin. subst. congruence.
      - exfalso.
        subst Σrel Δ.
        pose proof (soundness_relevant_env_arrow_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) τx τ v y
          ltac:(clear -Hy_fresh; better_set_solver))
          as Hnot.
        exact (Hnot Hin).
    }
    2:{ clear -Hy_fresh. better_set_solver. }
    2:{ exact Hτx_lc. }
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree y := erase_ty τx]> Δ)
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - symmetry.
      rewrite lty_env_insert_free_commute by (clear -Hy_fresh; set_solver).
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy_fresh Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTArrow τx τ)) Hz_rel_arg).
      apply lam_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + cbn [fv_tm]. clear -Hy_fresh. better_set_solver.
    - eapply res_models_kripke; [ |exact Harg].
      rewrite <- Hrestr_nz. apply res_restrict_le.
  }
  pose proof (res_models_impl_elim _ _ _ Hopen_y Harg_nz) as Happ_raw.
  change (nz ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0)))) in Happ_raw.
  rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
      y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
      τ (erase_ty τx) (tret (vfvar z))) in Happ_raw.
  2:{ apply lty_env_closed_insert_free.
      subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst. congruence.
    - exfalso.
      subst Σrel Δ.
      pose proof (soundness_relevant_env_arrow_value_fresh
        (atom_env_to_lty_env (erase_ctx Γ)) τx τ v y
        ltac:(clear -Hy_fresh; better_set_solver))
        as Hnot.
      exact (Hnot Hin).
  }
  2:{ cbn [fv_tm fv_value]. clear -Hy_fresh. set_solver. }
  2:{ clear -Hy_fresh. better_set_solver. }
  2:{ apply lc_ret_iff_value. constructor. }
  assert (Happ_alias :
      nz ⊨ ty_denote_gas gas
        (<[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
          (<[LVFree y := erase_ty τx]> Δ))
        (cty_open 0 y τ) (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree y := erase_ty τx]>
          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        (X := relevant_lvars (cty_open 0 y τ)
          (tapp_tm (tret (vfvar z)) (vfvar y))).
    - reflexivity.
    - symmetry.
      apply lam_lty_env_restrict_result_first_result_eq.
      + apply atom_store_to_lvar_store_closed.
      + eapply cty_lvars_open_body_closed_no_fresh.
        * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
          exact Hτ_lc1.
        * intros HyD.
          apply lvars_fv_elem in HyD.
          rewrite context_ty_lvars_fv_at in HyD.
          clear -Hy_fresh HyD. better_set_solver.
        * reflexivity.
      + clear -Hy_fresh. set_solver.
      + clear -Hy_fresh. better_set_solver.
      + clear -Hz. better_set_solver.
    - exact Happ_raw.
  }
  (* static facts about the application *)
  assert (Hctx_comma_n :
      n ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (ext_v_arrow_open_arg_to_comma_ctx Σ Γ τx τ v m n y).
    - exact Hwf.
    - exact Hctx.
    - exact Hdomn.
    - exact Hrestrictn.
    - exact Hy_rest.
    - exact Harg.
  }
  assert (Hle_n_nz : n ⊑ nz).
  { rewrite <- Hrestr_nz. apply res_restrict_le. }
  pose proof (ext_v_arrow_opened_app_static_guard_full
    Σ Γ τx τ v n y Hwf Hy_rest Hctx_comma_n) as Hstatic_app_n.
  assert (Hstatic_app := res_models_kripke _ _ _ Hle_n_nz Hstatic_app_n).
  assert (Hfun_basic :
      nz ⊨ expr_basic_typing_formula
        (<[LVFree y := erase_ty τx]> Δ)
        (tret v) (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
  {
    apply expr_basic_typing_formula_models_iff.
    split.
    - apply lty_env_closed_insert_free. apply atom_store_to_lvar_store_closed.
    - split.
      + pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_app)
          as Hworld_app.
        apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope _]].
        exact Hscope.
      + rewrite cty_open_preserves_erasure.
        eapply basic_tm_has_ltype_weaken.
        * subst Δ.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret v) (CTArrow τx τ) Hwf).
        * apply insert_subseteq. apply not_elem_of_dom.
          apply atom_env_to_lty_env_dom_free_notin.
          eapply (soundness_fresh_erase_ctx_from_context_union
            Σ Γ y (fv_value v) (fv_cty τx) (fv_cty τ)).
          clear -Hy_fresh. better_set_solver.
  }
  assert (Hlc_v : lc_value v).
  { apply lc_ret_iff_value. exact Hlcv. }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    subst Δ. apply
      (ctx_erasure_under_inserted_erase_ctx_lty_env_fresh
        Σ Γ z y (erase_ty τx)).
    - exact Hzy.
    - clear -Hz. better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value v ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
  {
    apply value_open_result_alias_fresh.
    clear -Hzy Hz. set_solver.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_back_from_static
    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
    v y z (erase_ty τx) nz
    Hz_insert_env Hz_alias_fresh
    ltac:(apply map_lookup_insert)
    Hlc_v Hres_nz Hfun_basic Hstatic_app Happ_alias) as Happ_v.
  (* restrict back to [n] *)
  assert (Happ_fv :
      formula_fv (ty_denote_gas gas (<[LVFree y := erase_ty τx]> Δ)
        (cty_open 0 y τ) (tapp_tm (tret v) (vfvar y))) ⊆
      world_dom (n : WorldT)).
  {
    intros a Ha.
    apply formula_fv_ty_denote_gas_subset_relevant in Ha.
    rewrite Hdomn.
    unfold tapp_tm in Ha. cbn [fv_tm fv_value] in Ha.
    rewrite value_shift_fv in Ha.
    pose proof (cty_open_fv_subset 0 y τ) as Hopen_fv.
    apply elem_of_union in Ha as [Ha|Ha].
    - apply elem_of_union in Ha as [Ha|Ha].
      + apply elem_of_union_l. apply HΓm. apply Hvfv. exact Ha.
      + set_solver.
    - apply Hopen_fv in Ha. apply elem_of_union in Ha as [Ha|Ha].
      + apply elem_of_union_l. apply HΓm. apply Hτ_fv. exact Ha.
      + set_solver.
  }
  rewrite <- Hrestr_nz.
  apply (proj1 (res_models_minimal_on _ nz _ Happ_fv)).
  exact Happ_v.
Qed.

(** ** T-FixUnroll for arrow types *)

Lemma ext_fix_unroll_app_transfer Σ Γ τx τ self arg sx t body (m : WfWorldT) :
  lc_tm body ->
  context_typing_wf Σ Γ (tret (fixfun_named self arg sx t body)) (CTArrow τx τ) ->
  context_typing_wf Σ Γ (tret (ext_fix_unfolding self arg sx t body)) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  ext_arrow_app_prop Σ Γ τx τ (ext_fix_unfolding self arg sx t body) m ->
  ext_arrow_app_prop Σ Γ τx τ (fixfun_named self arg sx t body) m.
Proof.
  intros Hb Hwf_fix Hwf_unf Hctx [L HP].
  set (fx := fixfun_named self arg sx t body) in *.
  set (unf := ext_fix_unfolding self arg sx t body) in *.
  exists (L ∪ {[self]} ∪ {[arg]} ∪ fv_value fx ∪ fv_value unf ∪
    world_dom (m : WorldT) ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_cty τx ∪ fv_cty τ).
  intros y n Hy Hdomn Hrestrictn Harg.
  pose proof (HP y n ltac:(clear -Hy; set_solver) Hdomn Hrestrictn Harg)
    as Happ_unf.
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)) in *.
  set (Σy := <[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ))) in *.
  assert (Hy_fix :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value fx ∪ fv_cty τx ∪ fv_cty τ).
  { clear -Hy. better_set_solver. }
  assert (Hy_unf :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value unf ∪ fv_cty τx ∪ fv_cty τ).
  { clear -Hy. better_set_solver. }
  pose proof (ext_v_arrow_open_arg_to_comma_ctx Σ Γ τx τ fx m n y
    Hwf_fix Hctx Hdomn Hrestrictn Hy_fix Harg) as Hctx_comma.
  pose proof (ext_v_arrow_opened_app_static_guard_full
    Σ Γ τx τ fx n y Hwf_fix Hy_fix Hctx_comma) as Hstatic_fix.
  pose proof (ext_v_arrow_opened_app_static_guard_full
    Σ Γ τx τ unf n y Hwf_unf Hy_unf Hctx_comma) as Hstatic_unf.
  assert (Hclosed :
      wfworld_closed_on (fv_value fx ∪ fv_value unf ∪ {[y]}) n).
  {
    pose proof (ty_static_guard_wfworld_closed_on_term _ _ _ _ Hstatic_fix) as H1.
    pose proof (ty_static_guard_wfworld_closed_on_term _ _ _ _ Hstatic_unf) as H2.
    pose proof (wfworld_closed_on_union _ _ _ H1 H2) as H12.
    eapply wfworld_closed_on_mono; [ |exact H12].
    unfold tapp_tm. cbn [fv_tm fv_value]. rewrite !value_shift_fv.
    clear. set_solver.
  }
  assert (Hy_dom : y ∈ world_dom (n : WorldT)) by (rewrite Hdomn; set_solver).
  destruct (ext_fix_unroll_tm_equiv n self arg sx t body y Hb
    ltac:(clear -Hy; set_solver) ltac:(clear -Hy; set_solver)
    ltac:(clear -Hy; set_solver) Hy_dom Hclosed) as [Heq Htot].
  fold fx unf in Heq, Htot.
  assert (Heq' : tm_equiv_on n (tapp_tm (tret unf) (vfvar y)) (tapp_tm (tret fx) (vfvar y))).
  { intros σ v Hσ. symmetry. apply Heq. exact Hσ. }
  assert (Htot' : tm_total_equiv_on n (tapp_tm (tret unf) (vfvar y)) (tapp_tm (tret fx) (vfvar y))).
  { intros σ Hσ. symmetry. apply Htot. exact Hσ. }
  pose proof (ty_denote_gas_zero_of_guard _ _ _ _
    (ty_denote_gas_guard _ _ _ _ _ Happ_unf)) as Hzero_unf.
  assert (Hlc_app : lc_tm (tapp_tm (tret fx) (vfvar y))).
  { apply lc_tapp_tm; [constructor; apply ext_fixfun_named_lc; exact Hb|constructor]. }
  assert (Hfv_app : fv_tm (tapp_tm (tret fx) (vfvar y)) ⊆ world_dom (n : WorldT)).
  { eapply ty_static_guard_fv_tm_subset. exact Hstatic_fix. }
  pose proof (ty_denote_gas_zero_transport_static_tm_equiv
    Σy (cty_open 0 y τ) (tapp_tm (tret unf) (vfvar y)) (tapp_tm (tret fx) (vfvar y)) n
    Heq' Htot' Hstatic_fix Hlc_app Hfv_app Hzero_unf) as Hzero_fix.
  eapply ty_denote_gas_tm_equiv; [ |exact Happ_unf].
  split; [exact Heq'| ]. split; [exact Htot'| ]. split; assumption.
Qed.

Theorem ext_fix_unroll_named_sound_arrow Σ Γ self arg sx t body τx τ :
  lc_tm body ->
  context_typing_wf Σ Γ (tret (fixfun_named self arg sx t body)) (CTArrow τx τ) ->
  context_typing_wf Σ Γ
    (tret (lam_named arg sx (tm_subst self (fixfun_named self arg sx t body) body)))
    (CTArrow τx τ) ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow τx τ)
      (tret (lam_named arg sx (tm_subst self (fixfun_named self arg sx t body) body)))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow τx τ) (tret (fixfun_named self arg sx t body)).
Proof.
  intros Hb Hwf_fix Hwf_unf IH m Hctx.
  apply ext_arrow_value_intro; [exact Hwf_fix|exact Hctx| ].
  apply (ext_fix_unroll_app_transfer Σ Γ τx τ self arg sx t body m Hb Hwf_fix Hwf_unf Hctx).
  apply ext_arrow_value_elim; [exact Hwf_unf|exact Hctx| ].
  exact (IH m Hctx).
Qed.

(** Types for which T-FixUnroll is proved sound: arrows (and the base
    types, for which the rule is vacuous since a [fix] value has no base
    type), closed under intersection and union.  [-∗], [⊕], [□] are covered
    by [ext_fix_unroll_named_sound_ext] at the end of this file. *)
Notation ext_fix_unroll_shape := fix_unroll_shape (only parsing).

Lemma ext_fix_not_base Σ Γ self arg sx t body τ b :
  erase_ty τ = TBase b ->
  context_typing_wf Σ Γ (tret (fixfun_named self arg sx t body)) τ -> False.
Proof.
  intros Herase Hwf.
  pose proof (context_typing_wf_basic_typing _ _ _ _ Hwf) as Hty.
  rewrite Herase in Hty.
  inversion Hty; subst.
  match goal with
  | H : _ ⊢ᵥ fixfun_named _ _ _ _ _ ⋮ _ |- _ =>
      unfold fixfun_named in H; inversion H
  end.
Qed.

Lemma ext_context_typing_wf_inter_l Σ Γ e τ1 τ2 :
  context_typing_wf Σ Γ e (CTInter τ1 τ2) -> context_typing_wf Σ Γ e τ1.
Proof.
  intros [Hctx [Hτ He]]. cbn [wf_context_ty_at erase_ty] in Hτ, He.
  split; [exact Hctx| ]. split; [exact (proj1 Hτ)|exact He].
Qed.

Lemma ext_context_typing_wf_inter_r Σ Γ e τ1 τ2 :
  context_typing_wf Σ Γ e (CTInter τ1 τ2) -> context_typing_wf Σ Γ e τ2.
Proof.
  intros [Hctx [Hτ He]]. cbn [wf_context_ty_at erase_ty] in Hτ, He.
  split; [exact Hctx| ]. split; [exact (proj1 (proj2 Hτ))| ].
  rewrite <- (proj2 (proj2 Hτ)). exact He.
Qed.

Lemma ext_context_typing_wf_union_l Σ Γ e τ1 τ2 :
  context_typing_wf Σ Γ e (CTUnion τ1 τ2) -> context_typing_wf Σ Γ e τ1.
Proof.
  intros [Hctx [Hτ He]]. cbn [wf_context_ty_at erase_ty] in Hτ, He.
  split; [exact Hctx| ]. split; [exact (proj1 Hτ)|exact He].
Qed.

Lemma ext_context_typing_wf_union_r Σ Γ e τ1 τ2 :
  context_typing_wf Σ Γ e (CTUnion τ1 τ2) -> context_typing_wf Σ Γ e τ2.
Proof.
  intros [Hctx [Hτ He]]. cbn [wf_context_ty_at erase_ty] in Hτ, He.
  split; [exact Hctx| ]. split; [exact (proj1 (proj2 Hτ))| ].
  rewrite <- (proj2 (proj2 Hτ)). exact He.
Qed.

Lemma ext_ty_denote_under_component Σ Γ τi gas e (m : WfWorldT) :
  cty_depth τi <= gas ->
  m ⊨ ty_denote_gas gas (atom_env_to_lty_env (erase_ctx Γ)) τi e <->
  m ⊨ ty_denote_under Σ Γ τi e.
Proof.
  intros Hle. unfold ty_denote_under, ty_denote.
  rewrite ty_denote_gas_saturate by exact Hle. reflexivity.
Qed.

Lemma ext_fix_unroll_world Σ Γ self arg sx t body τ (m : WfWorldT) :
  ext_fix_unroll_shape τ ->
  lc_tm body ->
  context_typing_wf Σ Γ (tret (fixfun_named self arg sx t body)) τ ->
  context_typing_wf Σ Γ (tret (ext_fix_unfolding self arg sx t body)) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ τ (tret (ext_fix_unfolding self arg sx t body)) ->
  m ⊨ ty_denote_under Σ Γ τ (tret (fixfun_named self arg sx t body)).
Proof.
  induction τ as [b φ|b φ|τ1 IH1 τ2 IH2|τ1 IH1 τ2 IH2|τ1 IH1 τ2 IH2
    |τx IHx τr IHr|τx IHx τr IHr|τ1 IH1];
    cbn [ext_fix_unroll_shape]; intros Hshape Hb Hwf_fix Hwf_unf Hctx Hden;
    try contradiction.
  - exfalso. exact (ext_fix_not_base _ _ _ _ _ _ _ (CTOver b φ) b eq_refl Hwf_fix).
  - exfalso. exact (ext_fix_not_base _ _ _ _ _ _ _ (CTUnder b φ) b eq_refl Hwf_fix).
  - (* intersection *)
    destruct Hshape as [Hs1 Hs2].
    set (fx := fixfun_named self arg sx t body) in *.
    set (unf := ext_fix_unfolding self arg sx t body) in *.
    pose proof (context_typing_wf_denot_static_guard_full
      Σ Γ (CTInter τ1 τ2) (tret fx) m Hwf_fix Hctx) as Hstatic.
    pose proof (ty_denote_gas_zero_tret_of_static_guard
      _ (CTInter τ1 τ2) fx m Hstatic) as Hzero.
    unfold ty_denote_under, ty_denote in Hden |- *.
    cbn [cty_depth ty_denote_gas] in Hden |- *.
    rewrite res_models_and_iff in Hden |- *.
    destruct Hden as [_ Hden]. rewrite res_models_and_iff in Hden |- *.
    destruct Hden as [Hd1 Hd2].
    split; [eapply ty_denote_gas_guard_of_zero; exact Hzero| ].
    split.
    + apply (ext_ty_denote_under_component Σ Γ τ1); [lia| ].
      apply IH1; eauto using ext_context_typing_wf_inter_l.
      apply (ext_ty_denote_under_component Σ Γ τ1
        (Nat.max (cty_depth τ1) (cty_depth τ2))); [lia|exact Hd1].
    + apply (ext_ty_denote_under_component Σ Γ τ2); [lia| ].
      apply IH2; eauto using ext_context_typing_wf_inter_r.
      apply (ext_ty_denote_under_component Σ Γ τ2
        (Nat.max (cty_depth τ1) (cty_depth τ2))); [lia|exact Hd2].
  - (* union *)
    destruct Hshape as [Hs1 Hs2].
    set (fx := fixfun_named self arg sx t body) in *.
    set (unf := ext_fix_unfolding self arg sx t body) in *.
    pose proof (context_typing_wf_denot_static_guard_full
      Σ Γ (CTUnion τ1 τ2) (tret fx) m Hwf_fix Hctx) as Hstatic.
    pose proof (ty_denote_gas_zero_tret_of_static_guard
      _ (CTUnion τ1 τ2) fx m Hstatic) as Hzero.
    unfold ty_denote_under, ty_denote in Hden |- *.
    cbn [cty_depth ty_denote_gas] in Hden |- *.
    rewrite res_models_and_iff in Hden |- *.
    destruct Hden as [_ Hden].
    split; [eapply ty_denote_gas_guard_of_zero; exact Hzero| ].
    apply (proj1 (res_models_or_iff _ _ _ (res_models_scoped _ _ Hden))) in Hden.
    apply res_models_or_iff.
    {
      pose proof (ty_denote_gas_scope_from_zero_any
        (S (Nat.max (cty_depth τ1) (cty_depth τ2)))
        (atom_env_to_lty_env (erase_ctx Γ)) (CTUnion τ1 τ2) (tret fx) m Hzero)
        as Hscope_full.
      cbn [ty_denote_gas] in Hscope_full.
      apply (proj1 (formula_scoped_and_iff _ _ _)) in Hscope_full as [_ Hsc].
      exact Hsc.
    }
    destruct Hden as [Hd1|Hd2].
    + left.
      apply (ext_ty_denote_under_component Σ Γ τ1); [lia| ].
      apply IH1; eauto using ext_context_typing_wf_union_l.
      apply (ext_ty_denote_under_component Σ Γ τ1
        (Nat.max (cty_depth τ1) (cty_depth τ2))); [lia|exact Hd1].
    + right.
      apply (ext_ty_denote_under_component Σ Γ τ2); [lia| ].
      apply IH2; eauto using ext_context_typing_wf_union_r.
      apply (ext_ty_denote_under_component Σ Γ τ2
        (Nat.max (cty_depth τ1) (cty_depth τ2))); [lia|exact Hd2].
  - (* arrow *)
    apply ext_arrow_value_intro; [exact Hwf_fix|exact Hctx| ].
    apply (ext_fix_unroll_app_transfer Σ Γ τx τr self arg sx t body m
      Hb Hwf_fix Hwf_unf Hctx).
    apply ext_arrow_value_elim; [exact Hwf_unf|exact Hctx|exact Hden].
Qed.

(** Soundness of [EXT_FixUnrollNamed], for arrow-shaped target types (arrows
    closed under [⊓] and [∪]) and a locally closed body. *)
Theorem ext_fix_unroll_named_sound Σ Γ self arg sx t body τ :
  ext_fix_unroll_shape τ ->
  lc_tm body ->
  context_typing_wf Σ Γ (tret (fixfun_named self arg sx t body)) τ ->
  context_typing_wf Σ Γ
    (tret (lam_named arg sx (tm_subst self (fixfun_named self arg sx t body) body))) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ
      (tret (lam_named arg sx (tm_subst self (fixfun_named self arg sx t body) body)))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tret (fixfun_named self arg sx t body)).
Proof.
  intros Hshape Hb Hwf_fix Hwf_unf IH m Hctx.
  eapply ext_fix_unroll_world; [exact Hshape|exact Hb|exact Hwf_fix
    |exact Hwf_unf|exact Hctx| ].
  exact (IH m Hctx).
Qed.

From ContextBasicDenotation Require Import Qualifier.
From ContextAlgebra Require Import ResourceAlgebra.
From ContextLogic Require Import FormulaSyntax FormulaSemantics.
From ContextTyping Require Import SoundnessMatch.
From Stdlib Require Import Lia.
Import ListNotations.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).
Local Notation LStoreT := (LStore (V := value)) (only parsing).

(** * Corrected (paper-form) match rules

    The pattern variables are bound by the branch context itself (as in the
    paper's T-Match, Fig. 4), so a branch context that is unmodelable once
    the pattern variables are added can no longer be used to "type" the
    whole match.  Only the demonic half [{ν = v}] of the pattern equation is
    used.  Results: [ext_list_match_cons_paper_sound],
    [ext_list_match_nil_sound], [ext_list_match_both_paper_sound],
    [ext_tree_match_node_paper_sound], [ext_tree_match_leaf_sound],
    [ext_tree_match_both_paper_sound] (scrutinee a variable [x]). *)

(** ** Equality qualifiers *)

Lemma ext_eq_qual_open_vars x y :
  x <> y ->
  qual_vars
    (qual_open_atom 0 x (mk_q_eq (vbvar 0) (vfvar y))) =
  (({[LVFree x]} ∪ {[LVFree y]}) : lvset).
Proof.
  intros Hxy.
  rewrite qual_open_atom_vars.
  unfold mk_q_eq, qual_vars.
  cbn [qual_lvars lvar_value_keys].
  rewrite set_swap_union, !set_swap_singleton.
  base_swap_normalize.
  better_set_solver.
Qed.

Lemma ext_eq_qual_open_fibvars_set z y :
  z <> y ->
  set_swap (LVBound 0) (LVFree z)
    (qual_vars (mk_q_eq (vbvar 0) (vfvar y)) ∖ {[LVBound 0]}) =
  qual_vars (qual_open_atom 0 z (mk_q_eq (vbvar 0) (vfvar y))) ∖
    {[LVFree z]}.
Proof.
  intros Hzy.
  replace
    (qual_vars (mk_q_eq (vbvar 0) (vfvar y)) ∖ {[LVBound 0]})
    with ({[LVFree y]} : lvset).
  2:{
    unfold mk_q_eq, qual_vars.
    cbn [qual_lvars lvar_value_keys].
    better_set_solver.
  }
  rewrite set_swap_singleton.
  base_swap_normalize.
  rewrite ext_eq_qual_open_vars by exact Hzy.
  better_set_solver.
Qed.

Lemma ext_eq_qual_open_vars_without_opened z y :
  z <> y ->
  qual_vars (qual_open_atom 0 z (mk_q_eq (vbvar 0) (vfvar y))) ∖
    {[LVFree z]} =
  ({[LVFree y]} : lvset).
Proof.
  intros Hzy.
  rewrite ext_eq_qual_open_vars by exact Hzy.
  better_set_solver.
Qed.

Lemma ext_eq_qual_open_prop_iff x y
    (Hxy : x <> y)
    (s : LStoreOn (V := value)
      (qual_vars
        (qual_open_atom 0 x (mk_q_eq (vbvar 0) (vfvar y))))) :
  qual_prop
    (qual_open_atom 0 x (mk_q_eq (vbvar 0) (vfvar y))) s <->
  (lso_store s : LStore (V := value)) !! LVFree x =
  (lso_store s : LStore (V := value)) !! LVFree y.
Proof.
  unfold qual_open_atom, mk_q_eq.
  cbn [qual_prop qual_lvars lvar_value_keys denote_lvar_value
    lstore_on_open_back lso_store].
  unfold lstore_on_open_back.
  cbn [lso_store storeAO_store].
  rewrite !lstore_swap_lookup_inv_value.
  base_swap_normalize.
  tauto.
Qed.

Lemma ext_eq_type_qualifier_open_msubst_lookup z y
    (Hzy : z <> y) (σy : StoreT) (m : WfWorldT) σ :
  dom (σy : StoreT) = {[y]} ->
  res_models m (formula_msubst_store σy
      (FAtom
        (qual_open_atom 0 z (mk_q_eq (vbvar 0) (vfvar y))))) ->
  (m : WorldT) σ ->
  σ !! z = σy !! y.
Proof.
  intros Hσy_dom Hqual Hσ.
  formula_msubst_syntax_norm_in Hqual.
  unfold res_models in Hqual.
  cbn [formula_measure res_models_fuel] in Hqual.
  destruct Hqual as [_ Hqual].
  cbn [qualifier_exact_denote qual_msubst_store qual_mlsubst] in Hqual.
  set (q := qual_open_atom 0 z (mk_q_eq (vbvar 0) (vfvar y))).
  set (D := qual_vars q).
  set (ρ := lstore_lift_free σy : LStoreT).
  destruct Hqual as [Hlc [Hscope Hholds]].
  set (D' := D ∖ dom (ρ : LStoreT)).
  set (s_store := storeA_restrict (lstore_lift_free σ : LStoreT) D').
  assert (HD : D = (({[LVFree z]} ∪ {[LVFree y]}) : lvset)).
  { subst D q. rewrite ext_eq_qual_open_vars by exact Hzy. reflexivity. }
  assert (Hρ_dom : dom (ρ : LStoreT) = {[LVFree y]}).
  {
    subst ρ.
    rewrite dom_lstore_lift_free.
    change (lvars_of_atoms (dom (σy : StoreT)) = {[LVFree y]}).
    rewrite Hσy_dom.
    unfold lvars_of_atoms. rewrite set_map_singleton_L. reflexivity.
  }
  assert (HD' : D' = ({[LVFree z]} : lvset)).
  {
    subst D'. rewrite HD, Hρ_dom.
    better_set_solver.
  }
  assert (Hz_dom : z ∈ dom (σ : StoreT)).
  {
    change (z ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ).
    apply Hscope.
    change (z ∈ lvars_fv D').
    rewrite HD'. rewrite lvars_fv_singleton_free. better_set_solver.
  }
  assert (Hs_dom : dom (s_store : gmap logic_var value) = D').
  {
    subst s_store.
    rewrite storeA_restrict_dom, dom_lstore_lift_free.
    apply set_eq. intros v. split.
    - intros Hv. apply elem_of_intersection in Hv as [_ Hv]. exact Hv.
    - intros Hv. apply elem_of_intersection. split; [ |exact Hv].
      unfold lvars_of_atoms.
      rewrite HD' in Hv.
      apply elem_of_singleton in Hv. subst v.
      apply elem_of_map. eexists. split; [reflexivity|exact Hz_dom].
  }
  pose (s' :=
    (Build_StoreAOn (V := value) logic_var _ _ D' s_store Hs_dom
      : StoreAOn (K := logic_var) (V := value) D')).
  assert (Hmem' : lstore_in_lworld_on s' (lworld_on_lift D' m Hlc Hscope)).
  {
    unfold s', lstore_in_lworld_on, lworld_on_lift.
    cbn [lw lso_store lraw_world raw_worldA worldA_stores storeAO_store].
    exists (lstore_lift_free (store_restrict σ (lvars_fv D'))).
    split.
    - exists (store_restrict σ (lvars_fv D')).
      split.
      + exists σ. split; [exact Hσ|reflexivity].
      + reflexivity.
    - apply lstore_lift_free_restrict_fv_lvars_eq.
  }
  specialize (Hholds s').
  pose proof (proj2 Hholds Hmem') as Hprop.
  change (qual_prop q (lstore_on_mlsubst_back D ρ s')) in Hprop.
  subst q.
  apply ext_eq_qual_open_prop_iff in Hprop; [ |exact Hzy].
  unfold lstore_on_mlsubst_back in Hprop.
  cbn [lso_store storeAO_store] in Hprop.
  unfold s_store in Hprop.
  assert (Hρz : (ρ : LStoreT) !! LVFree z = None).
  { subst ρ. rewrite lstore_lift_free_lookup_free.
    change ((σy : gmap atom value) !! z = None).
    apply not_elem_of_dom_1.
    change (z ∉ dom (σy : gmap atom value)).
    change (dom (σy : gmap atom value) = {[y]}) in Hσy_dom.
    rewrite Hσy_dom. better_set_solver. }
  assert (Hρy : (ρ : LStoreT) !! LVFree y = σy !! y).
  { subst ρ. apply lstore_lift_free_lookup_free. }
  assert (HzD' : LVFree z ∈ D') by (rewrite HD'; set_solver).
  assert (HyD' : LVFree y ∉ D') by (rewrite HD'; clear -Hzy; set_solver).
  assert (HyD : LVFree y ∈ D) by (rewrite HD; set_solver).
  rewrite (lookup_union_l (storeA_restrict (lstore_lift_free σ : LStoreT) D')
    (storeA_restrict ρ D) (LVFree z)) in Hprop.
  2:{ apply storeA_restrict_lookup_none_l. exact Hρz. }
  rewrite (lookup_union_r (storeA_restrict (lstore_lift_free σ : LStoreT) D')
    (storeA_restrict ρ D) (LVFree y)) in Hprop.
  2:{ apply storeA_restrict_lookup_none_r. exact HyD'. }
  assert (E1 : (storeA_restrict (lstore_lift_free σ : LStoreT) D' : LStoreT)
      !! LVFree z = σ !! z).
  { transitivity ((lstore_lift_free σ : LStoreT) !! LVFree z).
    - pose proof (storeA_restrict_lookup (lstore_lift_free σ : LStoreT) D' (LVFree z)) as H.
      rewrite decide_True in H by exact HzD'. exact H.
    - apply lstore_lift_free_lookup_free. }
  assert (E2 : (storeA_restrict ρ D : LStoreT) !! LVFree y = σy !! y).
  { transitivity ((ρ : LStoreT) !! LVFree y).
    - pose proof (storeA_restrict_lookup ρ D (LVFree y)) as H.
      rewrite decide_True in H by exact HyD. exact H.
    - exact Hρy. }
  etransitivity; [symmetry; exact E1| ].
  etransitivity; [exact Hprop|exact E2].
Qed.


(** ** Operational facts for list matching *)

Lemma ext_reduction_matchlist_cons_iff n xs enil econs v :
  lc_tm (tmatchlist (vconst (clist (n :: xs))) enil econs) ->
  tmatchlist (vconst (clist (n :: xs))) enil econs →* tret v <->
  open_list_cons_branch_value (vconst (cnat n)) (vconst (clist xs)) econs →* tret v.
Proof.
  intros Hlc. split.
  - intros Hsteps.
    destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
    + discriminate.
    + inversion Hstep; subst.
      inversion H; subst; try discriminate. exact Hrest.
  - intros Hsteps.
    eapply steps_trans; [ |exact Hsteps].
    apply steps_R. apply Step_head. apply HS_MatchListCons. exact Hlc.
Qed.

Lemma ext_must_terminating_matchlist_cons_equiv n xs enil econs :
  lc_tm (tmatchlist (vconst (clist (n :: xs))) enil econs) ->
  must_terminating (tmatchlist (vconst (clist (n :: xs))) enil econs) <->
  must_terminating (open_list_cons_branch_value (vconst (cnat n)) (vconst (clist xs)) econs).
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_MatchListCons. exact Hlc.
  - apply Must_step.
    + eexists. apply Step_head. apply HS_MatchListCons. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.

(** ** Locally-nameless facts for the cons branch *)

Lemma ext_open_close_commute_value x y v : forall j k,
  x <> y -> j <> k ->
  open_value j (vfvar x) (close_value y k v) =
  close_value y k (open_value j (vfvar x) v).
Proof.
  induction v using value_mut with
    (P0 := fun e => forall j k, x <> y -> j <> k ->
      open_tm j (vfvar x) (close_tm y k e) =
      close_tm y k (open_tm j (vfvar x) e));
    intros j k Hxy Hjk; cbn [open_value open_tm close_value close_tm];
    try reflexivity;
    try solve [f_equal; first [apply IHv | apply IHv0 | apply IHv1 | apply IHv2
      | apply IHv3 | apply IHv4 | auto]; lia].
  - (* fvar *)
    destruct (decide (y = x0)) as [->|Hne]; cbn [open_value close_value].
    + destruct (decide (j = k)) as [->|_]; [lia|reflexivity].
    + destruct (decide (y = x0)); [contradiction|reflexivity].
  - (* bvar *)
    destruct (decide (j = n)) as [->|Hne]; cbn [close_value].
    + destruct (decide (y = x)) as [->|_]; [contradiction|reflexivity].
    + reflexivity.
Qed.

Lemma ext_open_close_commute_tm x y e : forall j k,
  x <> y -> j <> k ->
  open_tm j (vfvar x) (close_tm y k e) =
  close_tm y k (open_tm j (vfvar x) e).
Proof.
  induction e using tm_mut with
    (P := fun v => forall j k, x <> y -> j <> k ->
      open_value j (vfvar x) (close_value y k v) =
      close_value y k (open_value j (vfvar x) v));
    intros j k Hxy Hjk; cbn [open_value open_tm close_value close_tm];
    try reflexivity;
    try solve [f_equal; first [apply IHe | apply IHe0 | apply IHe1 | apply IHe2
      | apply IHe3 | auto]; lia].
  - destruct (decide (y = x0)) as [->|Hne]; cbn [open_value close_value].
    + destruct (decide (j = k)) as [->|_]; [lia|reflexivity].
    + destruct (decide (y = x0)); [contradiction|reflexivity].
  - destruct (decide (j = n)) as [->|Hne]; cbn [close_value].
    + destruct (decide (y = x)) as [->|_]; [contradiction|reflexivity].
    + reflexivity.
Qed.

Lemma ext_open_close_cons_branch hd tl econs :
  lc_tm econs -> hd <> tl ->
  open_list_cons_branch hd tl (close_tm tl 1 (close_tm hd 0 econs)) = econs.
Proof.
  intros Hlc Hne.
  unfold open_list_cons_branch, open_list_cons_branch_value.
  rewrite ext_open_close_commute_tm by (congruence || lia).
  rewrite open_close_var_tm by exact Hlc.
  apply open_close_var_tm_aux.
  apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma ext_close_fv_tm_subset x e : forall k,
  fv_tm (close_tm x k e) ⊆ fv_tm e.
Proof.
  induction e using tm_mut with
    (P := fun v => forall k, fv_value (close_value x k v) ⊆ fv_value v);
    intros k; cbn [close_value close_tm fv_value fv_tm];
    try set_solver;
    try (specialize (IHe k); set_solver).
  destruct (decide (x = x0)); cbn [fv_value]; set_solver.
Qed.

Lemma ext_msubst_cons_branch σ hd tl econs n xs :
  store_closed σ -> lc_tm econs -> hd <> tl ->
  σ !! hd = Some (vconst (cnat n)) ->
  σ !! tl = Some (vconst (clist xs)) ->
  m{σ} econs =
  open_list_cons_branch_value (vconst (cnat n)) (vconst (clist xs))
    (m{σ} (close_tm tl 1 (close_tm hd 0 econs))).
Proof.
  intros [Hclosed Hlcσ] Hlc Hne Hhd Htl.
  set (E := close_tm tl 1 (close_tm hd 0 econs)).
  assert (HtlE : tl ∉ fv_tm E) by (subst E; apply close_rm_fv_tm).
  assert (HhdE : hd ∉ fv_tm E).
  { subst E. intros Hin. apply ext_close_fv_tm_subset in Hin.
    exact (close_rm_fv_tm hd 0 econs Hin). }
  rewrite <- (ext_open_close_cons_branch hd tl econs Hlc Hne) at 1.
  fold E.
  unfold open_list_cons_branch, open_list_cons_branch_value.
  rewrite (msubst_open_lookup_tm σ (open_tm 0 (vfvar hd) E) 1 tl
    (vconst (clist xs)) Hclosed Hlcσ Htl).
  2:{ intros Hin. apply open_fv_tm in Hin. cbn [fv_value] in Hin. set_solver. }
  erewrite (msubst_open_lookup_tm _ E 0 hd (vconst (cnat n))).
  2:{ apply closed_env_delete. exact Hclosed. }
  2:{ apply lc_env_delete. exact Hlcσ. }
  2:{ etransitivity; [apply lookup_delete_ne; congruence|exact Hhd]. }
  2:{ exact HhdE. }
  f_equal. f_equal.
  eapply (msubst_agree tm _ σ (fv_tm E) E).
  - apply closed_env_delete. apply closed_env_delete. exact Hclosed.
  - exact Hclosed.
  - reflexivity.
  - intros z Hz.
    etransitivity; [apply lookup_delete_ne; intros ->; contradiction| ].
    apply lookup_delete_ne; intros ->; contradiction.
Qed.

Lemma ext_tm_eval_in_store_match_list_cons σ v enil hd tl econs n xs w :
  store_closed σ -> lc_tm econs -> hd <> tl ->
  lc_tm (match_list_named v enil hd tl econs) ->
  σ !! hd = Some (vconst (cnat n)) ->
  σ !! tl = Some (vconst (clist xs)) ->
  m{σ} v = vconst (clist (n :: xs)) ->
  tm_eval_in_store σ (match_list_named v enil hd tl econs) w <->
  tm_eval_in_store σ econs w.
Proof.
  intros Hclosed Hlc Hne Hlc_match Hhd Htl Hv.
  pose proof (ext_msubst_cons_branch σ hd tl econs n xs Hclosed Hlc Hne Hhd Htl)
    as Hbranch.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    unfold match_list_named. rewrite msubst_tmatchlist, Hv.
    rewrite Hbranch.
    apply ext_reduction_matchlist_cons_iff.
    rewrite <- Hv, <- msubst_tmatchlist.
    apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma ext_tm_total_in_store_match_list_cons σ v enil hd tl econs n xs :
  store_closed σ -> lc_tm econs -> hd <> tl ->
  lc_tm (match_list_named v enil hd tl econs) ->
  σ !! hd = Some (vconst (cnat n)) ->
  σ !! tl = Some (vconst (clist xs)) ->
  m{σ} v = vconst (clist (n :: xs)) ->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
    (match_list_named v enil hd tl econs)) <->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ) econs).
Proof.
  intros Hclosed Hlc Hne Hlc_match Hhd Htl Hv.
  pose proof (ext_msubst_cons_branch σ hd tl econs n xs Hclosed Hlc Hne Hhd Htl)
    as Hbranch.
  rewrite !lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite !lstore_free_part_lift_free.
  rewrite !subst_map_tm_eq_msubst.
  unfold match_list_named. rewrite msubst_tmatchlist, Hv.
  rewrite Hbranch.
  apply ext_must_terminating_matchlist_cons_equiv.
  rewrite <- Hv, <- msubst_tmatchlist.
  apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
Qed.


(** ** Reading a demonic equation off an over-approximate type *)

Lemma ext_over_eq_fvar_lookup gas (Δ : lty_env) b x e (m : WfWorldT) σ w :
  m ⊨ ty_denote_gas (S gas) Δ (CTOver b (mk_q_eq (vbvar 0) (vfvar x))) e ->
  (m : WorldT) σ ->
  tm_eval_in_store σ e w ->
  σ !! x = Some w.
Proof.
  intros Hden Hσ Heval.
  set (τq := CTOver b (mk_q_eq (vbvar 0) (vfvar x))) in *.
  set (Σg := relevant_env Δ τq e).
  pose proof (ty_denote_gas_guard_formula _ _ _ _ _ Hden) as Hguard.
  fold Σg in Hguard.
  destruct (ty_guard_lc_parts _ _ _ _ Hguard) as [HlcD Hlce].
  assert (Hfv : fv_tm e ⊆ world_dom (m : WorldT)).
  { exact (ty_denote_gas_fv_tm_subset _ _ _ _ _ Hden). }
  pose proof Hden as Hden_body.
  cbn [ty_denote_gas] in Hden_body.
  rewrite res_models_and_iff in Hden_body.
  destruct Hden_body as [_ Hforall].
  fold Σg in Hforall.
  set (z := fresh_for (world_dom (m : WorldT) ∪ {[x]} ∪ fv_tm e ∪
    lvars_fv (dom Σg))).
  pose proof (fresh_for_not_in (world_dom (m : WorldT) ∪ {[x]} ∪ fv_tm e ∪
    lvars_fv (dom Σg))) as Hz. fold z in Hz.
  assert (Hzm : z ∉ world_dom (m : WorldT)) by (clear -Hz; set_solver).
  assert (Hzx : z <> x) by (clear -Hz; set_solver).
  destruct (expr_result_extension_witness_on_exists
    (world_dom (m : WorldT)) e z Hfv Hzm) as [F HF].
  assert (Happ : extension_applicable F m).
  {
    destruct HF as [_ _ [Hin Hout] _].
    constructor.
    - change (ext_in F ⊆ world_dom (m : WorldT)). rewrite Hin. set_solver.
    - change (ext_out F ## world_dom (m : WorldT)). rewrite Hout. set_solver.
  }
  destruct (res_extend_by_exists m F Happ) as [mx Hext].
  assert (Hdom_mx : world_dom (mx : WorldT) = world_dom (m : WorldT) ∪ {[z]}).
  {
    rewrite (res_extend_by_dom m F mx Hext).
    destruct HF as [_ _ [_ Hout] _].
    change (world_dom (m : WorldT) ∪ ext_out F = world_dom (m : WorldT) ∪ {[z]}).
    rewrite Hout. reflexivity.
  }
  pose proof (res_extend_by_restrict_base m F mx Hext) as Hrestr.
  pose proof (expr_result_formula_at_env_of_result_extends_from_ty_guard_on
    Σg τq e z m mx F HF Hext Hguard) as Hres_at.
  pose proof (res_models_forall_open_named_fresh m mx z _ Hforall Hzm
    Hdom_mx Hrestr) as Hopen.
  rewrite formula_open_impl in Hopen.
  rewrite ext_open_result_shift0 in Hopen.
  2:{ exact HlcD. }
  2:{ exact Hlce. }
  2:{ clear -Hz. set_solver. }
  2:{ clear -Hz. set_solver. }
  pose proof (res_models_impl_elim _ _ _ Hopen Hres_at) as Hfib.
  rewrite formula_open_fibvars, formula_open_over, formula_open_atom in Hfib.
  rewrite (ext_eq_qual_open_fibvars_set z x Hzx) in Hfib.
  rewrite (ext_eq_qual_open_vars_without_opened z x Hzx) in Hfib.
  (* the extended store *)
  set (σmx := σ ∪ ({[z := w]} : StoreT)).
  assert (Hσdom : dom (σ : StoreT) = world_dom (m : WorldT)).
  { exact (wfworld_store_dom m σ Hσ). }
  assert (Hσmx : (mx : WorldT) σmx).
  {
    apply (proj2 (resA_extend_by_store_iff m F mx σmx Hext)).
    pose proof HF as HF0.
    destruct HF as [Hfv_on Hfresh_on [Hin Hout] Hrel].
    set (σX := store_restrict σ (world_dom (m : WorldT))).
    assert (HσX : σX = σ).
    { subst σX. rewrite <- Hσdom. apply storeA_restrict_idemp. set_solver. }
    exists σ, (expr_result_output_world e z σX), ({[z := w]} : StoreT).
    split; [exact Hσ| ].
    split.
    - change (ext_rel F (store_restrict σ (ext_in F)) (expr_result_output_world e z σX)).
      rewrite Hin. fold σX. apply Hrel.
      subst σX. rewrite HσX. exact Hσdom.
    - split; [ |reflexivity].
      eapply expr_result_extension_apply_total_store_on.
      + exact HF0.
      + rewrite HσX. exact Hσdom.
      + apply Hrel. rewrite HσX. exact Hσdom.
      + rewrite HσX. exact Heval.
  }
  pose proof (res_models_scoped _ _ Hfib) as Hscope_fib.
  assert (Hx_mx : x ∈ world_dom (mx : WorldT)).
  {
    apply Hscope_fib.
    rewrite formula_fv_fibvars.
    apply elem_of_union_l.
    rewrite lvars_fv_singleton_free. set_solver.
  }
  destruct (res_fiber_from_projection_of_store mx {[x]} σmx)
    as [mfib [Hfiber Hσmx_fib]].
  { intros a Ha. apply elem_of_singleton in Ha. subst a. exact Hx_mx. }
  { exact Hσmx. }
  unfold res_models in Hfib.
  cbn [formula_measure res_models_fuel] in Hfib.
  destruct Hfib as [_ [_ Hfib_body]].
  rewrite lvars_fv_singleton_free in Hfib_body.
  specialize (Hfib_body (store_restrict σmx {[x]}) mfib Hfiber).
  unfold res_models in Hfib_body.
  cbn [formula_measure res_models_fuel] in Hfib_body.
  destruct Hfib_body as [_ [mo [Hsub_fib_mo Hqual_mo]]].
  assert (Hqual_model :
      mo ⊨ formula_msubst_store (store_restrict σmx {[x]})
        (FAtom (qual_open_atom 0 z (mk_q_eq (vbvar 0) (vfvar x))))).
  { unfold res_models. models_fuel_irrel Hqual_mo. }
  destruct Hsub_fib_mo as [_ Hsub_stores].
  assert (Hσmx_mo : (mo : WorldT) σmx).
  { apply Hsub_stores. exact Hσmx_fib. }
  assert (Hσx_dom : dom (store_restrict σmx {[x]} : StoreT) = {[x]}).
  {
    change (dom (storeA_restrict σmx ({[x]} : aset) : gmap atom value) = {[x]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom mx σmx Hσmx).
    apply set_eq. intros a. split.
    - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
    - intros Ha. apply elem_of_intersection. split; [ |exact Ha].
      apply elem_of_singleton in Ha. subst a. exact Hx_mx.
  }
  pose proof (ext_eq_type_qualifier_open_msubst_lookup z x Hzx
    (store_restrict σmx {[x]}) mo σmx Hσx_dom Hqual_model Hσmx_mo) as Heq.
  assert (Hz_look : σmx !! z = Some w).
  {
    subst σmx. apply map_lookup_union_Some_raw. right. split.
    - apply not_elem_of_dom. rewrite Hσdom. exact Hzm.
    - apply map_lookup_singleton.
  }
  assert (Hx_look : (store_restrict σmx {[x]} : StoreT) !! x = σ !! x).
  {
    transitivity (σmx !! x).
    - pose proof (storeA_restrict_lookup σmx ({[x]} : aset) x) as H.
      rewrite decide_True in H by set_solver. exact H.
    - subst σmx.
      destruct (σ !! x) as [vx| ] eqn:Hσx.
      + apply map_lookup_union_Some_raw. left. exact Hσx.
      + apply map_lookup_union_None. split; [exact Hσx| ].
        apply map_lookup_singleton_ne. congruence.
  }
  congruence.
Qed.

(** ** Typed lookups and the evaluation of [hd ::ᵗ tl] *)

Lemma ext_basic_world_typed_lookup (Δ : lty_env) (m : WfWorldT) σ x T :
  m ⊨ basic_world_formula Δ ->
  (m : WorldT) σ ->
  Δ !! LVFree x = Some T ->
  exists v, σ !! x = Some v /\ ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros Hworld Hσ HΔx.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope Htyped]].
  assert (Hx : x ∈ world_dom (m : WorldT)).
  { apply Hscope. apply lvars_fv_elem. eapply elem_of_dom_2. exact HΔx. }
  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
  destruct (σ !! x) as [v| ] eqn:Hσx.
  2:{ apply not_elem_of_dom in Hσx. change (x ∉ dom (σ : StoreT)) in Hσx.
      rewrite Hσdom in Hσx. contradiction. }
  exists v. split; [reflexivity| ].
  destruct Htyped as [_ Hstores].
  assert (Hlift : (res_lift_free m : LWorld) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ|reflexivity]. }
  apply (Hstores _ Hlift (LVFree x) T v HΔx).
  rewrite lstore_lift_free_lookup_free. exact Hσx.
Qed.

Lemma ext_reduction_tcons_iff n xs w :
  tcons (vconst (cnat n)) (vconst (clist xs)) →* tret w <->
  w = vconst (clist (n :: xs)).
Proof.
  split.
  - intros Hsteps.
    destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
    + discriminate.
    + inversion Hstep; subst.
      inversion H; subst; try discriminate.
      pose proof (value_steps_self _ _ Hrest) as Heq. inversion Heq. reflexivity.
  - intros ->.
    apply steps_R. apply Step_head. apply HS_ListCons.
    constructor; constructor.
Qed.

Lemma ext_tm_eval_in_store_tcons σ hd tl n xs w :
  store_closed σ ->
  σ !! hd = Some (vconst (cnat n)) ->
  σ !! tl = Some (vconst (clist xs)) ->
  tm_eval_in_store σ (tcons (vfvar hd) (vfvar tl)) w <->
  w = vconst (clist (n :: xs)).
Proof.
  intros Hclosed Hhd Htl.
  unfold tm_eval_in_store.
  rewrite expr_eval_in_store_no_bvars_iff.
  - rewrite lstore_free_part_lift_free, subst_map_tm_eq_msubst.
    rewrite msubst_tcons.
    rewrite (msubst_fvar_lookup_closed σ hd _ (proj1 Hclosed) Hhd).
    rewrite (msubst_fvar_lookup_closed σ tl _ (proj1 Hclosed) Htl).
    apply ext_reduction_tcons_iff.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

(** ** Soundness of the corrected (paper-form) cons-only list match *)

Lemma ext_tcons_fvar_typing_inv (G : gmap atom ty) hd tl T :
  G ⊢ₑ tcons (vfvar hd) (vfvar tl) ⋮ T ->
  G !! hd = Some (TBase TNat) /\ G !! tl = Some (TBase TList).
Proof.
  intros H. inversion H; subst.
  match goal with
  | H1 : G ⊢ᵥ vfvar hd ⋮ _, H2 : G ⊢ᵥ vfvar tl ⋮ _ |- _ =>
      inversion H1; inversion H2; subst; split; assumption
  end.
Qed.

Lemma ext_cons_pattern_pointwise Σ Γ x hd tl (m : WfWorldT) :
  context_typing_wf Σ Γ (tcons (vfvar hd) (vfvar tl)) (list_match_eq_ty (vfvar x)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ (list_match_eq_ty (vfvar x)) (tcons (vfvar hd) (vfvar tl)) ->
  forall σ, (m : WorldT) σ ->
    exists n xs,
      σ !! hd = Some (vconst (cnat n)) /\
      σ !! tl = Some (vconst (clist xs)) /\
      σ !! x = Some (vconst (clist (n :: xs))).
Proof.
  intros Hwf Hctx Hden σ Hσ.
  set (e := tcons (vfvar hd) (vfvar tl)) in *.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (list_match_eq_ty (vfvar x)) e m Hwf Hctx) as Hstatic.
  pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic) as Hworld.
  pose proof (ty_static_guard_wfworld_closed_on_term _ _ _ _ Hstatic) as Hclosed_e.
  pose proof (context_typing_wf_basic_typing _ _ _ _ Hwf) as Hbasic.
  destruct (ext_tcons_fvar_typing_inv _ _ _ _ Hbasic) as [Hhd_ty Htl_ty].
  destruct (ext_basic_world_typed_lookup Δ m σ hd (TBase TNat) Hworld Hσ)
    as [vh [Hσhd Hvh]].
  { subst Δ. rewrite atom_store_to_lvar_store_lookup_free. exact Hhd_ty. }
  destruct (ext_basic_world_typed_lookup Δ m σ tl (TBase TList) Hworld Hσ)
    as [vt [Hσtl Hvt]].
  { subst Δ. rewrite atom_store_to_lvar_store_lookup_free. exact Htl_ty. }
  destruct (basic_typing_nat_canonical_form vh Hvh) as [n ->].
  destruct (basic_typing_list_canonical_form vt Hvt) as [xs ->].
  exists n, xs. split; [exact Hσhd| ]. split; [exact Hσtl| ].
  assert (Heval : tm_eval_in_store σ e (vconst (clist (n :: xs)))).
  {
    apply (proj1 (tm_eval_in_store_restrict_fv_subset σ e _ (fv_tm e)
      ltac:(reflexivity))).
    apply (proj2 (ext_tm_eval_in_store_tcons _ hd tl n xs _
      (Hclosed_e σ Hσ)
      ltac:(apply storeA_restrict_lookup_some_2; [exact Hσhd|subst e; cbn; set_solver])
      ltac:(apply storeA_restrict_lookup_some_2; [exact Hσtl|subst e; cbn; set_solver]))).
    reflexivity.
  }
  unfold ty_denote_under, ty_denote, list_match_eq_ty, over_ty, under_ty in Hden.
  cbn [cty_depth ty_denote_gas Nat.max] in Hden.
  rewrite res_models_and_iff in Hden. destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter. destruct Hinter as [Hover _].
  eapply (ext_over_eq_fvar_lookup 0 _ TList x e m σ); [exact Hover|exact Hσ|exact Heval].
Qed.



(** ** The nil branch *)

Lemma ext_tm_eval_in_store_ret_const σ c w :
  tm_eval_in_store σ (tret (vconst c)) w <-> w = vconst c.
Proof.
  rewrite <- (tm_eval_in_store_restrict_fv_subset σ (tret (vconst c)) w ∅)
    by (cbn; set_solver).
  rewrite storeA_restrict_empty_set.
  assert (Hclosed : store_closed (∅ : StoreT)).
  { split; apply map_Forall_empty. }
  split.
  - intros Heval.
    pose proof (tm_eval_in_store_ret_value_inv ∅ (vconst c) w Hclosed
      ltac:(constructor) Heval) as ->.
    rewrite msubst_empty. reflexivity.
  - intros ->.
    pose proof (tm_eval_in_store_ret_value ∅ (vconst c) Hclosed
      ltac:(constructor)) as H.
    rewrite msubst_empty in H. exact H.
Qed.

Lemma ext_reduction_matchlist_nil_iff enil econs v :
  lc_tm (tmatchlist (vconst (clist [])) enil econs) ->
  tmatchlist (vconst (clist [])) enil econs →* tret v <-> enil →* tret v.
Proof.
  intros Hlc. split.
  - intros Hsteps.
    destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
    + discriminate.
    + inversion Hstep; subst.
      inversion H; subst; try discriminate. exact Hrest.
  - intros Hsteps.
    eapply steps_trans; [ |exact Hsteps].
    apply steps_R. apply Step_head. apply HS_MatchListNil. exact Hlc.
Qed.

Lemma ext_must_terminating_matchlist_nil_equiv enil econs :
  lc_tm (tmatchlist (vconst (clist [])) enil econs) ->
  must_terminating (tmatchlist (vconst (clist [])) enil econs) <->
  must_terminating enil.
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_MatchListNil. exact Hlc.
  - apply Must_step.
    + eexists. apply Step_head. apply HS_MatchListNil. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.

Lemma ext_tm_eval_in_store_match_list_nil σ v enil hd tl econs w :
  store_closed σ ->
  lc_tm (match_list_named v enil hd tl econs) ->
  m{σ} v = vconst (clist []) ->
  tm_eval_in_store σ (match_list_named v enil hd tl econs) w <->
  tm_eval_in_store σ enil w.
Proof.
  intros Hclosed Hlc_match Hv.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    unfold match_list_named. rewrite msubst_tmatchlist, Hv.
    apply ext_reduction_matchlist_nil_iff.
    rewrite <- Hv, <- msubst_tmatchlist.
    apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma ext_tm_total_in_store_match_list_nil σ v enil hd tl econs :
  store_closed σ ->
  lc_tm (match_list_named v enil hd tl econs) ->
  m{σ} v = vconst (clist []) ->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
    (match_list_named v enil hd tl econs)) <->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ) enil).
Proof.
  intros Hclosed Hlc_match Hv.
  rewrite !lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite !lstore_free_part_lift_free.
  rewrite !subst_map_tm_eq_msubst.
  unfold match_list_named. rewrite msubst_tmatchlist, Hv.
  apply ext_must_terminating_matchlist_nil_equiv.
  rewrite <- Hv, <- msubst_tmatchlist.
  apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
Qed.

Lemma ext_nil_pattern_pointwise Σ Γ x (m : WfWorldT) :
  m ⊨ ty_denote_under Σ Γ (list_match_eq_ty (vfvar x)) (tret (vconst (clist []))) ->
  forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (clist [])).
Proof.
  intros Hden σ Hσ.
  unfold ty_denote_under, ty_denote, list_match_eq_ty, over_ty, under_ty in Hden.
  cbn [cty_depth ty_denote_gas Nat.max] in Hden.
  rewrite res_models_and_iff in Hden. destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter. destruct Hinter as [Hover _].
  eapply (ext_over_eq_fvar_lookup 0 _ TList x _ m σ); [exact Hover|exact Hσ| ].
  apply ext_tm_eval_in_store_ret_const. reflexivity.
Qed.


(** ** Branch transport and the per-world match lemmas *)

Lemma ext_branch_transport Σ Γ τ ebr em (m : WfWorldT) :
  context_typing_wf Σ Γ em τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  tm_equiv_on m ebr em ->
  tm_total_equiv_on m ebr em ->
  m ⊨ ty_denote_under Σ Γ τ ebr ->
  m ⊨ ty_denote_under Σ Γ τ em.
Proof.
  intros Hwf_m Hctx Hequiv Htotal Hden.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ em m Hwf_m Hctx) as Hstatic_m.
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf_m) as Hlc_m.
  unfold ty_denote_under, ty_denote in Hden |- *.
  pose proof (ty_denote_gas_zero_of_guard _ _ _ _
    (ty_denote_gas_guard _ _ _ _ _ Hden)) as Hzero_b.
  assert (Hfv_m_dom : fv_tm em ⊆ world_dom (m : WorldT)).
  { eapply ty_static_guard_fv_tm_subset. exact Hstatic_m. }
  pose proof (ty_denote_gas_zero_transport_static_tm_equiv
    _ τ ebr em m Hequiv Htotal Hstatic_m Hlc_m Hfv_m_dom Hzero_b) as Hzero_m.
  eapply ty_denote_gas_tm_equiv; [ |exact Hden].
  split; [exact Hequiv| ]. split; [exact Htotal| ]. split; assumption.
Qed.

Lemma ext_list_match_cons_world Σ Γ x enil hd tl econs τ (m : WfWorldT) :
  hd <> tl ->
  context_typing_wf Σ Γ (match_list_named (vfvar x) enil hd tl econs) τ ->
  context_typing_wf Σ Γ (tcons (vfvar hd) (vfvar tl)) (list_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γ econs τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ (list_match_eq_ty (vfvar x)) (tcons (vfvar hd) (vfvar tl)) ->
  m ⊨ ty_denote_under Σ Γ τ econs ->
  m ⊨ ty_denote_under Σ Γ τ (match_list_named (vfvar x) enil hd tl econs).
Proof.
  intros Hne Hwf_m Hwf_eq Hwf_c Hctx Heq Hc.
  set (e := tcons (vfvar hd) (vfvar tl)) in *.
  set (em := match_list_named (vfvar x) enil hd tl econs) in *.
  pose proof (ext_cons_pattern_pointwise Σ Γ x hd tl m Hwf_eq Hctx Heq) as Hpw.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ em m Hwf_m Hctx) as Hstatic_m.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ econs m Hwf_c Hctx) as Hstatic_c.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (list_match_eq_ty (vfvar x)) e m Hwf_eq Hctx) as Hstatic_e.
  set (X := fv_tm em ∪ fv_tm econs ∪ fv_tm e).
  assert (Hclosed : wfworld_closed_on X m).
  {
    apply wfworld_closed_on_union; [apply wfworld_closed_on_union| ];
      eapply ty_static_guard_wfworld_closed_on_term; eassumption.
  }
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf_m) as Hlc_m.
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf_c) as Hlc_c.
  assert (Hfv_m : fv_tm em ⊆ X) by (subst X; set_solver).
  assert (Hfv_c : fv_tm econs ⊆ X) by (subst X; set_solver).
  assert (HxX : x ∈ X) by (subst X em; unfold match_list_named; cbn; set_solver).
  assert (HhdX : hd ∈ X) by (subst X e; cbn; set_solver).
  assert (HtlX : tl ∈ X) by (subst X e; cbn; set_solver).
  assert (Hstore : forall σ, (m : WorldT) σ ->
    exists n xs,
      store_closed (store_restrict σ X) /\
      (store_restrict σ X : StoreT) !! hd = Some (vconst (cnat n)) /\
      (store_restrict σ X : StoreT) !! tl = Some (vconst (clist xs)) /\
      m{store_restrict σ X} (vfvar x) = vconst (clist (n :: xs))).
  {
    intros σ Hσ.
    destruct (Hpw σ Hσ) as [n [xs [Hh [Ht Hx]]]].
    exists n, xs.
    pose proof (Hclosed σ Hσ) as HσX.
    split; [exact HσX| ].
    split; [apply storeA_restrict_lookup_some_2; assumption| ].
    split; [apply storeA_restrict_lookup_some_2; assumption| ].
    apply msubst_fvar_lookup_closed; [exact (proj1 HσX)| ].
    apply storeA_restrict_lookup_some_2; assumption.
  }
  apply (ext_branch_transport Σ Γ τ econs em m Hwf_m Hctx); [ | |exact Hc].
  - intros σ w Hσ.
    destruct (Hstore σ Hσ) as [n [xs [HσX [Hh [Ht Hx]]]]].
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ econs w X Hfv_c).
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ em w X Hfv_m).
    symmetry.
    apply (ext_tm_eval_in_store_match_list_cons _ (vfvar x) enil hd tl econs n xs w
      HσX Hlc_c Hne Hlc_m Hh Ht Hx).
  - intros σ Hσ.
    destruct (Hstore σ Hσ) as [n [xs [HσX [Hh [Ht Hx]]]]].
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) econs Hlc_c).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_c]. }
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) em Hlc_m).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_m]. }
    symmetry.
    apply (ext_tm_total_in_store_match_list_cons _ (vfvar x) enil hd tl econs n xs
      HσX Hlc_c Hne Hlc_m Hh Ht Hx).
Qed.

Lemma ext_list_match_nil_world Σ Γ x enil hd tl econs τ (m : WfWorldT) :
  context_typing_wf Σ Γ (match_list_named (vfvar x) enil hd tl econs) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ (list_match_eq_ty (vfvar x)) (tret (vconst (clist []))) ->
  m ⊨ ty_denote_under Σ Γ τ enil ->
  m ⊨ ty_denote_under Σ Γ τ (match_list_named (vfvar x) enil hd tl econs).
Proof.
  intros Hwf_m Hctx Heq Hn.
  set (em := match_list_named (vfvar x) enil hd tl econs) in *.
  pose proof (ext_nil_pattern_pointwise Σ Γ x m Heq) as Hpw.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ em m Hwf_m Hctx) as Hstatic_m.
  set (X := fv_tm em).
  assert (Hclosed : wfworld_closed_on X m).
  { eapply ty_static_guard_wfworld_closed_on_term; eassumption. }
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf_m) as Hlc_m.
  assert (Hfv_n : fv_tm enil ⊆ X) by (subst X em; unfold match_list_named; cbn; set_solver).
  assert (HxX : x ∈ X) by (subst X em; unfold match_list_named; cbn; set_solver).
  assert (Hlc_n : lc_tm enil).
  { subst em. unfold match_list_named in Hlc_m. inversion Hlc_m; assumption. }
  assert (Hstore : forall σ, (m : WorldT) σ ->
      store_closed (store_restrict σ X) /\
      m{store_restrict σ X} (vfvar x) = vconst (clist [])).
  {
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as HσX.
    split; [exact HσX| ].
    apply msubst_fvar_lookup_closed; [exact (proj1 HσX)| ].
    apply storeA_restrict_lookup_some_2; [apply Hpw; exact Hσ|exact HxX].
  }
  apply (ext_branch_transport Σ Γ τ enil em m Hwf_m Hctx); [ | |exact Hn].
  - intros σ w Hσ.
    destruct (Hstore σ Hσ) as [HσX Hx].
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ enil w X Hfv_n).
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ em w X ltac:(reflexivity)).
    symmetry.
    apply (ext_tm_eval_in_store_match_list_nil _ (vfvar x) enil hd tl econs w
      HσX Hlc_m Hx).
  - intros σ Hσ.
    destruct (Hstore σ Hσ) as [HσX Hx].
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) enil Hlc_n).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_n]. }
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) em Hlc_m).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|reflexivity]. }
    symmetry.
    apply (ext_tm_total_in_store_match_list_nil _ (vfvar x) enil hd tl econs
      HσX Hlc_m Hx).
Qed.

(** Corrected, paper-form T-Match (cons branch only): the context binds the
    pattern variables itself. *)
Lemma ext_list_match_cons_paper_sound Σ Γ x enil hd tl econs τ :
  hd <> tl ->
  context_typing_wf Σ Γ (match_list_named (vfvar x) enil hd tl econs) τ ->
  context_typing_wf Σ Γ (tcons (vfvar hd) (vfvar tl)) (list_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γ econs τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (list_match_eq_ty (vfvar x)) (tcons (vfvar hd) (vfvar tl))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ econs) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (match_list_named (vfvar x) enil hd tl econs).
Proof.
  intros Hne Hwf_m Hwf_eq Hwf_c Heq Hc m Hctx.
  eapply ext_list_match_cons_world; eauto.
Qed.

(** Soundness of the nil-only list match. *)
Lemma ext_list_match_nil_sound Σ Γ x enil hd tl econs τ :
  context_typing_wf Σ Γ (match_list_named (vfvar x) enil hd tl econs) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (list_match_eq_ty (vfvar x)) (tret (vconst (clist [])))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ enil) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (match_list_named (vfvar x) enil hd tl econs).
Proof.
  intros Hwf_m Heq Hn m Hctx.
  eapply ext_list_match_nil_world; eauto.
Qed.

Lemma ext_context_typing_wf_sum_l Σ Γt Γf e τt τf :
  context_typing_wf Σ (CtxSum Γt Γf) e (CTSum τt τf) ->
  context_typing_wf Σ Γt e τt.
Proof.
  intros Hwf.
  destruct Hwf as [Hbasic_sum [Hty_sum Htm]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [Hbasic_t [_ [_ _]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [Hty_t [_ _]].
  cbn [erase_ctx erase_ty] in Htm.
  split; [exact Hbasic_t| ]. split; [exact Hty_t|exact Htm].
Qed.

Lemma ext_context_typing_wf_sum_r Σ Γt Γf e τt τf :
  context_typing_wf Σ (CtxSum Γt Γf) e (CTSum τt τf) ->
  context_typing_wf Σ Γf e τf.
Proof.
  intros Hwf.
  destruct Hwf as [Hbasic_sum [Hty_sum Htm]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [_ [Hbasic_f [_ Herase_ctx]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [_ [Hty_f Herase_ty]].
  cbn [erase_ctx erase_ty] in Htm.
  split; [exact Hbasic_f| ].
  split.
  - replace (dom (erase_ctx Γf)) with (dom (erase_ctx Γt)); [exact Hty_f| ].
    rewrite Herase_ctx. reflexivity.
  - rewrite <- Herase_ctx, <- Herase_ty. exact Htm.
Qed.

(** Corrected, paper-form T-Match with both branches reachable. *)
Lemma ext_list_match_both_paper_sound Σ Γn Γc x enil hd tl econs τn τc :
  hd <> tl ->
  context_typing_wf Σ (CtxSum Γn Γc)
    (match_list_named (vfvar x) enil hd tl econs) (CTSum τn τc) ->
  context_typing_wf Σ Γc (tcons (vfvar hd) (vfvar tl)) (list_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γc econs τc ->
  (ctx_denote_under Σ Γn ⊫
    ty_denote_under Σ Γn (list_match_eq_ty (vfvar x)) (tret (vconst (clist [])))) ->
  (ctx_denote_under Σ Γc ⊫
    ty_denote_under Σ Γc (list_match_eq_ty (vfvar x)) (tcons (vfvar hd) (vfvar tl))) ->
  (ctx_denote_under Σ Γn ⊫ ty_denote_under Σ Γn τn enil) ->
  (ctx_denote_under Σ Γc ⊫ ty_denote_under Σ Γc τc econs) ->
  ctx_denote_under Σ (CtxSum Γn Γc) ⊫
    ty_denote_under Σ (CtxSum Γn Γc) (CTSum τn τc)
      (match_list_named (vfvar x) enil hd tl econs).
Proof.
  intros Hne Hwf Hwf_eq Hwf_c Heq_n Heq_c Hn Hc m Hctx.
  set (em := match_list_named (vfvar x) enil hd tl econs) in *.
  pose proof Hwf as Hwf_for_eqs.
  destruct Hwf_for_eqs as [Hbasic_sum [Hty_sum _]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [_ [_ [_ Herase_ctx]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [_ [_ Herase_ty]].
  destruct (ctx_denote_under_sum_elim Σ Γn Γc m Hctx)
    as [mn [mc [Hdef [Hle [HΓn HΓc]]]]].
  pose proof (ext_context_typing_wf_sum_l _ _ _ _ _ _ Hwf) as Hwf_n.
  pose proof (ext_context_typing_wf_sum_r _ _ _ _ _ _ Hwf) as Hwf_cm.
  pose proof (ext_list_match_nil_world Σ Γn x enil hd tl econs τn mn
    Hwf_n HΓn (Heq_n mn HΓn) (Hn mn HΓn)) as Hmatch_n.
  pose proof (ext_list_match_cons_world Σ Γc x enil hd tl econs τc mc
    Hne Hwf_cm Hwf_eq Hwf_c HΓc (Heq_c mc HΓc) (Hc mc HΓc)) as Hmatch_c.
  fold em in Hmatch_n, Hmatch_c.
  unfold ty_denote_under, ty_denote in Hmatch_n, Hmatch_c |- *.
  rewrite <- (ty_denote_gas_saturate
      (cty_depth (CTSum τn τc))
      (atom_env_to_lty_env (erase_ctx Γn)) τn em) in Hmatch_n
    by (cbn [cty_depth]; lia).
  rewrite <- (ty_denote_gas_saturate
      (cty_depth (CTSum τn τc))
      (atom_env_to_lty_env (erase_ctx Γc)) τc em) in Hmatch_c
    by (cbn [cty_depth]; lia).
  replace (atom_env_to_lty_env (erase_ctx Γc))
    with (atom_env_to_lty_env (erase_ctx Γn)) in Hmatch_c
    by (rewrite Herase_ctx; reflexivity).
  assert (Htotal_n : mn ⊨ expr_total_formula em).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_n) as Hguard.
    repeat rewrite res_models_and_iff in Hguard. tauto.
  }
  assert (Htotal_c : mc ⊨ expr_total_formula em).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_c) as Hguard.
    repeat rewrite res_models_and_iff in Hguard. tauto.
  }
  assert (Htotal_m : m ⊨ expr_total_formula em).
  {
    eapply res_models_kripke; [exact Hle| ].
    eapply expr_total_formula_sum_intro; eauto.
  }
  assert (Hstatic :
      m ⊨ ty_static_guard_formula
        (atom_env_to_lty_env (erase_ctx (CtxSum Γn Γc)))
        (CTSum τn τc) em).
  { exact (context_typing_wf_denot_static_guard_full
      Σ (CtxSum Γn Γc) (CTSum τn τc) em m Hwf Hctx). }
  replace (atom_env_to_lty_env (erase_ctx (CtxSum Γn Γc)))
    with (atom_env_to_lty_env (erase_ctx Γn)) in Hstatic |- *
    by (cbn [erase_ctx]; reflexivity).
  eapply ty_denote_gas_sum_intro_from_branch_refinement
    with (m1 := mn) (m2 := mc) (Hdef := Hdef).
  - exact Hle.
  - exact Herase_ty.
  - cbn [cty_depth]. lia.
  - cbn [cty_depth]. lia.
  - exact Hstatic.
  - exact Htotal_m.
  - exact Hmatch_n.
  - exact Hmatch_c.
Qed.

(** ** Trees: operational and locally-nameless facts *)

Lemma ext_reduction_matchtree_node_iff n l r eleaf enode v :
  lc_tm (tmatchtree (vconst (ctree (tr_node n l r))) eleaf enode) ->
  tmatchtree (vconst (ctree (tr_node n l r))) eleaf enode →* tret v <->
  open_tree_node_branch_value (vconst (cnat n)) (vconst (ctree l))
    (vconst (ctree r)) enode →* tret v.
Proof.
  intros Hlc. split.
  - intros Hsteps.
    destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
    + discriminate.
    + inversion Hstep; subst.
      inversion H; subst; try discriminate. exact Hrest.
  - intros Hsteps.
    eapply steps_trans; [ |exact Hsteps].
    apply steps_R. apply Step_head. apply HS_MatchTreeNode. exact Hlc.
Qed.

Lemma ext_must_terminating_matchtree_node_equiv n l r eleaf enode :
  lc_tm (tmatchtree (vconst (ctree (tr_node n l r))) eleaf enode) ->
  must_terminating (tmatchtree (vconst (ctree (tr_node n l r))) eleaf enode) <->
  must_terminating (open_tree_node_branch_value (vconst (cnat n))
    (vconst (ctree l)) (vconst (ctree r)) enode).
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_MatchTreeNode. exact Hlc.
  - apply Must_step.
    + eexists. apply Step_head. apply HS_MatchTreeNode. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.

Lemma ext_reduction_matchtree_leaf_iff eleaf enode v :
  lc_tm (tmatchtree (vconst (ctree tr_leaf)) eleaf enode) ->
  tmatchtree (vconst (ctree tr_leaf)) eleaf enode →* tret v <-> eleaf →* tret v.
Proof.
  intros Hlc. split.
  - intros Hsteps.
    destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
    + discriminate.
    + inversion Hstep; subst.
      inversion H; subst; try discriminate. exact Hrest.
  - intros Hsteps.
    eapply steps_trans; [ |exact Hsteps].
    apply steps_R. apply Step_head. apply HS_MatchTreeLeaf. exact Hlc.
Qed.

Lemma ext_must_terminating_matchtree_leaf_equiv eleaf enode :
  lc_tm (tmatchtree (vconst (ctree tr_leaf)) eleaf enode) ->
  must_terminating (tmatchtree (vconst (ctree tr_leaf)) eleaf enode) <->
  must_terminating eleaf.
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_MatchTreeLeaf. exact Hlc.
  - apply Must_step.
    + eexists. apply Step_head. apply HS_MatchTreeLeaf. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.

Lemma ext_open_close_node_branch root left right enode :
  lc_tm enode -> root <> left -> root <> right -> left <> right ->
  open_tree_node_branch root left right
    (close_tm right 2 (close_tm left 1 (close_tm root 0 enode))) = enode.
Proof.
  intros Hlc H01 H02 H12.
  unfold open_tree_node_branch, open_tree_node_branch_value.
  rewrite (ext_open_close_commute_tm root right) by (congruence || lia).
  rewrite (ext_open_close_commute_tm root left) by (congruence || lia).
  rewrite open_close_var_tm by exact Hlc.
  rewrite (ext_open_close_commute_tm left right) by (congruence || lia).
  rewrite (open_close_var_tm_aux left enode 1) by (apply open_rec_lc_tm; exact Hlc).
  apply open_close_var_tm_aux.
  apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma ext_msubst_node_branch σ root left right enode n l r :
  store_closed σ -> lc_tm enode ->
  root <> left -> root <> right -> left <> right ->
  σ !! root = Some (vconst (cnat n)) ->
  σ !! left = Some (vconst (ctree l)) ->
  σ !! right = Some (vconst (ctree r)) ->
  m{σ} enode =
  open_tree_node_branch_value (vconst (cnat n)) (vconst (ctree l))
    (vconst (ctree r))
    (m{σ} (close_tm right 2 (close_tm left 1 (close_tm root 0 enode)))).
Proof.
  intros [Hclosed Hlcσ] Hlc H01 H02 H12 Hroot Hleft Hright.
  set (E := close_tm right 2 (close_tm left 1 (close_tm root 0 enode))).
  assert (HrightE : right ∉ fv_tm E) by (subst E; apply close_rm_fv_tm).
  assert (HleftE : left ∉ fv_tm E).
  { subst E. intros Hin. apply ext_close_fv_tm_subset in Hin.
    exact (close_rm_fv_tm left 1 _ Hin). }
  assert (HrootE : root ∉ fv_tm E).
  { subst E. intros Hin. apply ext_close_fv_tm_subset in Hin.
    apply ext_close_fv_tm_subset in Hin.
    exact (close_rm_fv_tm root 0 enode Hin). }
  rewrite <- (ext_open_close_node_branch root left right enode Hlc H01 H02 H12) at 1.
  fold E.
  unfold open_tree_node_branch, open_tree_node_branch_value.
  rewrite (msubst_open_lookup_tm σ (open_tm 1 (vfvar left) (open_tm 0 (vfvar root) E)) 2 right
    (vconst (ctree r)) Hclosed Hlcσ Hright).
  2:{ intros Hin. apply open_fv_tm in Hin. cbn [fv_value] in Hin.
      apply elem_of_union in Hin as [Hin|Hin]; [set_solver| ].
      apply open_fv_tm in Hin. cbn [fv_value] in Hin. set_solver. }
  erewrite (msubst_open_lookup_tm _ (open_tm 0 (vfvar root) E) 1 left
    (vconst (ctree l))).
  2:{ apply closed_env_delete. exact Hclosed. }
  2:{ apply lc_env_delete. exact Hlcσ. }
  2:{ etransitivity; [apply lookup_delete_ne; congruence|exact Hleft]. }
  2:{ intros Hin. apply open_fv_tm in Hin. cbn [fv_value] in Hin. set_solver. }
  erewrite (msubst_open_lookup_tm _ E 0 root (vconst (cnat n))).
  2:{ apply closed_env_delete. apply closed_env_delete. exact Hclosed. }
  2:{ apply lc_env_delete. apply lc_env_delete. exact Hlcσ. }
  2:{ etransitivity; [apply lookup_delete_ne; congruence| ].
      etransitivity; [apply lookup_delete_ne; congruence|exact Hroot]. }
  2:{ exact HrootE. }
  f_equal. f_equal. f_equal.
  eapply (msubst_agree tm _ σ (fv_tm E) E).
  - apply closed_env_delete. apply closed_env_delete. apply closed_env_delete.
    exact Hclosed.
  - exact Hclosed.
  - reflexivity.
  - intros z Hz.
    etransitivity; [apply lookup_delete_ne; intros ->; contradiction| ].
    etransitivity; [apply lookup_delete_ne; intros ->; contradiction| ].
    apply lookup_delete_ne; intros ->; contradiction.
Qed.

Lemma ext_tm_eval_in_store_match_tree_node σ v eleaf root left right enode n l r w :
  store_closed σ -> lc_tm enode ->
  root <> left -> root <> right -> left <> right ->
  lc_tm (match_tree_named v eleaf root left right enode) ->
  σ !! root = Some (vconst (cnat n)) ->
  σ !! left = Some (vconst (ctree l)) ->
  σ !! right = Some (vconst (ctree r)) ->
  m{σ} v = vconst (ctree (tr_node n l r)) ->
  tm_eval_in_store σ (match_tree_named v eleaf root left right enode) w <->
  tm_eval_in_store σ enode w.
Proof.
  intros Hclosed Hlc H01 H02 H12 Hlc_match Hroot Hleft Hright Hv.
  pose proof (ext_msubst_node_branch σ root left right enode n l r
    Hclosed Hlc H01 H02 H12 Hroot Hleft Hright) as Hbranch.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    unfold match_tree_named. rewrite msubst_tmatchtree, Hv.
    rewrite Hbranch.
    apply ext_reduction_matchtree_node_iff.
    rewrite <- Hv, <- msubst_tmatchtree.
    apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma ext_tm_total_in_store_match_tree_node σ v eleaf root left right enode n l r :
  store_closed σ -> lc_tm enode ->
  root <> left -> root <> right -> left <> right ->
  lc_tm (match_tree_named v eleaf root left right enode) ->
  σ !! root = Some (vconst (cnat n)) ->
  σ !! left = Some (vconst (ctree l)) ->
  σ !! right = Some (vconst (ctree r)) ->
  m{σ} v = vconst (ctree (tr_node n l r)) ->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
    (match_tree_named v eleaf root left right enode)) <->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ) enode).
Proof.
  intros Hclosed Hlc H01 H02 H12 Hlc_match Hroot Hleft Hright Hv.
  pose proof (ext_msubst_node_branch σ root left right enode n l r
    Hclosed Hlc H01 H02 H12 Hroot Hleft Hright) as Hbranch.
  rewrite !lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite !lstore_free_part_lift_free.
  rewrite !subst_map_tm_eq_msubst.
  unfold match_tree_named. rewrite msubst_tmatchtree, Hv.
  rewrite Hbranch.
  apply ext_must_terminating_matchtree_node_equiv.
  rewrite <- Hv, <- msubst_tmatchtree.
  apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
Qed.

Lemma ext_tm_eval_in_store_match_tree_leaf σ v eleaf root left right enode w :
  store_closed σ ->
  lc_tm (match_tree_named v eleaf root left right enode) ->
  m{σ} v = vconst (ctree tr_leaf) ->
  tm_eval_in_store σ (match_tree_named v eleaf root left right enode) w <->
  tm_eval_in_store σ eleaf w.
Proof.
  intros Hclosed Hlc_match Hv.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    unfold match_tree_named. rewrite msubst_tmatchtree, Hv.
    apply ext_reduction_matchtree_leaf_iff.
    rewrite <- Hv, <- msubst_tmatchtree.
    apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma ext_tm_total_in_store_match_tree_leaf σ v eleaf root left right enode :
  store_closed σ ->
  lc_tm (match_tree_named v eleaf root left right enode) ->
  m{σ} v = vconst (ctree tr_leaf) ->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
    (match_tree_named v eleaf root left right enode)) <->
  must_terminating (lstore_instantiate_tm (lstore_lift_free σ) eleaf).
Proof.
  intros Hclosed Hlc_match Hv.
  rewrite !lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite !lstore_free_part_lift_free.
  rewrite !subst_map_tm_eq_msubst.
  unfold match_tree_named. rewrite msubst_tmatchtree, Hv.
  apply ext_must_terminating_matchtree_leaf_equiv.
  rewrite <- Hv, <- msubst_tmatchtree.
  apply msubst_lc; [exact (proj2 Hclosed)|exact Hlc_match].
Qed.

Lemma ext_reduction_tnode_iff n l r w :
  tnode (vconst (cnat n)) (vconst (ctree l)) (vconst (ctree r)) →* tret w <->
  w = vconst (ctree (tr_node n l r)).
Proof.
  split.
  - intros Hsteps.
    destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
    + discriminate.
    + inversion Hstep; subst.
      inversion H; subst; try discriminate.
      pose proof (value_steps_self _ _ Hrest) as Heq. inversion Heq. reflexivity.
  - intros ->.
    apply steps_R. apply Step_head. apply HS_TreeNode.
    constructor; constructor.
Qed.

Lemma ext_tm_eval_in_store_tnode σ root left right n l r w :
  store_closed σ ->
  σ !! root = Some (vconst (cnat n)) ->
  σ !! left = Some (vconst (ctree l)) ->
  σ !! right = Some (vconst (ctree r)) ->
  tm_eval_in_store σ (tnode (vfvar root) (vfvar left) (vfvar right)) w <->
  w = vconst (ctree (tr_node n l r)).
Proof.
  intros Hclosed Hroot Hleft Hright.
  unfold tm_eval_in_store.
  rewrite expr_eval_in_store_no_bvars_iff.
  - rewrite lstore_free_part_lift_free, subst_map_tm_eq_msubst.
    rewrite msubst_tnode.
    rewrite (msubst_fvar_lookup_closed σ root _ (proj1 Hclosed) Hroot).
    rewrite (msubst_fvar_lookup_closed σ left _ (proj1 Hclosed) Hleft).
    rewrite (msubst_fvar_lookup_closed σ right _ (proj1 Hclosed) Hright).
    apply ext_reduction_tnode_iff.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma ext_tnode_fvar_typing_inv (G : gmap atom ty) root left right T :
  G ⊢ₑ tnode (vfvar root) (vfvar left) (vfvar right) ⋮ T ->
  G !! root = Some (TBase TNat) /\ G !! left = Some (TBase TTree) /\
  G !! right = Some (TBase TTree).
Proof.
  intros H. inversion H; subst.
  match goal with
  | H1 : G ⊢ᵥ vfvar root ⋮ _, H2 : G ⊢ᵥ vfvar left ⋮ _,
    H3 : G ⊢ᵥ vfvar right ⋮ _ |- _ =>
      inversion H1; inversion H2; inversion H3; subst;
      split; [assumption|split; assumption]
  end.
Qed.

Lemma ext_node_pattern_pointwise Σ Γ x root left right (m : WfWorldT) :
  context_typing_wf Σ Γ (tnode (vfvar root) (vfvar left) (vfvar right))
    (tree_match_eq_ty (vfvar x)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ (tree_match_eq_ty (vfvar x))
    (tnode (vfvar root) (vfvar left) (vfvar right)) ->
  forall σ, (m : WorldT) σ ->
    exists n l r,
      σ !! root = Some (vconst (cnat n)) /\
      σ !! left = Some (vconst (ctree l)) /\
      σ !! right = Some (vconst (ctree r)) /\
      σ !! x = Some (vconst (ctree (tr_node n l r))).
Proof.
  intros Hwf Hctx Hden σ Hσ.
  set (e := tnode (vfvar root) (vfvar left) (vfvar right)) in *.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (tree_match_eq_ty (vfvar x)) e m Hwf Hctx) as Hstatic.
  pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic) as Hworld.
  pose proof (ty_static_guard_wfworld_closed_on_term _ _ _ _ Hstatic) as Hclosed_e.
  pose proof (context_typing_wf_basic_typing _ _ _ _ Hwf) as Hbasic.
  destruct (ext_tnode_fvar_typing_inv _ _ _ _ _ Hbasic) as [Hr_ty [Hl_ty Hrr_ty]].
  destruct (ext_basic_world_typed_lookup Δ m σ root (TBase TNat) Hworld Hσ)
    as [vr [Hσr Hvr]].
  { subst Δ. rewrite atom_store_to_lvar_store_lookup_free. exact Hr_ty. }
  destruct (ext_basic_world_typed_lookup Δ m σ left (TBase TTree) Hworld Hσ)
    as [vl [Hσl Hvl]].
  { subst Δ. rewrite atom_store_to_lvar_store_lookup_free. exact Hl_ty. }
  destruct (ext_basic_world_typed_lookup Δ m σ right (TBase TTree) Hworld Hσ)
    as [vrr [Hσrr Hvrr]].
  { subst Δ. rewrite atom_store_to_lvar_store_lookup_free. exact Hrr_ty. }
  destruct (basic_typing_nat_canonical_form vr Hvr) as [n ->].
  destruct (basic_typing_tree_canonical_form vl Hvl) as [l ->].
  destruct (basic_typing_tree_canonical_form vrr Hvrr) as [r ->].
  exists n, l, r. split; [exact Hσr| ]. split; [exact Hσl| ]. split; [exact Hσrr| ].
  assert (Heval : tm_eval_in_store σ e (vconst (ctree (tr_node n l r)))).
  {
    apply (proj1 (tm_eval_in_store_restrict_fv_subset σ e _ (fv_tm e)
      ltac:(reflexivity))).
    apply (proj2 (ext_tm_eval_in_store_tnode _ root left right n l r _
      (Hclosed_e σ Hσ)
      ltac:(apply storeA_restrict_lookup_some_2; [exact Hσr|subst e; cbn; set_solver])
      ltac:(apply storeA_restrict_lookup_some_2; [exact Hσl|subst e; cbn; set_solver])
      ltac:(apply storeA_restrict_lookup_some_2; [exact Hσrr|subst e; cbn; set_solver]))).
    reflexivity.
  }
  unfold ty_denote_under, ty_denote, tree_match_eq_ty, over_ty, under_ty in Hden.
  cbn [cty_depth ty_denote_gas Nat.max] in Hden.
  rewrite res_models_and_iff in Hden. destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter. destruct Hinter as [Hover _].
  eapply (ext_over_eq_fvar_lookup 0 _ TTree x e m σ); [exact Hover|exact Hσ|exact Heval].
Qed.

Lemma ext_leaf_pattern_pointwise Σ Γ x (m : WfWorldT) :
  m ⊨ ty_denote_under Σ Γ (tree_match_eq_ty (vfvar x)) (tret (vconst (ctree tr_leaf))) ->
  forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (ctree tr_leaf)).
Proof.
  intros Hden σ Hσ.
  unfold ty_denote_under, ty_denote, tree_match_eq_ty, over_ty, under_ty in Hden.
  cbn [cty_depth ty_denote_gas Nat.max] in Hden.
  rewrite res_models_and_iff in Hden. destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter. destruct Hinter as [Hover _].
  eapply (ext_over_eq_fvar_lookup 0 _ TTree x _ m σ); [exact Hover|exact Hσ| ].
  apply ext_tm_eval_in_store_ret_const. reflexivity.
Qed.

Lemma ext_tree_match_node_world Σ Γ x eleaf root left right enode τ (m : WfWorldT) :
  root <> left -> root <> right -> left <> right ->
  context_typing_wf Σ Γ (match_tree_named (vfvar x) eleaf root left right enode) τ ->
  context_typing_wf Σ Γ (tnode (vfvar root) (vfvar left) (vfvar right))
    (tree_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γ enode τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ (tree_match_eq_ty (vfvar x))
    (tnode (vfvar root) (vfvar left) (vfvar right)) ->
  m ⊨ ty_denote_under Σ Γ τ enode ->
  m ⊨ ty_denote_under Σ Γ τ (match_tree_named (vfvar x) eleaf root left right enode).
Proof.
  intros H01 H02 H12 Hwf_m Hwf_eq Hwf_c Hctx Heq Hc.
  set (e := tnode (vfvar root) (vfvar left) (vfvar right)) in *.
  set (em := match_tree_named (vfvar x) eleaf root left right enode) in *.
  pose proof (ext_node_pattern_pointwise Σ Γ x root left right m Hwf_eq Hctx Heq) as Hpw.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ em m Hwf_m Hctx) as Hstatic_m.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ enode m Hwf_c Hctx) as Hstatic_c.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (tree_match_eq_ty (vfvar x)) e m Hwf_eq Hctx) as Hstatic_e.
  set (X := fv_tm em ∪ fv_tm enode ∪ fv_tm e).
  assert (Hclosed : wfworld_closed_on X m).
  {
    apply wfworld_closed_on_union; [apply wfworld_closed_on_union| ];
      eapply ty_static_guard_wfworld_closed_on_term; eassumption.
  }
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf_m) as Hlc_m.
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf_c) as Hlc_c.
  assert (Hfv_m : fv_tm em ⊆ X) by (subst X; set_solver).
  assert (Hfv_c : fv_tm enode ⊆ X) by (subst X; set_solver).
  assert (HxX : x ∈ X) by (subst X em; unfold match_tree_named; cbn; set_solver).
  assert (HrX : root ∈ X) by (subst X e; cbn; set_solver).
  assert (HlX : left ∈ X) by (subst X e; cbn; set_solver).
  assert (HrrX : right ∈ X) by (subst X e; cbn; set_solver).
  assert (Hstore : forall σ, (m : WorldT) σ ->
    exists n l r,
      store_closed (store_restrict σ X) /\
      (store_restrict σ X : StoreT) !! root = Some (vconst (cnat n)) /\
      (store_restrict σ X : StoreT) !! left = Some (vconst (ctree l)) /\
      (store_restrict σ X : StoreT) !! right = Some (vconst (ctree r)) /\
      m{store_restrict σ X} (vfvar x) = vconst (ctree (tr_node n l r))).
  {
    intros σ Hσ.
    destruct (Hpw σ Hσ) as [n [l [r [Hr [Hl [Hrr Hx]]]]]].
    exists n, l, r.
    pose proof (Hclosed σ Hσ) as HσX.
    split; [exact HσX| ].
    split; [apply storeA_restrict_lookup_some_2; assumption| ].
    split; [apply storeA_restrict_lookup_some_2; assumption| ].
    split; [apply storeA_restrict_lookup_some_2; assumption| ].
    apply msubst_fvar_lookup_closed; [exact (proj1 HσX)| ].
    apply storeA_restrict_lookup_some_2; assumption.
  }
  apply (ext_branch_transport Σ Γ τ enode em m Hwf_m Hctx); [ | |exact Hc].
  - intros σ w Hσ.
    destruct (Hstore σ Hσ) as [n [l [r [HσX [Hr [Hl [Hrr Hx]]]]]]].
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ enode w X Hfv_c).
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ em w X Hfv_m).
    symmetry.
    apply (ext_tm_eval_in_store_match_tree_node _ (vfvar x) eleaf root left right
      enode n l r w HσX Hlc_c H01 H02 H12 Hlc_m Hr Hl Hrr Hx).
  - intros σ Hσ.
    destruct (Hstore σ Hσ) as [n [l [r [HσX [Hr [Hl [Hrr Hx]]]]]]].
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) enode Hlc_c).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_c]. }
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) em Hlc_m).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_m]. }
    symmetry.
    apply (ext_tm_total_in_store_match_tree_node _ (vfvar x) eleaf root left right
      enode n l r HσX Hlc_c H01 H02 H12 Hlc_m Hr Hl Hrr Hx).
Qed.

Lemma ext_tree_match_leaf_world Σ Γ x eleaf root left right enode τ (m : WfWorldT) :
  context_typing_wf Σ Γ (match_tree_named (vfvar x) eleaf root left right enode) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ (tree_match_eq_ty (vfvar x)) (tret (vconst (ctree tr_leaf))) ->
  m ⊨ ty_denote_under Σ Γ τ eleaf ->
  m ⊨ ty_denote_under Σ Γ τ (match_tree_named (vfvar x) eleaf root left right enode).
Proof.
  intros Hwf_m Hctx Heq Hn.
  set (em := match_tree_named (vfvar x) eleaf root left right enode) in *.
  pose proof (ext_leaf_pattern_pointwise Σ Γ x m Heq) as Hpw.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ em m Hwf_m Hctx) as Hstatic_m.
  set (X := fv_tm em).
  assert (Hclosed : wfworld_closed_on X m).
  { eapply ty_static_guard_wfworld_closed_on_term; eassumption. }
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf_m) as Hlc_m.
  assert (Hfv_n : fv_tm eleaf ⊆ X) by (subst X em; unfold match_tree_named; cbn; set_solver).
  assert (HxX : x ∈ X) by (subst X em; unfold match_tree_named; cbn; set_solver).
  assert (Hlc_n : lc_tm eleaf).
  { subst em. unfold match_tree_named in Hlc_m. inversion Hlc_m; assumption. }
  assert (Hstore : forall σ, (m : WorldT) σ ->
      store_closed (store_restrict σ X) /\
      m{store_restrict σ X} (vfvar x) = vconst (ctree tr_leaf)).
  {
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as HσX.
    split; [exact HσX| ].
    apply msubst_fvar_lookup_closed; [exact (proj1 HσX)| ].
    apply storeA_restrict_lookup_some_2; [apply Hpw; exact Hσ|exact HxX].
  }
  apply (ext_branch_transport Σ Γ τ eleaf em m Hwf_m Hctx); [ | |exact Hn].
  - intros σ w Hσ.
    destruct (Hstore σ Hσ) as [HσX Hx].
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ eleaf w X Hfv_n).
    rewrite <- (tm_eval_in_store_restrict_fv_subset σ em w X ltac:(reflexivity)).
    symmetry.
    apply (ext_tm_eval_in_store_match_tree_leaf _ (vfvar x) eleaf root left right enode w
      HσX Hlc_m Hx).
  - intros σ Hσ.
    destruct (Hstore σ Hσ) as [HσX Hx].
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) eleaf Hlc_n).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_n]. }
    rewrite (tm_must_terminating_agree_on_fv σ (store_restrict σ X) em Hlc_m).
    2:{ rewrite storeA_restrict_twice_subset; [reflexivity|reflexivity]. }
    symmetry.
    apply (ext_tm_total_in_store_match_tree_leaf _ (vfvar x) eleaf root left right enode
      HσX Hlc_m Hx).
Qed.

(** Corrected, paper-form tree match (node branch only). *)
Lemma ext_tree_match_node_paper_sound Σ Γ x eleaf root left right enode τ :
  root <> left -> root <> right -> left <> right ->
  context_typing_wf Σ Γ (match_tree_named (vfvar x) eleaf root left right enode) τ ->
  context_typing_wf Σ Γ (tnode (vfvar root) (vfvar left) (vfvar right))
    (tree_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γ enode τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (tree_match_eq_ty (vfvar x))
      (tnode (vfvar root) (vfvar left) (vfvar right))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ enode) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (match_tree_named (vfvar x) eleaf root left right enode).
Proof.
  intros H01 H02 H12 Hwf_m Hwf_eq Hwf_c Heq Hc m Hctx.
  eapply ext_tree_match_node_world; eauto.
Qed.

(** Soundness of the leaf-only tree match. *)
Lemma ext_tree_match_leaf_sound Σ Γ x eleaf root left right enode τ :
  context_typing_wf Σ Γ (match_tree_named (vfvar x) eleaf root left right enode) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (tree_match_eq_ty (vfvar x)) (tret (vconst (ctree tr_leaf)))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ eleaf) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (match_tree_named (vfvar x) eleaf root left right enode).
Proof.
  intros Hwf_m Heq Hn m Hctx.
  eapply ext_tree_match_leaf_world; eauto.
Qed.

(** Corrected, paper-form tree match with both branches reachable. *)
Lemma ext_tree_match_both_paper_sound Σ Γl Γn x eleaf root left right enode τl τn :
  root <> left -> root <> right -> left <> right ->
  context_typing_wf Σ (CtxSum Γl Γn)
    (match_tree_named (vfvar x) eleaf root left right enode) (CTSum τl τn) ->
  context_typing_wf Σ Γn (tnode (vfvar root) (vfvar left) (vfvar right))
    (tree_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γn enode τn ->
  (ctx_denote_under Σ Γl ⊫
    ty_denote_under Σ Γl (tree_match_eq_ty (vfvar x)) (tret (vconst (ctree tr_leaf)))) ->
  (ctx_denote_under Σ Γn ⊫
    ty_denote_under Σ Γn (tree_match_eq_ty (vfvar x))
      (tnode (vfvar root) (vfvar left) (vfvar right))) ->
  (ctx_denote_under Σ Γl ⊫ ty_denote_under Σ Γl τl eleaf) ->
  (ctx_denote_under Σ Γn ⊫ ty_denote_under Σ Γn τn enode) ->
  ctx_denote_under Σ (CtxSum Γl Γn) ⊫
    ty_denote_under Σ (CtxSum Γl Γn) (CTSum τl τn)
      (match_tree_named (vfvar x) eleaf root left right enode).
Proof.
  intros H01 H02 H12 Hwf Hwf_eq Hwf_c Heq_l Heq_n Hl Hn m Hctx.
  set (em := match_tree_named (vfvar x) eleaf root left right enode) in *.
  pose proof Hwf as Hwf_for_eqs.
  destruct Hwf_for_eqs as [Hbasic_sum [Hty_sum _]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [_ [_ [_ Herase_ctx]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [_ [_ Herase_ty]].
  destruct (ctx_denote_under_sum_elim Σ Γl Γn m Hctx)
    as [ml [mn [Hdef [Hle [HΓl HΓn]]]]].
  pose proof (ext_context_typing_wf_sum_l _ _ _ _ _ _ Hwf) as Hwf_l.
  pose proof (ext_context_typing_wf_sum_r _ _ _ _ _ _ Hwf) as Hwf_nm.
  pose proof (ext_tree_match_leaf_world Σ Γl x eleaf root left right enode τl ml
    Hwf_l HΓl (Heq_l ml HΓl) (Hl ml HΓl)) as Hmatch_l.
  pose proof (ext_tree_match_node_world Σ Γn x eleaf root left right enode τn mn
    H01 H02 H12 Hwf_nm Hwf_eq Hwf_c HΓn (Heq_n mn HΓn) (Hn mn HΓn)) as Hmatch_n.
  fold em in Hmatch_l, Hmatch_n.
  unfold ty_denote_under, ty_denote in Hmatch_l, Hmatch_n |- *.
  rewrite <- (ty_denote_gas_saturate
      (cty_depth (CTSum τl τn))
      (atom_env_to_lty_env (erase_ctx Γl)) τl em) in Hmatch_l
    by (cbn [cty_depth]; lia).
  rewrite <- (ty_denote_gas_saturate
      (cty_depth (CTSum τl τn))
      (atom_env_to_lty_env (erase_ctx Γn)) τn em) in Hmatch_n
    by (cbn [cty_depth]; lia).
  replace (atom_env_to_lty_env (erase_ctx Γn))
    with (atom_env_to_lty_env (erase_ctx Γl)) in Hmatch_n
    by (rewrite Herase_ctx; reflexivity).
  assert (Htotal_l : ml ⊨ expr_total_formula em).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_l) as Hguard.
    repeat rewrite res_models_and_iff in Hguard. tauto.
  }
  assert (Htotal_n : mn ⊨ expr_total_formula em).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_n) as Hguard.
    repeat rewrite res_models_and_iff in Hguard. tauto.
  }
  assert (Htotal_m : m ⊨ expr_total_formula em).
  {
    eapply res_models_kripke; [exact Hle| ].
    eapply expr_total_formula_sum_intro; eauto.
  }
  assert (Hstatic :
      m ⊨ ty_static_guard_formula
        (atom_env_to_lty_env (erase_ctx (CtxSum Γl Γn)))
        (CTSum τl τn) em).
  { exact (context_typing_wf_denot_static_guard_full
      Σ (CtxSum Γl Γn) (CTSum τl τn) em m Hwf Hctx). }
  replace (atom_env_to_lty_env (erase_ctx (CtxSum Γl Γn)))
    with (atom_env_to_lty_env (erase_ctx Γl)) in Hstatic |- *
    by (cbn [erase_ctx]; reflexivity).
  eapply ty_denote_gas_sum_intro_from_branch_refinement
    with (m1 := ml) (m2 := mn) (Hdef := Hdef).
  - exact Hle.
  - exact Herase_ty.
  - cbn [cty_depth]. lia.
  - cbn [cty_depth]. lia.
  - exact Hstatic.
  - exact Htotal_m.
  - exact Hmatch_l.
  - exact Hmatch_n.
Qed.


(** Rule-shaped corollaries: the distinctness side conditions on the
    pattern variables that follow from the basic typing of the pattern
    premise are discharged. *)

Lemma ext_tcons_wf_distinct Σ Γ hd tl τ :
  context_typing_wf Σ Γ (tcons (vfvar hd) (vfvar tl)) τ -> hd <> tl.
Proof.
  intros Hwf ->.
  destruct (ext_tcons_fvar_typing_inv _ _ _ _
    (context_typing_wf_basic_typing _ _ _ _ Hwf)) as [H1 H2].
  rewrite H1 in H2. discriminate.
Qed.

Lemma ext_tnode_wf_distinct Σ Γ root left right τ :
  context_typing_wf Σ Γ (tnode (vfvar root) (vfvar left) (vfvar right)) τ ->
  root <> left /\ root <> right.
Proof.
  intros Hwf.
  destruct (ext_tnode_fvar_typing_inv _ _ _ _ _
    (context_typing_wf_basic_typing _ _ _ _ Hwf)) as [H1 [H2 H3]].
  split; intros ->; congruence.
Qed.

Lemma ext_list_match_cons_paper_rule_sound Σ Γ x enil hd tl econs τ :
  context_typing_wf Σ Γ (match_list_named (vfvar x) enil hd tl econs) τ ->
  context_typing_wf Σ Γ (tcons (vfvar hd) (vfvar tl)) (list_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γ econs τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (list_match_eq_ty (vfvar x)) (tcons (vfvar hd) (vfvar tl))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ econs) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (match_list_named (vfvar x) enil hd tl econs).
Proof.
  intros Hwf_m Hwf_eq. apply ext_list_match_cons_paper_sound; auto.
  exact (ext_tcons_wf_distinct _ _ _ _ _ Hwf_eq).
Qed.

Lemma ext_list_match_both_paper_rule_sound Σ Γn Γc x enil hd tl econs τn τc :
  context_typing_wf Σ (CtxSum Γn Γc)
    (match_list_named (vfvar x) enil hd tl econs) (CTSum τn τc) ->
  context_typing_wf Σ Γc (tcons (vfvar hd) (vfvar tl)) (list_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γc econs τc ->
  (ctx_denote_under Σ Γn ⊫
    ty_denote_under Σ Γn (list_match_eq_ty (vfvar x)) (tret (vconst (clist [])))) ->
  (ctx_denote_under Σ Γc ⊫
    ty_denote_under Σ Γc (list_match_eq_ty (vfvar x)) (tcons (vfvar hd) (vfvar tl))) ->
  (ctx_denote_under Σ Γn ⊫ ty_denote_under Σ Γn τn enil) ->
  (ctx_denote_under Σ Γc ⊫ ty_denote_under Σ Γc τc econs) ->
  ctx_denote_under Σ (CtxSum Γn Γc) ⊫
    ty_denote_under Σ (CtxSum Γn Γc) (CTSum τn τc)
      (match_list_named (vfvar x) enil hd tl econs).
Proof.
  intros Hwf Hwf_eq. apply ext_list_match_both_paper_sound; auto.
  exact (ext_tcons_wf_distinct _ _ _ _ _ Hwf_eq).
Qed.

Lemma ext_tree_match_node_paper_rule_sound Σ Γ x eleaf root left right enode τ :
  left <> right ->
  context_typing_wf Σ Γ (match_tree_named (vfvar x) eleaf root left right enode) τ ->
  context_typing_wf Σ Γ (tnode (vfvar root) (vfvar left) (vfvar right))
    (tree_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γ enode τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (tree_match_eq_ty (vfvar x))
      (tnode (vfvar root) (vfvar left) (vfvar right))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ enode) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (match_tree_named (vfvar x) eleaf root left right enode).
Proof.
  intros H12 Hwf_m Hwf_eq.
  destruct (ext_tnode_wf_distinct _ _ _ _ _ _ Hwf_eq) as [H01 H02].
  apply ext_tree_match_node_paper_sound; auto.
Qed.

Lemma ext_tree_match_both_paper_rule_sound Σ Γl Γn x eleaf root left right enode τl τn :
  left <> right ->
  context_typing_wf Σ (CtxSum Γl Γn)
    (match_tree_named (vfvar x) eleaf root left right enode) (CTSum τl τn) ->
  context_typing_wf Σ Γn (tnode (vfvar root) (vfvar left) (vfvar right))
    (tree_match_eq_ty (vfvar x)) ->
  context_typing_wf Σ Γn enode τn ->
  (ctx_denote_under Σ Γl ⊫
    ty_denote_under Σ Γl (tree_match_eq_ty (vfvar x)) (tret (vconst (ctree tr_leaf)))) ->
  (ctx_denote_under Σ Γn ⊫
    ty_denote_under Σ Γn (tree_match_eq_ty (vfvar x))
      (tnode (vfvar root) (vfvar left) (vfvar right))) ->
  (ctx_denote_under Σ Γl ⊫ ty_denote_under Σ Γl τl eleaf) ->
  (ctx_denote_under Σ Γn ⊫ ty_denote_under Σ Γn τn enode) ->
  ctx_denote_under Σ (CtxSum Γl Γn) ⊫
    ty_denote_under Σ (CtxSum Γl Γn) (CTSum τl τn)
      (match_tree_named (vfvar x) eleaf root left right enode).
Proof.
  intros H12 Hwf Hwf_eq.
  destruct (ext_tnode_wf_distinct _ _ _ _ _ _ Hwf_eq) as [H01 H02].
  apply ext_tree_match_both_paper_sound; auto.
Qed.

(** ** The named match rules of [ExtendedTyping] are unsound as stated *)

Import ListNotations.
Open Scope core_scope.
Open Scope case_scope.
Open Scope cty_scope.
Open Scope ctx_scope.

Definition q_never : type_qualifier := tqual ∅ (fun _ => False).

Lemma ty_denote_gas_over_never_false gas (Σ : lty_env) b e (m : WfWorldT) :
  m ⊨ ty_denote_gas (S gas) Σ (CTOver b q_never) e -> False.
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard_formula _ _ _ _ _ Hden) as Hguard.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hforall].
  destruct (res_models_forall_rev _ _ Hforall) as [L HL].
  set (y := fresh_for (L ∪ world_dom (m : WorldT) ∪ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTOver b q_never) e)))).
  pose proof (fresh_for_not_in (L ∪ world_dom (m : WorldT) ∪ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTOver b q_never) e)))) as Hy.
  fold y in Hy.
  destruct (ext_result_world_exists _ _ _ m y Hguard ltac:(set_solver))
    as [my [Hdom [Hres [Hmy _]]]].
  pose proof (HL y ltac:(set_solver) my Hdom Hres) as Hopen.
  destruct (ty_guard_lc_parts _ _ _ _ Hguard) as [HlcD Hlc].
  rewrite formula_open_impl in Hopen.
  rewrite ext_open_result_shift0 in Hopen by first [exact HlcD | exact Hlc | set_solver].
  pose proof (res_models_impl_elim _ _ _ Hopen Hmy) as Hfib.
  cbn [formula_open q_never qual_vars] in Hfib.
  replace (set_swap (LVBound 0) (LVFree y) (qual_lvars q_never ∖ {[LVBound 0]}))
    with (∅ : lvset) in Hfib.
  2:{ unfold q_never. cbn [qual_lvars].
      replace ((∅ : lvset) ∖ {[LVBound 0]}) with (∅ : lvset) by set_solver.
      symmetry. apply set_swap_empty. }
  apply res_models_fibvars_empty_elim in Hfib.
  destruct (world_wf my) as [[σ Hσ] _].
  pose proof (res_models_over_FAtom_store_holds _ _ Hfib σ Hσ) as Hholds.
  unfold q_never in Hholds. cbn [qual_open_atom qualifier_holds_store] in Hholds.
  destruct Hholds as [_ [_ []]].
Qed.

Definition NatNever : context_ty := over_ty TNat q_never.
Definition cex_hd : atom := 9001%positive.
Definition cex_tl : atom := 9002%positive.
Definition cex_pat : ctx := (cex_hd ∷ NatNever) ,, (cex_tl ∷ OList).
Definition cex_ctx : ctx := Emp ,, cex_pat.
Definition cex_match : tm :=
  match_list_named (vlist [1%nat]) (ret (vnat 0)) cex_hd cex_tl (ret (vnat 0)).

Lemma cex_match_wf : ∅; Emp ⊢wf cex_match ⋮ NatNever.
Proof. unfold cex_match, NatNever, q_never. extended_wf. Qed.

Lemma cex_ctx_unmodelable : entails (ctx_denote_under ∅ cex_ctx) FFalse.
Proof.
  intros m Hctx. exfalso.
  unfold cex_ctx, cex_pat in Hctx.
  cbn [ctx_denote_under] in Hctx.
  rewrite !res_models_and_iff in Hctx.
  repeat match goal with H : _ ∧ _ |- _ => destruct H end.
  match goal with
  | H : m ⊨ ty_denote _ NatNever _ |- _ =>
      unfold ty_denote, NatNever, over_ty in H; cbn [cty_depth] in H;
      exact (ty_denote_gas_over_never_false 0 _ _ _ m H)
  end.
Qed.

Lemma ctx_sub_vacuous Σ X Γ1 Γ2 :
  wf_ctx_under Σ Γ1 ->
  wf_ctx_under Σ Γ2 ->
  ty_env_agree_on X (erase_ctx Γ1) (erase_ctx Γ2) ->
  entails (ctx_denote_under Σ Γ1) FFalse ->
  ctx_sub_under Σ X Γ1 Γ2.
Proof.
  intros H1 H2 Hagree Hfalse.
  split; [exact H1| ]. split; [exact H2| ]. split; [exact Hagree| ].
  intros r Hr. exfalso.
  pose proof (Hfalse r Hr) as Hf.
  unfold res_models in Hf. cbn in Hf. tauto.
Qed.

Lemma cex_hd_tl_neq : cex_hd ≠ cex_tl.
Proof. unfold cex_hd, cex_tl. discriminate. Qed.

(** The previous (unsound) shape of [EXT_ListMatchConsOnlyNamed]: premises
    under [Γ ,, Γpat], conclusion at [Γ].  It is no longer a constructor of
    [has_extended_context_type]; the counterexample below shows that adding
    it as a rule would derive a semantically false judgment. *)
Definition old_list_match_cons_rule : Prop :=
  forall Σ Γ Γpat v τ enil hd tl econs,
    ctx_dom Γpat = {[hd]} ∪ {[tl]} ->
    Σ; Γ ⊢wf match_list_named v enil hd tl econs ⋮ τ ->
    Σ; (Γ ,, Γpat) ⊢ₓ (avar hd ::ᵗ avar tl) ⋮ (list_match_eq_ty v) ->
    Σ; (Γ ,, Γpat) ⊢ₓ econs ⋮ τ ->
    Σ; Γ ⊢ₓ match_list_named v enil hd tl econs ⋮ τ.

Lemma cex_derivation :
  old_list_match_cons_rule -> ∅; Emp ⊢ₓ cex_match ⋮ NatNever.
Proof.
  intros Hold.
  unfold cex_match.
  eapply (Hold _ _ cex_pat).
  - reflexivity.
  - exact cex_match_wf.
  - eapply EXT_Sub with (τ1 := list_cons_precise_ty (avar cex_hd) (avar cex_tl)).
    + unfold cex_pat, NatNever, q_never. extended_wf.
    + eapply EXT_ListCons.
      * unfold cex_pat, NatNever, q_never. extended_wf.
      * eapply EXT_CtxSub with (Γ2 := cex_hd ∷ ONat).
        -- unfold cex_pat, NatNever, q_never. extended_wf.
        -- eapply EXT_Var. extended_wf.
        -- apply ctx_sub_vacuous.
           ++ unfold cex_pat, NatNever, q_never. extended_wf_ctx.
              all: assert (Hn := cex_hd_tl_neq); set_solver.
           ++ extended_wf_ctx.
           ++ intros a Ha.
              pose proof (basic_context_ty_fv_subset _ _ basic_context_ty_ONat_empty) as HfvO.
              assert (a = cex_hd) as -> by (cbn in Ha; set_solver).
              vm_compute. reflexivity.
           ++ exact cex_ctx_unmodelable.
      * eapply EXT_CtxSub with (Γ2 := cex_tl ∷ OList).
        -- unfold cex_pat, NatNever, q_never. extended_wf.
        -- eapply EXT_Var. extended_wf.
        -- apply ctx_sub_vacuous.
           ++ unfold cex_pat, NatNever, q_never. extended_wf_ctx.
              all: assert (Hn := cex_hd_tl_neq); set_solver.
           ++ extended_wf_ctx.
           ++ intros a Ha.
              pose proof (basic_context_ty_fv_subset _ _ basic_context_ty_OList_empty) as HfvO.
              assert (a = cex_tl) as -> by (cbn in Ha; set_solver).
              vm_compute. reflexivity.
           ++ exact cex_ctx_unmodelable.
    + apply subtype_vacuous_of_unmodelable_ctx.
      * unfold cex_pat, NatNever, q_never. extended_wf_ctx.
        all: assert (Hn := cex_hd_tl_neq); set_solver.
      * extended_wf.
      * extended_wf.
      * reflexivity.
      * exact cex_ctx_unmodelable.
  - eapply EXT_Sub with (τ1 := const_precise_ty (cnat 0)).
    + unfold cex_pat, NatNever, q_never. extended_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp).
      * unfold cex_pat, NatNever, q_never. extended_wf.
      * eapply EXT_Const. extended_wf.
      * apply ctx_sub_vacuous.
        -- unfold cex_pat, NatNever, q_never. extended_wf_ctx.
           all: assert (Hn := cex_hd_tl_neq); set_solver.
        -- extended_wf_ctx.
        -- intros a Ha.
           assert (Hfv0 : fv_cty (const_precise_ty (cnat 0)) ⊆ ∅).
           { apply (wf_context_ty_at_fv_subset 0 ∅). extended_wf_type. }
           exfalso. cbn in Ha. set_solver.
        -- exact cex_ctx_unmodelable.
    + apply subtype_vacuous_of_unmodelable_ctx.
      * unfold cex_pat, NatNever, q_never. extended_wf_ctx.
        all: assert (Hn := cex_hd_tl_neq); set_solver.
      * extended_wf.
      * unfold NatNever, q_never. extended_wf.
      * reflexivity.
      * exact cex_ctx_unmodelable.
Qed.

(** The conclusion is semantically false: the empty context is modeled by
    the unit world, but no world models [e ⋮ {ν:nat | False}]. *)
Lemma cex_conclusion_false :
  ~ (ctx_denote_under ∅ Emp ⊫ ty_denote_under ∅ Emp NatNever cex_match).
Proof.
  intros Hsem.
  assert (Hctx : res_unit ⊨ ctx_denote_under ∅ Emp).
  {
    cbn [ctx_denote_under store_restrict ctx_fv].
    rewrite res_models_and_iff. split.
    - apply basic_world_formula_empty.
    - apply res_models_true.
  }
  pose proof (Hsem res_unit Hctx) as Hden.
  unfold ty_denote_under, ty_denote, NatNever, over_ty in Hden.
  cbn [cty_depth] in Hden.
  exact (ty_denote_gas_over_never_false 0 _ _ _ _ Hden).
Qed.

Theorem ext_list_match_cons_only_named_unsound :
  old_list_match_cons_rule ->
  has_extended_context_type ∅ Emp cex_match NatNever /\
  ~ (ctx_denote_under ∅ Emp ⊫ ty_denote_under ∅ Emp NatNever cex_match).
Proof. intros Hold. split; [exact (cex_derivation Hold) | exact cex_conclusion_false]. Qed.

(** * T-FixUnroll at every target type ([-∗], [⊕], [□] included)

    [ext_fix_unroll_named_sound] above covers the targets in
    [fix_unroll_shape] (→, base, ⊓, ∪).  Here the remaining connectives are
    handled by a world-level value transport: the fix value [fx] and its
    one-step unfolding [unf] are applicatively equivalent
    ([ext_fix_unroll_tm_equiv]) and have the same free variables, so in a
    world whose result column [z] holds the instantiated [unf] one may swap
    that column to the instantiated [fx] ([ext_swapc]) and keep every
    type denotation of [ret z] / [z y].  The induction over the target type
    is [ext_vt_main]; the per-connective column swaps are
    [ext_vt_sum_body] (⊕, via pullback of the two summands),
    [ext_vt_persist_body] (□, via injectivity of closed instantiation
    [ext_inst_inj]), [ext_vt_arrow_body] (→) and [ext_vt_wand_body] (-∗,
    via products with the swapped world).  The final statement is
    [ext_fix_unroll_named_sound_ext]; its shape premise
    [fix_unroll_shape_ext] holds for every type
    ([fix_unroll_shape_ext_all]). *)

From Denotation Require Import TypeEquivFiberTransport.

(** ** Swapping the value column of a result variable *)

Local Notation ext_ins z a σ :=
  (@insert atom value (gmap atom value) (@map_insert atom value (gmap atom value) (@gmap_partial_alter atom _ _ value)) z a σ)
  (only parsing).

Lemma ext_restrict_lookup (σ : StoreT) (X : aset) a :
  (store_restrict σ X : StoreT) !! a = if decide (a ∈ X) then σ !! a else None.
Proof. apply storeA_restrict_lookup. Qed.

Definition ext_inst (v : value) (σ : StoreT) : value :=
  m{store_restrict σ (fv_value v)} v.

Definition ext_swapc_raw (w : WorldT) (z : atom) (v : value) : WorldT :=
  mk_worldA (world_dom w ∪ {[z]})
    (fun σ => exists σ0, (w : WorldT) σ0 /\
       σ = ext_ins z (ext_inst v σ0) σ0).

Lemma ext_swapc_wf (w : WfWorldT) z v : wf_world (ext_swapc_raw w z v).
Proof.
  destruct (world_wf w) as [[σ Hσ] Hdom]. split.
  - exists (ext_ins z (ext_inst v σ) σ). exists σ. split; [exact Hσ|reflexivity].
  - intros σ' [σ0 [Hσ0 ->]]. cbn. rewrite dom_insert_L.
    change (dom σ0) with (dom (σ0 : StoreT)).
    rewrite (Hdom σ0 Hσ0). set_solver.
Qed.

Definition ext_swapc (w : WfWorldT) (z : atom) (v : value) : WfWorldT :=
  exist _ (ext_swapc_raw w z v) (ext_swapc_wf w z v).

Lemma ext_swapc_dom w z v :
  world_dom (ext_swapc w z v : WorldT) = world_dom (w : WorldT) ∪ {[z]}.
Proof. reflexivity. Qed.

Lemma ext_swapc_stores w z v σ :
  (ext_swapc w z v : WorldT) σ <->
  exists σ0, (w : WorldT) σ0 /\ σ = ext_ins z (ext_inst v σ0) σ0.
Proof. reflexivity. Qed.

Lemma ext_inst_restrict v σ X :
  fv_value v ⊆ X -> ext_inst v (store_restrict σ X) = ext_inst v σ.
Proof.
  intros HX. unfold ext_inst. rewrite storeA_restrict_restrict.
  replace (X ∩ fv_value v) with (fv_value v) by set_solver. reflexivity.
Qed.

Lemma ext_inst_insert_fresh v σ z a :
  z ∉ fv_value v -> ext_inst v (ext_ins z a σ) = ext_inst v σ.
Proof.
  intros Hz. unfold ext_inst. rewrite storeA_restrict_insert_notin by exact Hz.
  reflexivity.
Qed.

Lemma ext_world_eq (w1 w2 : WfWorldT) :
  world_dom (w1 : WorldT) = world_dom (w2 : WorldT) ->
  (forall σ, (w1 : WorldT) σ <-> (w2 : WorldT) σ) ->
  w1 = w2.
Proof.
  intros Hdom Hst. apply wfworldA_ext. apply worldA_ext; assumption.
Qed.

Lemma ext_swapc_restrict_off (w : WfWorldT) z v X :
  z ∉ X ->
  res_restrict (ext_swapc w z v) X = res_restrict w X.
Proof.
  intros HzX. apply ext_world_eq.
  - rewrite !res_restrict_dom, ext_swapc_dom. set_solver.
  - intros σ. cbn. split.
    + intros [σ1 [[σ0 [Hσ0 ->]] <-]]. exists σ0. split; [exact Hσ0| ].
      rewrite storeA_restrict_insert_notin by exact HzX. reflexivity.
    + intros [σ0 [Hσ0 <-]]. exists (ext_ins z (ext_inst v σ0) σ0). split.
      * exists σ0. split; [exact Hσ0|reflexivity].
      * rewrite storeA_restrict_insert_notin by exact HzX. reflexivity.
Qed.

Lemma ext_swapc_restrict_on (w : WfWorldT) z v X :
  z ∈ X -> fv_value v ⊆ X ->
  res_restrict (ext_swapc w z v) X = ext_swapc (res_restrict w X) z v.
Proof.
  intros HzX HvX. apply ext_world_eq.
  - rewrite !res_restrict_dom, !ext_swapc_dom, res_restrict_dom. set_solver.
  - intros σ. cbn. split.
    + intros [σ1 [[σ0 [Hσ0 ->]] <-]].
      exists (store_restrict σ0 X). split; [exists σ0; split; [exact Hσ0|reflexivity]| ].
      rewrite storeA_restrict_insert_in by exact HzX.
      rewrite ext_inst_restrict by exact HvX. reflexivity.
    + intros [σ0' [[σ0 [Hσ0 <-]] ->]].
      exists (ext_ins z (ext_inst v σ0) σ0). split.
      * exists σ0. split; [exact Hσ0|reflexivity].
      * rewrite storeA_restrict_insert_in by exact HzX.
        rewrite ext_inst_restrict by exact HvX. reflexivity.
Qed.

Lemma ext_swapc_idem (w : WfWorldT) z v1 v2 :
  z ∉ fv_value v2 ->
  ext_swapc (ext_swapc w z v1) z v2 = ext_swapc w z v2.
Proof.
  intros Hz. apply ext_world_eq.
  - rewrite !ext_swapc_dom. set_solver.
  - intros σ. cbn. split.
    + intros [σ1 [[σ0 [Hσ0 ->]] ->]]. exists σ0. split; [exact Hσ0| ].
      rewrite ext_inst_insert_fresh by exact Hz. rewrite insert_insert_eq. reflexivity.
    + intros [σ0 [Hσ0 ->]]. exists (ext_ins z (ext_inst v1 σ0) σ0). split.
      * exists σ0. split; [exact Hσ0|reflexivity].
      * rewrite ext_inst_insert_fresh by exact Hz. rewrite insert_insert_eq. reflexivity.
Qed.

Lemma ext_swapc_lookup (w : WfWorldT) z v σ :
  z ∉ fv_value v ->
  (ext_swapc w z v : WorldT) σ -> σ !! z = Some (ext_inst v σ).
Proof.
  intros Hz [σ0 [_ ->]]. rewrite ext_inst_insert_fresh by exact Hz.
  apply lookup_insert_eq.
Qed.

(** A world whose [z] column is the instantiated [v] is a swap of its
    [z]-free part. *)
Lemma ext_swapc_self_restrict (w : WfWorldT) z v :
  z ∈ world_dom (w : WorldT) ->
  z ∉ fv_value v ->
  fv_value v ⊆ world_dom (w : WorldT) ->
  (forall σ, (w : WorldT) σ -> σ !! z = Some (ext_inst v σ)) ->
  w = ext_swapc (res_restrict w (world_dom (w : WorldT) ∖ {[z]})) z v.
Proof.
  intros Hzw Hzv Hvw Hlook. apply ext_world_eq.
  - rewrite ext_swapc_dom, res_restrict_dom.
    apply set_eq. intros a. destruct (decide (a = z)); set_solver.
  - intros σ. cbn. split.
    + intros Hσ. exists (store_restrict σ (world_dom (w : WorldT) ∖ {[z]})).
      split; [exists σ; split; [exact Hσ|reflexivity]| ].
      rewrite ext_inst_restrict by set_solver.
      apply map_eq. intros a. destruct (decide (a = z)) as [->|Haz].
      * rewrite lookup_insert_eq. apply Hlook. exact Hσ.
      * rewrite lookup_insert_ne by congruence.
        rewrite ext_restrict_lookup.
        destruct (decide (a ∈ world_dom (w : WorldT) ∖ {[z]})) as [Ha|Ha]; [reflexivity| ].
        apply not_elem_of_dom.
        rewrite (wfworld_store_dom w σ Hσ). set_solver.
    + intros [σ0 [[σ1 [Hσ1 <-]] ->]].
      rewrite ext_inst_restrict by set_solver.
      replace (ext_ins z (ext_inst v σ1) (store_restrict σ1 (world_dom (w : WorldT) ∖ {[z]})))
        with σ1; [exact Hσ1| ].
      apply map_eq. intros a. destruct (decide (a = z)) as [->|Haz].
      * rewrite lookup_insert_eq. apply Hlook. exact Hσ1.
      * rewrite lookup_insert_ne by congruence.
        rewrite ext_restrict_lookup.
        destruct (decide (a ∈ world_dom (w : WorldT) ∖ {[z]})) as [Ha|Ha]; [reflexivity| ].
        apply not_elem_of_dom.
        rewrite (wfworld_store_dom w σ1 Hσ1). set_solver.
Qed.

Lemma ext_sum_stores (w1 w2 : WfWorldT) Hdef σ :
  (res_sum w1 w2 Hdef : WorldT) σ <-> (w1 : WorldT) σ \/ (w2 : WorldT) σ.
Proof. reflexivity. Qed.

Lemma ext_sum_dom (w1 w2 : WfWorldT) Hdef :
  world_dom (res_sum w1 w2 Hdef : WorldT) = world_dom (w1 : WorldT).
Proof. reflexivity. Qed.

Lemma ext_restrict_stores (w : WfWorldT) X σ :
  (res_restrict w X : WorldT) σ <->
  exists σ0, (w : WorldT) σ0 /\ store_restrict σ0 X = σ.
Proof. reflexivity. Qed.

Lemma ext_product_stores (w1 w2 : WfWorldT) Hc σ :
  (res_product w1 w2 Hc : WorldT) σ <->
  exists σ1 σ2, (w1 : WorldT) σ1 /\ (w2 : WorldT) σ2 /\ storeA_compat σ1 σ2 /\
    σ = σ1 ∪ σ2.
Proof. reflexivity. Qed.

Lemma ext_swapc_sum_defined (w1 w2 : WfWorldT) z v :
  raw_sum_defined (w1 : WorldT) (w2 : WorldT) ->
  raw_sum_defined (ext_swapc w1 z v : WorldT) (ext_swapc w2 z v : WorldT).
Proof.
  unfold raw_sum_defined, rawA_sum_defined. intros H.
  change (world_dom (ext_swapc w1 z v : WorldT) = world_dom (ext_swapc w2 z v : WorldT)).
  rewrite !ext_swapc_dom. change (world_dom (w1 : WorldT) = world_dom (w2 : WorldT)) in H.
  rewrite H. reflexivity.
Qed.

Lemma ext_swapc_sum (w1 w2 : WfWorldT) z v Hdef Hdef' :
  res_sum (ext_swapc w1 z v) (ext_swapc w2 z v) Hdef' =
  ext_swapc (res_sum w1 w2 Hdef) z v.
Proof.
  apply ext_world_eq.
  - rewrite ext_sum_dom, !ext_swapc_dom. reflexivity.
  - intros σ. rewrite ext_sum_stores, !ext_swapc_stores. split.
    + intros [[σ0 [H ->]]|[σ0 [H ->]]]; exists σ0; split; try reflexivity;
        apply ext_sum_stores; auto.
    + intros [σ0 [H ->]]. apply ext_sum_stores in H as [H|H]; [left|right];
        exists σ0; split; auto.
Qed.

Lemma ext_restrict_sum_defined (w1 w2 : WfWorldT) X :
  raw_sum_defined (w1 : WorldT) (w2 : WorldT) ->
  raw_sum_defined (res_restrict w1 X : WorldT) (res_restrict w2 X : WorldT).
Proof.
  unfold raw_sum_defined, rawA_sum_defined. intros H.
  change (world_dom (res_restrict w1 X : WorldT) = world_dom (res_restrict w2 X : WorldT)).
  rewrite !res_restrict_dom. change (world_dom (w1 : WorldT) = world_dom (w2 : WorldT)) in H.
  rewrite H. reflexivity.
Qed.

Lemma ext_restrict_sum (w1 w2 : WfWorldT) X Hdef Hdef' :
  res_restrict (res_sum w1 w2 Hdef) X =
  res_sum (res_restrict w1 X) (res_restrict w2 X) Hdef'.
Proof.
  apply ext_world_eq.
  - rewrite ext_sum_dom, !res_restrict_dom, ext_sum_dom. reflexivity.
  - intros σ. rewrite ext_sum_stores, !ext_restrict_stores. split.
    + intros [σ0 [H <-]]. apply ext_sum_stores in H as [H|H]; [left|right];
        apply ext_restrict_stores; eauto.
    + intros [H|H]; apply ext_restrict_stores in H as [σ0 [H <-]];
        exists σ0; split; auto; apply ext_sum_stores; auto.
Qed.

Lemma ext_swapc_subset (q w : WfWorldT) z v :
  res_subset q (ext_swapc w z v) ->
  z ∉ fv_value v ->
  fv_value v ⊆ world_dom (w : WorldT) ->
  q = ext_swapc (res_restrict q (world_dom (q : WorldT) ∖ {[z]})) z v.
Proof.
  intros [Hdom Hsub] Hz Hv.
  change (world_dom (q : WorldT) = world_dom (ext_swapc w z v : WorldT)) in Hdom.
  apply ext_swapc_self_restrict.
  - rewrite Hdom, ext_swapc_dom. set_solver.
  - exact Hz.
  - rewrite Hdom, ext_swapc_dom. set_solver.
  - intros σ Hσ. apply (ext_swapc_lookup w z v σ Hz). apply Hsub. exact Hσ.
Qed.

Lemma ext_union_lookup_l (σ1 σ2 : StoreT) a u :
  σ1 !! a = Some u -> (σ1 ∪ σ2 : StoreT) !! a = Some u.
Proof. apply lookup_union_Some_l. Qed.

Lemma ext_union_lookup_r (σ1 σ2 : StoreT) a :
  σ1 !! a = None -> (σ1 ∪ σ2 : StoreT) !! a = σ2 !! a.
Proof. apply lookup_union_r. Qed.

Lemma ext_union_lookup (σ1 σ2 : StoreT) a :
  (σ1 ∪ σ2 : StoreT) !! a = match σ1 !! a with Some u => Some u | None => σ2 !! a end.
Proof.
  destruct (σ1 !! a) eqn:H.
  - apply ext_union_lookup_l. exact H.
  - apply ext_union_lookup_r. exact H.
Qed.

Lemma ext_restrict_union_r (σ1 σ2 : StoreT) X :
  storeA_compat σ1 σ2 -> X ⊆ dom σ2 ->
  store_restrict (σ1 ∪ σ2) X = store_restrict σ2 X.
Proof.
  intros Hc HX. apply map_eq. intros a.
  rewrite !ext_restrict_lookup.
  destruct (decide (a ∈ X)) as [Ha|Ha]; [ |reflexivity].
  assert (Ha2 : a ∈ dom σ2) by set_solver.
  apply elem_of_dom in Ha2 as [u2 Hu2].
  rewrite Hu2.
  destruct (σ1 !! a) as [u1| ] eqn:Hu1.
  - rewrite (ext_union_lookup_l _ _ _ _ Hu1). f_equal. exact (Hc a u1 u2 Hu1 Hu2).
  - rewrite (ext_union_lookup_r _ _ _ Hu1). exact Hu2.
Qed.

Lemma ext_insert_lookup_eq (σ : StoreT) z a :
  (ext_ins z a σ : StoreT) !! z = Some a.
Proof. apply lookup_insert_eq. Qed.

Lemma ext_insert_lookup_ne (σ : StoreT) z a b :
  b <> z -> (ext_ins z a σ : StoreT) !! b = σ !! b.
Proof. intros H. apply lookup_insert_ne. congruence. Qed.

Lemma ext_swapc_compat_restrict (m' w : WfWorldT) z v1 v2 X :
  z ∉ X ->
  world_compat (m' : WorldT) (ext_swapc w z v2 : WorldT) ->
  world_compat (res_restrict m' X : WorldT) (ext_swapc w z v1 : WorldT).
Proof.
  intros HzX Hc σ1 σ2 Hσ1 Hσ2.
  apply ext_restrict_stores in Hσ1 as [σ1' [Hσ1' <-]].
  apply ext_swapc_stores in Hσ2 as [σ0 [Hσ0 ->]].
  assert (Hc0 : storeA_compat σ1' (ext_ins z (ext_inst v2 σ0) σ0)).
  { apply Hc; [exact Hσ1'| ]. apply ext_swapc_stores. eauto. }
  intros a u1 u2 Hu1 Hu2.
  rewrite ext_restrict_lookup in Hu1.
  destruct (decide (a ∈ X)) as [HaX| ]; [ |discriminate].
  assert (Haz : a <> z) by (intros ->; contradiction).
  rewrite ext_insert_lookup_ne in Hu2 by exact Haz.
  apply (Hc0 a u1 u2 Hu1). rewrite ext_insert_lookup_ne by exact Haz. exact Hu2.
Qed.

Lemma ext_swapc_compat_base (m' w : WfWorldT) z v :
  z ∉ world_dom (m' : WorldT) ->
  world_compat (m' : WorldT) (ext_swapc w z v : WorldT) ->
  world_compat (m' : WorldT) (w : WorldT).
Proof.
  intros Hz Hc σ1 σ0 Hσ1 Hσ0 a u1 u2 Hu1 Hu2.
  assert (Haz : a <> z).
  { intros ->. apply Hz. rewrite <- (wfworld_store_dom m' σ1 Hσ1).
    apply elem_of_dom. eauto. }
  apply (Hc σ1 (ext_ins z (ext_inst v σ0) σ0) Hσ1) with (x := a);
    [apply ext_swapc_stores; eauto|exact Hu1| ].
  rewrite ext_insert_lookup_ne by exact Haz. exact Hu2.
Qed.

Lemma ext_swapc_compat_lift (m' w : WfWorldT) z v :
  z ∉ world_dom (m' : WorldT) ->
  world_compat (m' : WorldT) (w : WorldT) ->
  world_compat (m' : WorldT) (ext_swapc w z v : WorldT).
Proof.
  intros Hz Hc σ1 σ2 Hσ1 Hσ2 a u1 u2 Hu1 Hu2.
  apply ext_swapc_stores in Hσ2 as [σ0 [Hσ0 ->]].
  assert (Haz : a <> z).
  { intros ->. apply Hz. rewrite <- (wfworld_store_dom m' σ1 Hσ1).
    apply elem_of_dom. eauto. }
  rewrite ext_insert_lookup_ne in Hu2 by exact Haz.
  exact (Hc σ1 σ0 Hσ1 Hσ0 a u1 u2 Hu1 Hu2).
Qed.

Lemma ext_swapc_product (m'' w : WfWorldT) z v Hc Hc' :
  z ∉ world_dom (m'' : WorldT) ->
  fv_value v ⊆ world_dom (w : WorldT) ->
  res_product m'' (ext_swapc w z v) Hc = ext_swapc (res_product m'' w Hc') z v.
Proof.
  intros Hz Hv. apply ext_world_eq.
  - rewrite res_product_dom, !ext_swapc_dom, res_product_dom. set_solver.
  - assert (Hkey : forall σ1 σ0, (m'' : WorldT) σ1 -> (w : WorldT) σ0 ->
        storeA_compat σ1 σ0 ->
        σ1 ∪ ext_ins z (ext_inst v σ0) σ0 =
        ext_ins z (ext_inst v (σ1 ∪ σ0)) (σ1 ∪ σ0)).
    {
      intros σ1 σ0 Hσ1 Hσ0 Hc0.
      assert (Hf : ext_inst v (σ1 ∪ σ0) = ext_inst v σ0).
      { unfold ext_inst. rewrite ext_restrict_union_r; [reflexivity|exact Hc0| ].
        rewrite (wfworld_store_dom w σ0 Hσ0). exact Hv. }
      rewrite Hf.
      assert (Hz1 : σ1 !! z = None).
      { apply not_elem_of_dom. rewrite (wfworld_store_dom m'' σ1 Hσ1). exact Hz. }
      apply map_eq. intros a. rewrite !ext_union_lookup.
      destruct (decide (a = z)) as [->|Haz].
      - rewrite Hz1, !ext_insert_lookup_eq. reflexivity.
      - rewrite !ext_insert_lookup_ne by exact Haz. rewrite ext_union_lookup. reflexivity.
    }
    intros σ. rewrite ext_product_stores, ext_swapc_stores. split.
    + intros [σ1 [σ2 [Hσ1 [Hσ2 [Hc12 ->]]]]].
      apply ext_swapc_stores in Hσ2 as [σ0 [Hσ0 ->]].
      assert (Hc10 : storeA_compat σ1 σ0) by exact (Hc' σ1 σ0 Hσ1 Hσ0).
      exists (σ1 ∪ σ0). split.
      * apply ext_product_stores. exists σ1, σ0. repeat split; auto.
      * apply Hkey; auto.
    + intros [σ' [Hσ' ->]].
      apply ext_product_stores in Hσ' as [σ1 [σ0 [Hσ1 [Hσ0 [Hc10 ->]]]]].
      exists σ1, (ext_ins z (ext_inst v σ0) σ0). split; [exact Hσ1| ].
      split; [apply ext_swapc_stores; eauto| ].
      split; [apply Hc; [exact Hσ1|apply ext_swapc_stores; eauto]| ].
      symmetry. apply Hkey; auto.
Qed.

Lemma ext_product_absorb_store (σ1 σ2 : StoreT) z :
  storeA_compat σ1 σ2 -> z ∈ dom σ2 ->
  store_restrict σ1 (dom σ1 ∖ {[z]}) ∪ σ2 = σ1 ∪ σ2.
Proof.
  intros Hc Hz. apply elem_of_dom in Hz as [u2 Hu2].
  apply map_eq. intros a. rewrite !ext_union_lookup, ext_restrict_lookup.
  destruct (decide (a ∈ dom σ1 ∖ {[z]})) as [Ha|Ha].
  - reflexivity.
  - destruct (σ1 !! a) as [u1| ] eqn:Hu1; [ |reflexivity].
    assert (a = z).
    { destruct (decide (a = z)); [assumption| ]. exfalso. apply Ha.
      apply elem_of_difference. split; [apply elem_of_dom; eauto|set_solver]. }
    subst a. rewrite Hu2. f_equal. symmetry. exact (Hc z u1 u2 Hu1 Hu2).
Qed.

Lemma ext_product_absorb (m' w : WfWorldT) z v Hc Hc2 :
  z ∈ world_dom (m' : WorldT) ->
  res_product m' (ext_swapc w z v) Hc =
  res_product (res_restrict m' (world_dom (m' : WorldT) ∖ {[z]})) (ext_swapc w z v) Hc2.
Proof.
  intros Hz. apply ext_world_eq.
  - rewrite !res_product_dom, res_restrict_dom, !ext_swapc_dom.
    apply set_eq. intros a. destruct (decide (a = z)); set_solver.
  - intros σ. rewrite !ext_product_stores. split.
    + intros [σ1 [σ2 [Hσ1 [Hσ2 [Hc12 ->]]]]].
      exists (store_restrict σ1 (world_dom (m' : WorldT) ∖ {[z]})), σ2.
      split; [apply ext_restrict_stores; eauto| ]. split; [exact Hσ2| ].
      split; [apply Hc2; [apply ext_restrict_stores; eauto|exact Hσ2]| ].
      rewrite <- (wfworld_store_dom m' σ1 Hσ1).
      symmetry. apply ext_product_absorb_store; [exact Hc12| ].
      rewrite (wfworld_store_dom _ σ2 Hσ2), ext_swapc_dom. set_solver.
    + intros [σ1' [σ2 [Hσ1' [Hσ2 [Hc12 ->]]]]].
      apply ext_restrict_stores in Hσ1' as [σ1 [Hσ1 <-]].
      exists σ1, σ2. split; [exact Hσ1| ]. split; [exact Hσ2| ].
      split; [apply Hc; assumption| ].
      rewrite <- (wfworld_store_dom m' σ1 Hσ1).
      apply ext_product_absorb_store; [apply Hc; assumption| ].
      rewrite (wfworld_store_dom _ σ2 Hσ2), ext_swapc_dom. set_solver.
Qed.

Lemma ext_inst_eval (v : value) (σ : StoreT) :
  store_closed (store_restrict σ (fv_value v)) ->
  lc_value v ->
  tm_eval_in_store σ (tret v) (ext_inst v σ).
Proof.
  intros Hcl Hlc.
  apply (proj1 (tm_eval_in_store_restrict_fv_subset σ (tret v) _ (fv_value v)
    ltac:(cbn [fv_tm]; set_solver))).
  apply tm_eval_in_store_ret_value; assumption.
Qed.

Lemma ext_inst_eval_inv (v : value) (σ : StoreT) u :
  store_closed (store_restrict σ (fv_value v)) ->
  lc_value v ->
  tm_eval_in_store σ (tret v) u -> u = ext_inst v σ.
Proof.
  intros Hcl Hlc Hev.
  apply (proj2 (tm_eval_in_store_restrict_fv_subset σ (tret v) _ (fv_value v)
    ltac:(cbn [fv_tm]; set_solver))) in Hev.
  exact (tm_eval_in_store_ret_value_inv _ v u Hcl Hlc Hev).
Qed.

Lemma ext_lvars_ret_value v :
  lc_value v -> tm_lvars (tret v) = lvars_of_atoms (fv_value v).
Proof.
  intros Hlc. rewrite tm_lvars_lc_eq_atoms by (constructor; exact Hlc).
  reflexivity.
Qed.

Lemma ext_swapc_result (w : WfWorldT) z v :
  z ∉ fv_value v ->
  fv_value v ⊆ world_dom (w : WorldT) ->
  lc_value v ->
  wfworld_closed_on (fv_value v) w ->
  ext_swapc w z v ⊨ expr_result_formula (tret v) (LVFree z).
Proof.
  intros Hzv Hvw Hlc Hcl.
  assert (Hzl : LVFree z ∉ tm_lvars (tret v)).
  { rewrite ext_lvars_ret_value by exact Hlc. unfold lvars_of_atoms.
    rewrite elem_of_map. intros [a [Ha Hin]]. inversion Ha. subst. contradiction. }
  assert (Hcl' : forall σ, (ext_swapc w z v : WorldT) σ ->
      store_closed (store_restrict σ (fv_value v)) /\ σ !! z = Some (ext_inst v σ)).
  {
    intros σ Hσ. split; [ |exact (ext_swapc_lookup w z v σ Hzv Hσ)].
    pose proof Hσ as [σ0 [Hσ0 ->]].
    rewrite storeA_restrict_insert_notin by exact Hzv.
    exact (Hcl σ0 Hσ0).
  }
  apply expr_result_atom_world_to_formula.
  - split; [exact Hzl| ]. split.
    + rewrite res_lift_free_dom, ext_swapc_dom, ext_lvars_ret_value by exact Hlc.
      intros lv Hlv. unfold lvars_of_atoms in *. apply elem_of_map.
      apply elem_of_union in Hlv as [Hlv|Hlv].
      * apply elem_of_map in Hlv as [a [-> Ha]]. exists a. split; [reflexivity|set_solver].
      * apply elem_of_singleton in Hlv as ->. exists z. split; [reflexivity|set_solver].
    + intros τ [σ [Hσ ->]]. split; [exact Hzl| ].
      destruct (Hcl' σ Hσ) as [Hc Hz].
      exists (ext_inst v σ). split.
      * rewrite lstore_lift_free_lookup_free. exact Hz.
      * change (tm_eval_in_store σ (tret v) (ext_inst v σ)).
        apply ext_inst_eval; assumption.
  - intros y σ u Hy Hσ Hev. inversion Hy. subst y.
    destruct (Hcl' σ Hσ) as [Hc Hz].
    exists σ. split; [exact Hσ| ]. split; [reflexivity| ].
    rewrite Hz. f_equal. symmetry.
    apply (ext_inst_eval_inv v σ u Hc Hlc).
    apply (proj1 (tm_eval_in_store_restrict_fv_subset σ (tret v) u (fv_tm (tret v))
      ltac:(set_solver))). exact Hev.
Qed.

Lemma ext_result_lookup (w : WfWorldT) z v :
  z ∉ fv_value v ->
  lc_value v ->
  wfworld_closed_on (fv_value v) w ->
  w ⊨ expr_result_formula (tret v) (LVFree z) ->
  forall σ, (w : WorldT) σ -> σ !! z = Some (ext_inst v σ).
Proof.
  intros Hzv Hlc Hcl Hres σ Hσ.
  pose proof (expr_result_formula_to_atom_world (tret v) (LVFree z) w Hres)
    as [_ [_ Hst]].
  destruct (Hst (lstore_lift_free σ) ltac:(exists σ; split; [exact Hσ|reflexivity]))
    as [_ [u [Hu Hev]]].
  rewrite lstore_lift_free_lookup_free in Hu. rewrite Hu. f_equal.
  apply (ext_inst_eval_inv v σ u (Hcl σ Hσ) Hlc). exact Hev.
Qed.

Lemma ext_result_dom (w : WfWorldT) z v :
  lc_value v ->
  w ⊨ expr_result_formula (tret v) (LVFree z) ->
  z ∈ world_dom (w : WorldT) /\ fv_value v ⊆ world_dom (w : WorldT).
Proof.
  intros Hlc Hres.
  pose proof (expr_result_formula_to_atom_world (tret v) (LVFree z) w Hres)
    as [_ [Hdom _]].
  rewrite res_lift_free_dom, ext_lvars_ret_value in Hdom by exact Hlc.
  split.
  - assert (Hin : LVFree z ∈ lvars_of_atoms (world_dom (w : WorldT))) by set_solver.
    unfold lvars_of_atoms in Hin. apply elem_of_map in Hin as [a [Ha Hin]].
    inversion Ha. subst. exact Hin.
  - intros a Ha.
    assert (Hin : LVFree a ∈ lvars_of_atoms (world_dom (w : WorldT))).
    { apply Hdom. apply elem_of_union_l. unfold lvars_of_atoms. apply elem_of_map. eauto. }
    unfold lvars_of_atoms in Hin. apply elem_of_map in Hin as [b [Hb Hin]].
    inversion Hb. subst. exact Hin.
Qed.

Lemma ext_result_swapc (w : WfWorldT) z v :
  z ∉ fv_value v ->
  lc_value v ->
  wfworld_closed_on (fv_value v) w ->
  w ⊨ expr_result_formula (tret v) (LVFree z) ->
  w = ext_swapc (res_restrict w (world_dom (w : WorldT) ∖ {[z]})) z v.
Proof.
  intros Hzv Hlc Hcl Hres.
  destruct (ext_result_dom w z v Hlc Hres) as [Hz Hv].
  apply ext_swapc_self_restrict; try assumption.
  apply ext_result_lookup; assumption.
Qed.

(** Instantiation by closed stores is injective on the free variables. *)
Lemma ext_msubst_inj_mut :
  (forall v : value, forall ρ1 ρ2 : StoreT, closed_env ρ1 -> closed_env ρ2 ->
     m{ρ1} v = m{ρ2} v -> forall a, a ∈ fv_value v -> a ∈ dom ρ1 -> a ∈ dom ρ2 ->
     ρ1 !! a = ρ2 !! a) *
  (forall e : tm, forall ρ1 ρ2 : StoreT, closed_env ρ1 -> closed_env ρ2 ->
     m{ρ1} e = m{ρ2} e -> forall a, a ∈ fv_tm e -> a ∈ dom ρ1 -> a ∈ dom ρ2 ->
     ρ1 !! a = ρ2 !! a).
Proof.
  apply value_tm_mutind; intros;
    match goal with
    | Heq : m{_} _ = m{_} _ |- _ =>
        rewrite ?msubst_ret, ?msubst_lete, ?msubst_tprim, ?msubst_tbinop,
          ?msubst_tapp, ?msubst_tmatch, ?msubst_tnode, ?msubst_tmatchtree,
          ?msubst_tcons, ?msubst_tmatchlist, ?msubst_vlam, ?msubst_vfix in Heq
    end;
    cbn [fv_value fv_tm] in *;
    try set_solver.
  all: try (injection H3; intros;
    repeat match goal with
    | Ha : _ ∈ _ ∪ _ |- _ => apply elem_of_union in Ha as [Ha|Ha]
    end; eauto; fail).
  (* fvar *)
  apply elem_of_singleton in H2. subst a.
  apply elem_of_dom in H3 as [u1 Hu1]. apply elem_of_dom in H4 as [u2 Hu2].
  rewrite (msubst_fvar_lookup_closed ρ1 x u1 H Hu1) in H1.
  rewrite (msubst_fvar_lookup_closed ρ2 x u2 H0 Hu2) in H1.
  rewrite Hu1, Hu2. f_equal. exact H1.
Qed.

Lemma ext_inst_inj v (σ1 σ2 : StoreT) :
  store_closed (store_restrict σ1 (fv_value v)) ->
  store_closed (store_restrict σ2 (fv_value v)) ->
  fv_value v ⊆ dom σ1 -> fv_value v ⊆ dom σ2 ->
  ext_inst v σ1 = ext_inst v σ2 ->
  store_restrict σ1 (fv_value v) = store_restrict σ2 (fv_value v).
Proof.
  intros Hc1 Hc2 Hd1 Hd2 Heq. unfold ext_inst in Heq.
  apply map_eq. intros a. rewrite !ext_restrict_lookup.
  destruct (decide (a ∈ fv_value v)) as [Ha|Ha]; [ |reflexivity].
  pose proof (fst ext_msubst_inj_mut v _ _ (proj1 Hc1) (proj1 Hc2) Heq a Ha) as H.
  rewrite !ext_restrict_lookup in H. destruct (decide (a ∈ fv_value v)); [ |contradiction].
  apply H.
  - rewrite storeA_restrict_dom. set_solver.
  - rewrite storeA_restrict_dom. set_solver.
Qed.


Section ExtValueTransport.

Variables v1 v2 : value.
Hypothesis Hlc1 : lc_value v1.
Hypothesis Hlc2 : lc_value v2.
Hypothesis Hfv12 : fv_value v1 = fv_value v2.

Lemma ext_vt_lvars : tm_lvars (tret v1) = tm_lvars (tret v2).
Proof.
  rewrite !ext_lvars_ret_value by assumption. rewrite Hfv12. reflexivity.
Qed.

Lemma ext_vt_relevant Δ τ :
  relevant_env Δ τ (tret v1) = relevant_env Δ τ (tret v2).
Proof. unfold relevant_env. rewrite ext_vt_lvars. reflexivity. Qed.

Lemma ext_vt_typing_restrict Δ τ T :
  basic_tm_has_ltype Δ (tret v2) T ->
  basic_tm_has_ltype (relevant_env Δ τ (tret v2)) (tret v2) T.
Proof.
  intros Hty. unfold relevant_env, lty_env_restrict_lvars.
  apply basic_tm_has_ltype_restrict_lvars_lc; [exact Hty|constructor; exact Hlc2|set_solver].
Qed.

Lemma ext_vt_guard Δ τ (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Δ τ (tret v1)) τ (tret v1) ->
  basic_tm_has_ltype Δ (tret v2) (erase_ty τ) ->
  m ⊨ ty_guard_formula (relevant_env Δ τ (tret v2)) τ (tret v2).
Proof.
  intros Hg Hty. rewrite <- ext_vt_relevant.
  unfold ty_guard_formula in Hg |- *.
  repeat rewrite res_models_and_iff in Hg.
  destruct Hg as [Hwf [Hbw [Hbt _]]].
  assert (Hbt2 : m ⊨ expr_basic_typing_formula (relevant_env Δ τ (tret v1)) (tret v2) (erase_ty τ)).
  {
    apply expr_basic_typing_formula_models_iff in Hbt as [Hlc [Hsc _]].
    apply expr_basic_typing_formula_models_iff. split; [exact Hlc| ]. split; [exact Hsc| ].
    rewrite ext_vt_relevant. apply ext_vt_typing_restrict. exact Hty.
  }
  repeat rewrite res_models_and_iff. split; [exact Hwf| ]. split; [exact Hbw| ].
  split; [exact Hbt2| ].
  eapply expr_total_formula_tret_of_basic; eauto.
Qed.

Lemma ext_vt_zero Δ τ (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Δ τ (tret v1) ->
  basic_tm_has_ltype Δ (tret v2) (erase_ty τ) ->
  m ⊨ ty_denote_gas 0 Δ τ (tret v2).
Proof.
  intros H0 Hty.
  apply ty_denote_gas_zero_of_guard.
  apply (ext_vt_guard Δ τ m); [ |exact Hty].
  exact (ty_denote_gas_guard_of_zero _ _ _ _ H0).
Qed.


Lemma ext_restrict_self (w : WfWorldT) : res_restrict w (world_dom (w : WorldT)) = w.
Proof. apply res_restrict_eq_of_le. apply raw_le_refl. Qed.

Lemma ext_swapc_le (w : WfWorldT) z v :
  z ∉ world_dom (w : WorldT) -> w ⊑ ext_swapc w z v.
Proof.
  intros Hz. rewrite <- (ext_restrict_self w) at 1.
  rewrite <- (ext_swapc_restrict_off w z v (world_dom (w : WorldT)) Hz).
  apply res_restrict_le.
Qed.

Lemma ext_typing_fv Σ e T :
  basic_tm_has_ltype Σ e T -> fv_tm e ⊆ lvars_fv (dom Σ).
Proof.
  intros Hty a Ha. apply lvars_fv_elem. apply (basic_tm_has_ltype_lvars _ _ _ Hty).
  unfold lvars_of_atoms. apply elem_of_map. eauto.
Qed.

Lemma ext_lvars_fv_insert (Σ : lty_env) z (T : ty) :
  lvars_fv (dom (<[LVFree z := T]> Σ)) = {[z]} ∪ lvars_fv (dom Σ).
Proof.
  rewrite dom_insert_L, lvars_fv_union, lvars_fv_singleton_free. reflexivity.
Qed.

Lemma ext_static_ret Σg τ T z v (w : WfWorldT) :
  lty_env_closed Σg -> LVFree z ∉ dom Σg ->
  lvars_fv (dom Σg) ⊆ world_dom (w : WorldT) -> z ∈ world_dom (w : WorldT) ->
  basic_context_ty_lvars (dom Σg) τ -> T = erase_ty τ ->
  w ⊨ basic_world_formula Σg -> basic_tm_has_ltype Σg (tret v) T ->
  w ⊨ expr_result_formula (tret v) (LVFree z) ->
  w ⊨ ty_static_guard_formula (<[LVFree z := T]> Σg) τ (tret v).
Proof.
  intros Hcl HzΣ Hdom Hzw Hτ HT Hbw Hty Hres.
  assert (Hsub : Σg ⊆ <[LVFree z := T]> Σg).
  { apply insert_subseteq. apply not_elem_of_dom. exact HzΣ. }
  assert (Hdomz : lvars_fv (dom (<[LVFree z := T]> Σg)) ⊆ world_dom (w : WorldT)).
  { rewrite ext_lvars_fv_insert. set_solver. }
  assert (Hclz : lty_env_closed (<[LVFree z := T]> Σg)) by (apply lty_env_closed_insert_free; exact Hcl).
  assert (Hbt : w ⊨ expr_basic_typing_formula Σg (tret v) T).
  { apply expr_basic_typing_formula_models_iff. split; [exact Hcl| ].
    split; [exact Hdom|exact Hty]. }
  unfold ty_static_guard_formula. repeat rewrite res_models_and_iff.
  split; [ |split].
  - apply context_ty_wf_formula_models_iff. split; [exact Hclz| ]. split; [exact Hdomz| ].
    eapply basic_context_ty_lvars_mono; [ |exact Hτ]. rewrite dom_insert_L. set_solver.
  - eapply basic_world_insert_result_alias; eauto.
  - apply expr_basic_typing_formula_models_iff. split; [exact Hclz| ].
    split; [exact Hdomz| ]. subst T. eapply basic_tm_has_ltype_weaken; eauto.
Qed.

Lemma ext_vt_cs_ret g Σg τ T z (b : WfWorldT) :
  (forall Δ' (n : WfWorldT), basic_tm_has_ltype Δ' (tret v2) (erase_ty τ) ->
     n ⊨ ty_denote_gas g Δ' τ (tret v1) -> n ⊨ ty_denote_gas g Δ' τ (tret v2)) ->
  lty_env_closed Σg -> LVFree z ∉ dom Σg -> z ∉ world_dom (b : WorldT) ->
  z ∉ fv_value v1 -> z ∉ fv_cty τ -> T = erase_ty τ ->
  lvars_fv (dom Σg) ⊆ world_dom (b : WorldT) ->
  b ⊨ basic_world_formula Σg ->
  basic_tm_has_ltype Σg (tret v1) T -> basic_tm_has_ltype Σg (tret v2) T ->
  basic_context_ty_lvars (dom Σg) τ ->
  ext_swapc b z v1 ⊨ ty_denote_gas g (<[LVFree z := T]> Σg) τ (tret (vfvar z)) ->
  ext_swapc b z v2 ⊨ ty_denote_gas g (<[LVFree z := T]> Σg) τ (tret (vfvar z)).
Proof.
  intros IH Hcl HzΣ Hzb Hz1 Hzτ HT Hdomb Hbw Hty1 Hty2 Hτ Hsrc.
  assert (Hz2 : z ∉ fv_value v2) by (rewrite <- Hfv12; exact Hz1).
  pose proof (ext_typing_fv _ _ _ Hty1) as Hfv1. cbn [fv_tm] in Hfv1.
  pose proof (ext_typing_fv _ _ _ Hty2) as Hfv2. cbn [fv_tm] in Hfv2.
  pose proof (basic_world_formula_wfworld_closed_on_dom _ _ Hbw) as Hclb.
  set (Σz := <[LVFree z := T]> Σg).
  set (wu := ext_swapc b z v1). set (wf := ext_swapc b z v2).
  assert (Hzwu : z ∈ world_dom (wu : WorldT)) by (subst wu; rewrite ext_swapc_dom; set_solver).
  assert (Hzwf : z ∈ world_dom (wf : WorldT)) by (subst wf; rewrite ext_swapc_dom; set_solver).
  assert (Hres1 : wu ⊨ expr_result_formula (tret v1) (LVFree z)).
  { apply ext_swapc_result; try assumption; [set_solver| ].
    eapply wfworld_closed_on_mono; [ |exact Hclb]. exact Hfv1. }
  assert (Hres2 : wf ⊨ expr_result_formula (tret v2) (LVFree z)).
  { apply ext_swapc_result; try assumption; [set_solver| ].
    eapply wfworld_closed_on_mono; [ |exact Hclb]. exact Hfv2. }
  assert (Hbwu : wu ⊨ basic_world_formula Σg).
  { eapply res_models_kripke; [apply ext_swapc_le; exact Hzb|exact Hbw]. }
  assert (Hbwf : wf ⊨ basic_world_formula Σg).
  { eapply res_models_kripke; [apply ext_swapc_le; exact Hzb|exact Hbw]. }
  assert (Hst1 : wu ⊨ ty_static_guard_formula Σz τ (tret v1)).
  { eapply ext_static_ret; eauto. subst wu. rewrite ext_swapc_dom. set_solver. }
  assert (Hst2 : wf ⊨ ty_static_guard_formula Σz τ (tret v2)).
  { eapply ext_static_ret; eauto. subst wf. rewrite ext_swapc_dom. set_solver. }
  assert (Hclz1 : wfworld_closed_on (fv_tm (tret (vfvar z)) ∪ fv_tm (tret v1)) wu).
  { pose proof (ty_static_guard_basic_world _ _ _ _ Hst1) as Hb.
    eapply wfworld_closed_on_mono; [ |exact (basic_world_formula_wfworld_closed_on_dom _ _ Hb)].
    subst Σz. rewrite ext_lvars_fv_insert. cbn [fv_tm fv_value]. set_solver. }
  assert (Hclz2 : wfworld_closed_on (fv_tm (tret (vfvar z)) ∪ fv_tm (tret v2)) wf).
  { pose proof (ty_static_guard_basic_world _ _ _ _ Hst2) as Hb.
    eapply wfworld_closed_on_mono; [ |exact (basic_world_formula_wfworld_closed_on_dom _ _ Hb)].
    subst Σz. rewrite ext_lvars_fv_insert. cbn [fv_tm fv_value]. set_solver. }
  (* down *)
  assert (Hd1 : wu ⊨ ty_denote_gas g Σz τ (tret v1)).
  {
    eapply ty_denote_gas_tm_equiv; [ |exact Hsrc].
    split; [exact (tm_equiv_ret_value_result_alias wu v1 z Hclz1 Hlc1 Hres1)| ].
    split; [exact (tm_total_equiv_ret_value_result_alias wu v1 z Hclz1 Hlc1 Hres1)| ].
    split.
    - apply ty_denote_gas_zero_of_guard. exact (ty_denote_gas_guard _ _ _ _ _ Hsrc).
    - apply ty_denote_gas_zero_tret_of_static_guard. exact Hst1.
  }
  assert (Hd2 : wu ⊨ ty_denote_gas g Σz τ (tret v2)).
  { apply IH; [ |exact Hd1]. subst Σz. rewrite <- HT.
    eapply basic_tm_has_ltype_weaken; [exact Hty2| ].
    apply insert_subseteq. apply not_elem_of_dom. exact HzΣ. }
  assert (Hd2f : wf ⊨ ty_denote_gas g Σz τ (tret v2)).
  {
    eapply res_models_projection; [ |exact Hd2].
    pose proof (formula_fv_ty_denote_gas_subset_relevant g Σz τ (tret v2)) as Hfvφ.
    assert (Hzφ : z ∉ formula_fv (ty_denote_gas g Σz τ (tret v2))).
    { intros Hin. apply Hfvφ in Hin. cbn [fv_tm] in Hin. set_solver. }
    subst wu wf. rewrite !ext_swapc_restrict_off by exact Hzφ. reflexivity.
  }
  (* up *)
  eapply ty_denote_gas_tm_equiv; [ |exact Hd2f].
  apply typed_total_equiv_ret_value_result_alias_static; try assumption.
  - eapply ty_static_guard_ret_value_result_alias; [ | |exact Hres2|exact Hst2].
    + subst Σz. apply lty_env_closed_insert_free. exact Hcl.
    + subst Σz. rewrite <- HT. apply lookup_insert_eq.
  - apply ty_denote_gas_zero_of_guard. exact (ty_denote_gas_guard _ _ _ _ _ Hd2f).
Qed.

Lemma ext_guard_parts Σ τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  lty_env_closed Σ /\ lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  m ⊨ basic_world_formula Σ /\ basic_tm_has_ltype Σ e (erase_ty τ) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  intros Hg. pose proof Hg as Hg'. unfold ty_guard_formula in Hg'.
  repeat rewrite res_models_and_iff in Hg'.
  destruct Hg' as [Hwf [Hbw [Hbt _]]].
  pose proof Hbw as Hbw'.
  apply basic_world_formula_models_iff in Hbw' as [Hlc [Hsc _]].
  apply expr_basic_typing_formula_models_iff in Hbt as [_ [_ Hty]].
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hτ]].
  split; [exact Hlc| ]. split; [exact Hsc| ]. split; [exact Hbw| ].
  split; [exact Hty|exact Hτ].
Qed.

Lemma ext_vt_forall_swap Σg τ (m : WfWorldT) B :
  m ⊨ ty_guard_formula Σg τ (tret v1) ->
  formula_scoped_in_world m
    (FForall (FImpl (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
      (tm_shift 0 (tret v2)) (LVBound 0)) B)) ->
  (exists L : aset, forall z, z ∉ L -> z ∉ world_dom (m : WorldT) ->
     ext_swapc m z v1 ⊨ formula_open 0 z B ->
     ext_swapc m z v2 ⊨ formula_open 0 z B) ->
  m ⊨ FForall (FImpl (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
      (tm_shift 0 (tret v1)) (LVBound 0)) B) ->
  m ⊨ FForall (FImpl (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
      (tm_shift 0 (tret v2)) (LVBound 0)) B).
Proof.
  intros Hg Hscope [L HB] Hsrc.
  destruct (ext_guard_parts _ _ _ _ Hg) as [Hcl [Hdom [Hbw [Hty _]]]].
  pose proof (ext_typing_fv _ _ _ Hty) as Hfv1. cbn [fv_tm] in Hfv1.
  assert (Hfv2 : fv_value v2 ⊆ lvars_fv (dom Σg)) by (rewrite <- Hfv12; exact Hfv1).
  pose proof (basic_world_formula_wfworld_closed_on_dom _ _ Hbw) as Hclm.
  eapply res_models_forall_rev_intro; [exact Hscope| ].
  exists (L ∪ world_dom (m : WorldT) ∪ fv_value v1 ∪ lvars_fv (dom Σg)).
  intros z Hz mz Hdomz Hrestrz.
  assert (HzL : z ∉ L) by set_solver.
  assert (Hzm : z ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hz1 : z ∉ fv_value v1) by set_solver.
  assert (Hz2 : z ∉ fv_value v2) by (rewrite <- Hfv12; exact Hz1).
  assert (HzΣ : z ∉ lvars_fv (dom Σg)) by set_solver.
  assert (Hle : m ⊑ mz) by (rewrite <- Hrestrz; apply res_restrict_le).
  pose proof (formula_scoped_forall_open_res_le m mz z _ Hscope Hle
    (opened_world_dom_contains_slot m mz z Hdomz)) as Hosc.
  rewrite formula_open_impl in Hosc |- *.
  eapply res_models_impl_intro; [exact Hosc| ].
  intros Hres2.
  rewrite ext_open_result_shift0 in Hres2 by
    (exact Hcl || (constructor; exact Hlc2) || exact HzΣ || (cbn [fv_tm]; exact Hz2)).
  assert (Hres2' : mz ⊨ expr_result_formula (tret v2) (LVFree z)).
  {
    unfold expr_result_formula.
    apply (expr_result_formula_at_coarsen_domain (tm_lvars (tret v2)) (dom Σg)).
    - rewrite ext_lvars_ret_value by exact Hlc2. rewrite <- Hfv12.
      exact (basic_tm_has_ltype_lvars _ _ _ Hty).
    - reflexivity.
    - intros Hin. apply HzΣ. apply lvars_fv_elem. exact Hin.
    - exact Hres2.
  }
  assert (Hclz : wfworld_closed_on (fv_value v2) mz).
  { eapply wfworld_closed_on_le; [ |exact Hle| ].
    - set_solver.
    - eapply wfworld_closed_on_mono; [ |exact Hclm]. exact Hfv2. }
  pose proof (ext_result_swapc mz z v2 Hz2 Hlc2 Hclz Hres2') as Hmz.
  assert (Hbase : res_restrict mz (world_dom (mz : WorldT) ∖ {[z]}) = m).
  { rewrite <- Hrestrz. f_equal. rewrite Hdomz. apply set_eq. intros a.
    destruct (decide (a = z)); set_solver. }
  rewrite Hbase in Hmz. rewrite Hmz.
  destruct (ext_result_world_exists Σg τ (tret v1) m z Hg Hzm)
    as [my [Hdomy [Hrestry [Haty Hply]]]].
  assert (Hcly : wfworld_closed_on (fv_value v1) my).
  { assert (Hley : m ⊑ my) by (rewrite <- Hrestry; apply res_restrict_le).
    eapply wfworld_closed_on_le; [ |exact Hley| ].
    - set_solver.
    - eapply wfworld_closed_on_mono; [ |exact Hclm]. exact Hfv1. }
  pose proof (ext_result_swapc my z v1 Hz1 Hlc1 Hcly Hply) as Hmy.
  assert (Hbasey : res_restrict my (world_dom (my : WorldT) ∖ {[z]}) = m).
  { rewrite <- Hrestry. f_equal. rewrite Hdomy. apply set_eq. intros a.
    destruct (decide (a = z)); set_solver. }
  rewrite Hbasey in Hmy.
  apply (HB z HzL Hzm). rewrite <- Hmy.
  apply (result_first_forall_impl_open_elim m my z _ _ Hsrc Hzm Hdomy Hrestry).
  rewrite ext_open_result_shift0 by
    (exact Hcl || (constructor; exact Hlc1) || exact HzΣ || (cbn [fv_tm]; exact Hz1)).
  exact Haty.
Qed.

Lemma ext_bctl_binary D τ1 τ2 :
  (basic_context_ty_lvars D (CTSum τ1 τ2) \/ basic_context_ty_lvars D (CTInter τ1 τ2) \/
   basic_context_ty_lvars D (CTUnion τ1 τ2)) ->
  basic_context_ty_lvars D τ1 /\ basic_context_ty_lvars D τ2 /\ erase_ty τ1 = erase_ty τ2.
Proof.
  intros [H|[H|H]]; destruct H as [Hv [Hs1 [Hs2 He]]];
    cbn [context_ty_lvars context_ty_lvars_at] in Hv; unfold context_ty_lvars in *;
    (split; [split; [set_solver|exact Hs1]| ]; split; [split; [set_solver|exact Hs2]|exact He]).
Qed.

Lemma ext_swapc_subset_base (q w : WfWorldT) z v :
  res_subset q (ext_swapc w z v) ->
  z ∉ world_dom (w : WorldT) ->
  res_subset (res_restrict q (world_dom (w : WorldT))) w.
Proof.
  intros [Hdom Hsub] Hz.
  change (world_dom (q : WorldT) = world_dom (ext_swapc w z v : WorldT)) in Hdom.
  split.
  - change (world_dom (res_restrict q (world_dom (w : WorldT)) : WorldT) = world_dom (w : WorldT)).
    rewrite res_restrict_dom, Hdom, ext_swapc_dom. set_solver.
  - intros σ Hσ. apply ext_restrict_stores in Hσ as [σ0 [Hσ0 <-]].
    apply Hsub in Hσ0. apply ext_swapc_stores in Hσ0 as [σ1 [Hσ1 ->]].
    rewrite storeA_restrict_insert_notin by exact Hz.
    rewrite storeA_restrict_idemp; [exact Hσ1| ].
    rewrite (wfworld_store_dom w σ1 Hσ1). reflexivity.
Qed.

Lemma ext_swapc_subset' (q w : WfWorldT) z v :
  res_subset q (ext_swapc w z v) ->
  z ∉ world_dom (w : WorldT) ->
  z ∉ fv_value v ->
  fv_value v ⊆ world_dom (w : WorldT) ->
  q = ext_swapc (res_restrict q (world_dom (w : WorldT))) z v.
Proof.
  intros Hs Hz Hzv Hv.
  rewrite (ext_swapc_subset q w z v Hs Hzv Hv) at 1.
  f_equal. f_equal. destruct Hs as [Hdom _].
  change (world_dom (q : WorldT) = world_dom (ext_swapc w z v : WorldT)) in Hdom.
  rewrite Hdom, ext_swapc_dom. apply set_eq. intros a.
  destruct (decide (a = z)); set_solver.
Qed.

Lemma ext_le_full_eq (p w : WfWorldT) :
  p ⊑ w -> world_dom (p : WorldT) = world_dom (w : WorldT) -> p = w.
Proof.
  intros Hle Hdom. rewrite <- (res_restrict_eq_of_le p w Hle), Hdom.
  apply ext_restrict_self.
Qed.

Lemma ext_vt_sum_body g Σg τ1 τ2 z (m : WfWorldT) :
  (forall Δ' (n : WfWorldT), basic_tm_has_ltype Δ' (tret v2) (erase_ty τ1) ->
     n ⊨ ty_denote_gas g Δ' τ1 (tret v1) -> n ⊨ ty_denote_gas g Δ' τ1 (tret v2)) ->
  (forall Δ' (n : WfWorldT), basic_tm_has_ltype Δ' (tret v2) (erase_ty τ2) ->
     n ⊨ ty_denote_gas g Δ' τ2 (tret v1) -> n ⊨ ty_denote_gas g Δ' τ2 (tret v2)) ->
  lty_env_closed Σg -> LVFree z ∉ dom Σg -> z ∉ world_dom (m : WorldT) ->
  z ∉ fv_value v1 -> z ∉ fv_cty τ1 -> z ∉ fv_cty τ2 ->
  lvars_fv (dom Σg) ⊆ world_dom (m : WorldT) ->
  m ⊨ basic_world_formula Σg ->
  basic_tm_has_ltype Σg (tret v1) (erase_ty τ1) ->
  basic_tm_has_ltype Σg (tret v2) (erase_ty τ1) ->
  basic_context_ty_lvars (dom Σg) (CTSum τ1 τ2) ->
  ext_swapc m z v1 ⊨ FPlus
    (ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ1 (tret (vfvar z)))
    (ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ2 (tret (vfvar z))) ->
  ext_swapc m z v2 ⊨ FPlus
    (ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ1 (tret (vfvar z)))
    (ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ2 (tret (vfvar z))).
Proof.
  intros IH1 IH2 Hcl HzΣ Hzm Hz1 Hzτ1 Hzτ2 Hdomm Hbw Hty1 Hty2 Hτ Hsrc.
  destruct (ext_bctl_binary _ _ _ (or_introl Hτ)) as [Hτ1 [Hτ2 He12]].
  pose proof (ext_typing_fv _ _ _ Hty1) as Hfv1. cbn [fv_tm] in Hfv1.
  assert (Hfvm : fv_value v1 ⊆ world_dom (m : WorldT)) by set_solver.
  apply res_models_plus_iff in Hsrc as [p1 [p2 [Hdef [Hle [Hp1 Hp2]]]]].
  destruct (res_sum_pullback_subset_projection_full _ p1 p2 Hdef Hle)
    as [Hs1 [Hs2 [Hdf Hlef]]].
  set (q1 := res_pullback_subset_projection (ext_swapc m z v1) p1 Hs1) in *.
  set (q2 := res_pullback_subset_projection (ext_swapc m z v1) p2 Hs2) in *.
  pose proof (res_models_pullback_subset_projection _ _ Hs1 _ Hp1) as Hq1. fold q1 in Hq1.
  pose proof (res_models_pullback_subset_projection _ _ Hs2 _ Hp2) as Hq2. fold q2 in Hq2.
  pose proof (res_pullback_subset_projection_subset _ _ Hs1) as Hsub1. fold q1 in Hsub1.
  pose proof (res_pullback_subset_projection_subset _ _ Hs2) as Hsub2. fold q2 in Hsub2.
  set (b1 := res_restrict q1 (world_dom (m : WorldT))).
  set (b2 := res_restrict q2 (world_dom (m : WorldT))).
  pose proof (ext_swapc_subset' q1 m z v1 Hsub1 Hzm Hz1 Hfvm) as Hq1eq. fold b1 in Hq1eq.
  pose proof (ext_swapc_subset' q2 m z v1 Hsub2 Hzm Hz1 Hfvm) as Hq2eq. fold b2 in Hq2eq.
  pose proof (ext_swapc_subset_base q1 m z v1 Hsub1 Hzm) as Hb1m. fold b1 in Hb1m.
  pose proof (ext_swapc_subset_base q2 m z v1 Hsub2 Hzm) as Hb2m. fold b2 in Hb2m.
  assert (Hdb1 : world_dom (b1 : WorldT) = world_dom (m : WorldT)) by (destruct Hb1m as [H _]; exact H).
  assert (Hdb2 : world_dom (b2 : WorldT) = world_dom (m : WorldT)) by (destruct Hb2m as [H _]; exact H).
  assert (Hc1 : ext_swapc b1 z v2 ⊨
      ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ1 (tret (vfvar z))).
  {
    eapply (ext_vt_cs_ret g Σg τ1 (erase_ty τ1) z b1); try eassumption; try reflexivity.
    - rewrite Hdb1. exact Hzm.
    - rewrite Hdb1. exact Hdomm.
    - eapply basic_world_formula_res_subset; eassumption.
    - rewrite <- Hq1eq. exact Hq1.
  }
  assert (Hc2 : ext_swapc b2 z v2 ⊨
      ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ2 (tret (vfvar z))).
  {
    eapply (ext_vt_cs_ret g Σg τ2 (erase_ty τ1) z b2); try eassumption.
    - rewrite Hdb2. exact Hzm.
    - rewrite Hdb2. exact Hdomm.
    - eapply basic_world_formula_res_subset; eassumption.
    - rewrite <- Hq2eq. exact Hq2.
  }
  assert (Hdefb : raw_sum_defined (b1 : WorldT) (b2 : WorldT)).
  { unfold raw_sum_defined, rawA_sum_defined.
    change (world_dom (b1 : WorldT) = world_dom (b2 : WorldT)). congruence. }
  pose proof (ext_swapc_sum_defined b1 b2 z v2 Hdefb) as Hdef'.
  apply (res_models_plus_intro _ _ _ _ _ Hdef'); [ |exact Hc1|exact Hc2].
  rewrite (ext_swapc_sum b1 b2 z v2 Hdefb Hdef').
  assert (Hsum : res_sum b1 b2 Hdefb = m).
  {
    subst b1 b2. rewrite <- (ext_restrict_sum q1 q2 (world_dom (m : WorldT)) Hdf Hdefb).
    rewrite (ext_le_full_eq _ _ Hlef).
    - rewrite ext_swapc_restrict_off by exact Hzm. apply ext_restrict_self.
    - rewrite ext_sum_dom. destruct Hsub1 as [H _]. exact H.
  }
  rewrite Hsum. apply raw_le_refl.
Qed.

Lemma ext_inst_swap_eq (σa σb : StoreT) F z :
  z ∉ fv_value v1 ->
  store_closed (store_restrict σa (fv_value v1)) ->
  store_closed (store_restrict σb (fv_value v1)) ->
  fv_value v1 ⊆ dom σa -> fv_value v1 ⊆ dom σb ->
  store_restrict (ext_ins z (ext_inst v1 σa) σa) F =
    store_restrict (ext_ins z (ext_inst v1 σb) σb) F ->
  store_restrict (ext_ins z (ext_inst v2 σa) σa) F =
    store_restrict (ext_ins z (ext_inst v2 σb) σb) F.
Proof.
  intros Hz Hca Hcb Hda Hdb Heq.
  apply map_eq. intros k.
  pose proof (f_equal (fun s : StoreT => s !! k) Heq) as Hk. cbn beta in Hk.
  rewrite !ext_restrict_lookup in Hk |- *.
  destruct (decide (k ∈ F)) as [HkF|HkF]; [ |reflexivity].
  destruct (decide (k = z)) as [->|Hkz].
  - rewrite !ext_insert_lookup_eq in Hk |- *. injection Hk as Hk.
    pose proof (ext_inst_inj v1 σa σb Hca Hcb Hda Hdb Hk) as Hr.
    unfold ext_inst. rewrite <- !Hfv12, Hr. reflexivity.
  - rewrite !ext_insert_lookup_ne in Hk |- * by exact Hkz. exact Hk.
Qed.

Lemma ext_singleton_stores (σ τ : StoreT) :
  ((exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) : WorldT) τ <-> τ = σ.
Proof. reflexivity. Qed.

Lemma ext_singleton_dom (σ : StoreT) :
  world_dom ((exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) : WorldT) = dom σ.
Proof. reflexivity. Qed.

Lemma ext_vt_persist_body g Σg τ1 z (m : WfWorldT) :
  (forall Δ' (n : WfWorldT), basic_tm_has_ltype Δ' (tret v2) (erase_ty τ1) ->
     n ⊨ ty_denote_gas g Δ' τ1 (tret v1) -> n ⊨ ty_denote_gas g Δ' τ1 (tret v2)) ->
  lty_env_closed Σg -> LVFree z ∉ dom Σg -> z ∉ world_dom (m : WorldT) ->
  z ∉ fv_value v1 -> z ∉ fv_cty τ1 ->
  lvars_fv (dom Σg) ⊆ world_dom (m : WorldT) ->
  m ⊨ basic_world_formula Σg ->
  basic_tm_has_ltype Σg (tret v1) (erase_ty τ1) ->
  basic_tm_has_ltype Σg (tret v2) (erase_ty τ1) ->
  basic_context_ty_lvars (dom Σg) τ1 ->
  ext_swapc m z v1 ⊨ FPersist
    (ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ1 (tret (vfvar z))) ->
  ext_swapc m z v2 ⊨ FPersist
    (ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ1 (tret (vfvar z))).
Proof.
  intros IH1 Hcl HzΣ Hzm Hz1 Hzτ1 Hdomm Hbw Hty1 Hty2 Hτ1 Hsrc.
  set (A := ty_denote_gas g (<[LVFree z := erase_ty τ1]> Σg) τ1 (tret (vfvar z))) in *.
  pose proof (ext_typing_fv _ _ _ Hty1) as Hfv1. cbn [fv_tm] in Hfv1.
  pose proof (basic_world_formula_wfworld_closed_on_dom _ _ Hbw) as Hclb.
  pose proof (res_models_persist_elim _ _ Hsrc) as HAu.
  assert (HAf : ext_swapc m z v2 ⊨ A).
  { eapply (ext_vt_cs_ret g Σg τ1 (erase_ty τ1) z m); try eassumption; reflexivity. }
  apply res_models_persist_iff in Hsrc as [σ [Hdomσ [Hrestr _]]].
  set (F := formula_fv A) in *.
  assert (HFdom : F ⊆ world_dom (m : WorldT) ∪ {[z]}).
  { pose proof (res_models_scoped _ _ HAu) as Hsc. unfold formula_scoped_in_world in Hsc.
    rewrite ext_swapc_dom in Hsc. exact Hsc. }
  assert (Hcl1 : forall σ0, (m : WorldT) σ0 ->
      store_closed (store_restrict σ0 (fv_value v1)) /\ fv_value v1 ⊆ dom σ0).
  { intros σ0 Hσ0. split.
    - apply (wfworld_closed_on_mono _ _ m (ltac:(exact Hfv1)) Hclb σ0 Hσ0).
    - rewrite (wfworld_store_dom m σ0 Hσ0). set_solver. }
  assert (Hall : forall σa σb, (m : WorldT) σa -> (m : WorldT) σb ->
      store_restrict (ext_ins z (ext_inst v2 σa) σa) F =
      store_restrict (ext_ins z (ext_inst v2 σb) σb) F).
  {
    intros σa σb Ha Hb.
    destruct (Hcl1 σa Ha) as [Hca Hda]. destruct (Hcl1 σb Hb) as [Hcb Hdb].
    apply ext_inst_swap_eq; try assumption.
    assert (Hin : forall σ0, (m : WorldT) σ0 ->
        store_restrict (ext_ins z (ext_inst v1 σ0) σ0) F = σ).
    { intros σ0 H0.
      assert (Hm : (res_restrict (ext_swapc m z v1) F : WorldT)
          (store_restrict (ext_ins z (ext_inst v1 σ0) σ0) F)).
      { apply ext_restrict_stores. eexists. split; [ |reflexivity].
        apply ext_swapc_stores. eauto. }
      rewrite Hrestr in Hm. exact Hm. }
    rewrite (Hin σa Ha), (Hin σb Hb). reflexivity.
  }
  destruct (world_wf m) as [[σa Ha] _].
  set (σ' := store_restrict (ext_ins z (ext_inst v2 σa) σa) F).
  assert (Hdomσ' : dom σ' = F).
  { subst σ'. rewrite storeA_restrict_dom.
    replace (dom (ext_ins z (ext_inst v2 σa) σa)) with ({[z]} ∪ dom σa)
      by (symmetry; apply dom_insert_L).
    rewrite (wfworld_store_dom m σa Ha). set_solver. }
  assert (Hrestr' : res_restrict (ext_swapc m z v2) F =
      (exist _ (singleton_world σ') (wf_singleton_world σ') : WfWorldT)).
  {
    apply ext_world_eq.
    - rewrite res_restrict_dom, ext_swapc_dom, ext_singleton_dom, Hdomσ'. set_solver.
    - intros τ. rewrite ext_restrict_stores, ext_singleton_stores. split.
      + intros [σ0 [Hσ0 <-]]. apply ext_swapc_stores in Hσ0 as [σb [Hb ->]].
        subst σ'. apply Hall; assumption.
      + intros ->. exists (ext_ins z (ext_inst v2 σa) σa). split; [ |reflexivity].
        apply ext_swapc_stores. eauto.
  }
  apply (res_models_persist_intro _ _ σ' Hdomσ' Hrestr').
  rewrite <- Hrestr'. apply res_models_restrict_fv. exact HAf.
Qed.

Variable Lapp : aset.
Hypothesis Happ : forall (n : WfWorldT) y, y ∉ Lapp -> y ∈ world_dom (n : WorldT) ->
  wfworld_closed_on (fv_value v1 ∪ {[y]}) n ->
  tm_equiv_on n (tapp_tm (tret v1) (vfvar y)) (tapp_tm (tret v2) (vfvar y)) /\
  tm_total_equiv_on n (tapp_tm (tret v1) (vfvar y)) (tapp_tm (tret v2) (vfvar y)).

Lemma ext_static_app Σ τa s y v (w : WfWorldT) :
  lty_env_closed Σ -> lvars_fv (dom Σ) ⊆ world_dom (w : WorldT) ->
  Σ !! LVFree y = Some s ->
  w ⊨ basic_world_formula Σ ->
  basic_tm_has_ltype Σ (tret v) (s →ₜ erase_ty τa) ->
  basic_context_ty_lvars (dom Σ) τa ->
  w ⊨ ty_static_guard_formula Σ τa (tapp_tm (tret v) (vfvar y)).
Proof.
  intros Hcl Hdom Hy Hbw Hty Hτ.
  unfold ty_static_guard_formula. repeat rewrite res_models_and_iff.
  split; [ |split; [exact Hbw| ]].
  - apply context_ty_wf_formula_models_iff. split; [exact Hcl| ]. split; [exact Hdom|exact Hτ].
  - apply expr_basic_typing_formula_models_iff. split; [exact Hcl| ]. split; [exact Hdom| ].
    eapply basic_tm_has_ltype_tapp_tm_lvar; [exact Hcl|exact Hty| ].
    constructor. exact Hy.
Qed.

Lemma ext_vt_cs_app g Σ τa s y z (b : WfWorldT) :
  y ∉ Lapp ->
  lty_env_closed Σ -> LVFree z ∉ dom Σ -> z ∉ world_dom (b : WorldT) -> z <> y ->
  z ∉ fv_value v1 -> z ∉ fv_cty τa ->
  Σ !! LVFree y = Some s ->
  lvars_fv (dom Σ) ⊆ world_dom (b : WorldT) ->
  b ⊨ basic_world_formula Σ ->
  basic_tm_has_ltype Σ (tret v1) (s →ₜ erase_ty τa) ->
  basic_tm_has_ltype Σ (tret v2) (s →ₜ erase_ty τa) ->
  basic_context_ty_lvars (dom Σ) τa ->
  ext_swapc b z v1 ⊨ ty_denote_gas g (<[LVFree z := s →ₜ erase_ty τa]> Σ) τa
    (tapp_tm (tret (vfvar z)) (vfvar y)) ->
  ext_swapc b z v2 ⊨ ty_denote_gas g (<[LVFree z := s →ₜ erase_ty τa]> Σ) τa
    (tapp_tm (tret (vfvar z)) (vfvar y)).
Proof.
  intros HyL Hcl HzΣ Hzb Hzy Hz1 Hzτ Hy Hdomb Hbw Hty1 Hty2 Hτ Hsrc.
  assert (Hz2 : z ∉ fv_value v2) by (rewrite <- Hfv12; exact Hz1).
  pose proof (ext_typing_fv _ _ _ Hty1) as Hfv1. cbn [fv_tm] in Hfv1.
  pose proof (ext_typing_fv _ _ _ Hty2) as Hfv2. cbn [fv_tm] in Hfv2.
  assert (Hyd : y ∈ lvars_fv (dom Σ)).
  { apply lvars_fv_elem. apply elem_of_dom. eauto. }
  pose proof (basic_world_formula_wfworld_closed_on_dom _ _ Hbw) as Hclb.
  set (wu := ext_swapc b z v1). set (wf := ext_swapc b z v2).
  assert (Hdu : lvars_fv (dom Σ) ⊆ world_dom (wu : WorldT)) by (subst wu; rewrite ext_swapc_dom; set_solver).
  assert (Hdf : lvars_fv (dom Σ) ⊆ world_dom (wf : WorldT)) by (subst wf; rewrite ext_swapc_dom; set_solver).
  assert (Hbwu : wu ⊨ basic_world_formula Σ).
  { eapply res_models_kripke; [apply ext_swapc_le; exact Hzb|exact Hbw]. }
  assert (Hbwf : wf ⊨ basic_world_formula Σ).
  { eapply res_models_kripke; [apply ext_swapc_le; exact Hzb|exact Hbw]. }
  assert (Hres1 : wu ⊨ expr_result_formula (tret v1) (LVFree z)).
  { apply ext_swapc_result; try assumption; [set_solver| ].
    eapply wfworld_closed_on_mono; [ |exact Hclb]. exact Hfv1. }
  assert (Hres2 : wf ⊨ expr_result_formula (tret v2) (LVFree z)).
  { apply ext_swapc_result; try assumption; [set_solver| ].
    eapply wfworld_closed_on_mono; [ |exact Hclb]. exact Hfv2. }
  assert (Hbt1 : wu ⊨ expr_basic_typing_formula Σ (tret v1) (s →ₜ erase_ty τa)).
  { apply expr_basic_typing_formula_models_iff. split; [exact Hcl| ]. split; assumption. }
  assert (Hbt2 : wf ⊨ expr_basic_typing_formula Σ (tret v2) (s →ₜ erase_ty τa)).
  { apply expr_basic_typing_formula_models_iff. split; [exact Hcl| ]. split; assumption. }
  assert (Hst1 : wu ⊨ ty_static_guard_formula Σ τa (tapp_tm (tret v1) (vfvar y)))
    by (eapply ext_static_app; eauto).
  assert (Hst2u : wu ⊨ ty_static_guard_formula Σ τa (tapp_tm (tret v2) (vfvar y)))
    by (eapply ext_static_app; eauto).
  assert (Hst2 : wf ⊨ ty_static_guard_formula Σ τa (tapp_tm (tret v2) (vfvar y)))
    by (eapply ext_static_app; eauto).
  assert (Hzfresh1 : z ∉ fv_value v1 ∪ {[y]} ∪ fv_cty τa) by set_solver.
  assert (Hzfresh2 : z ∉ fv_value v2 ∪ {[y]} ∪ fv_cty τa) by set_solver.
  (* back to the application of v1 *)
  pose proof (ty_denote_gas_tapp_fun_result_alias_back_from_static
    g Σ τa v1 y z s wu HzΣ Hzfresh1 Hy Hlc1 Hres1 Hbt1 Hst1 Hsrc) as Hd1.
  (* applicative equivalence *)
  assert (Hyu : y ∈ world_dom (wu : WorldT)) by set_solver.
  assert (Hclu : wfworld_closed_on (fv_value v1 ∪ {[y]}) wu).
  { eapply wfworld_closed_on_mono; [ |exact (basic_world_formula_wfworld_closed_on_dom _ _ Hbwu)].
    set_solver. }
  destruct (Happ wu y HyL Hyu Hclu) as [Heq Htot].
  assert (Hlcapp : lc_tm (tapp_tm (tret v2) (vfvar y))).
  { apply lc_tapp_tm; [constructor; exact Hlc2|constructor]. }
  assert (Hzero2 : wu ⊨ ty_denote_gas 0 Σ τa (tapp_tm (tret v2) (vfvar y))).
  {
    eapply ty_denote_gas_zero_transport_static_tm_equiv; [exact Heq|exact Htot|exact Hst2u|exact Hlcapp| | ].
    - eapply ty_static_guard_fv_tm_subset. exact Hst2u.
    - apply ty_denote_gas_zero_of_guard. exact (ty_denote_gas_guard _ _ _ _ _ Hd1).
  }
  assert (Hd2 : wu ⊨ ty_denote_gas g Σ τa (tapp_tm (tret v2) (vfvar y))).
  {
    eapply ty_denote_gas_tm_equiv; [ |exact Hd1].
    split; [exact Heq| ]. split; [exact Htot| ]. split; [ |exact Hzero2].
    apply ty_denote_gas_zero_of_guard. exact (ty_denote_gas_guard _ _ _ _ _ Hd1).
  }
  assert (Hd2f : wf ⊨ ty_denote_gas g Σ τa (tapp_tm (tret v2) (vfvar y))).
  {
    eapply res_models_projection; [ |exact Hd2].
    pose proof (formula_fv_ty_denote_gas_subset_relevant g Σ τa (tapp_tm (tret v2) (vfvar y))) as Hfvφ.
    assert (Hzφ : z ∉ formula_fv (ty_denote_gas g Σ τa (tapp_tm (tret v2) (vfvar y)))).
    { intros Hin. apply Hfvφ in Hin. unfold tapp_tm in Hin. cbn [fv_tm fv_value] in Hin.
      rewrite value_shift_fv in Hin. set_solver. }
    subst wu wf. rewrite !ext_swapc_restrict_off by exact Hzφ. reflexivity.
  }
  exact (ty_denote_gas_tapp_fun_result_alias_from_static
    g Σ τa v2 y z s wf HzΣ Hzfresh2 Hy Hlc2 Hres2 Hbt2 Hst2 Hd2f).
Qed.

Lemma ext_bw_insert (Σ1 Σ2 : lty_env) y T (w : WfWorldT) :
  w ⊨ basic_world_formula Σ1 -> w ⊨ basic_world_formula Σ2 ->
  Σ2 !! LVFree y = Some T ->
  w ⊨ basic_world_formula (<[LVFree y := T]> Σ1).
Proof.
  intros H1 H2 Hy.
  apply basic_world_formula_models_iff in H1 as [Hlc1' [Hsc1 [Hd1 Ht1]]].
  apply basic_world_formula_models_iff in H2 as [Hlc2' [Hsc2 [Hd2 Ht2]]].
  assert (HyΣ2 : LVFree y ∈ dom Σ2) by (apply elem_of_dom; eauto).
  apply basic_world_formula_models_iff. split; [ |split; [ |split]].
  - intros lv Hlv. rewrite dom_insert_L in Hlv. apply elem_of_union in Hlv as [Hlv|Hlv].
    + apply elem_of_singleton in Hlv as ->. apply Hlc2'. exact HyΣ2.
    + apply Hlc1'. exact Hlv.
  - rewrite ext_lvars_fv_insert. intros a Ha. apply elem_of_union in Ha as [Ha|Ha].
    + apply elem_of_singleton in Ha as ->. apply Hsc2. apply lvars_fv_elem. exact HyΣ2.
    + apply Hsc1. exact Ha.
  - rewrite dom_insert_L. intros lv Hlv. apply elem_of_union in Hlv as [Hlv|Hlv].
    + apply elem_of_singleton in Hlv as ->. apply Hd2. exact HyΣ2.
    + apply Hd1. exact Hlv.
  - intros σ Hσ x T' u Hx Hu.
    destruct (decide (x = LVFree y)) as [->|Hne].
    + rewrite lookup_insert_eq in Hx. injection Hx as <-.
      exact (Ht2 σ Hσ (LVFree y) T u Hy Hu).
    + rewrite lookup_insert_ne in Hx by congruence.
      exact (Ht1 σ Hσ x T' u Hx Hu).
Qed.

Lemma ext_bctl_arrow D τx τr :
  lc_lvars D ->
  (basic_context_ty_lvars D (CTArrow τx τr) \/ basic_context_ty_lvars D (CTWand τx τr)) ->
  basic_context_ty_lvars D τx /\ context_ty_lvars_at 1 τr ⊆ D /\ context_ty_shape_ok τr /\
  lc_context_ty τx /\ cty_lc_at 1 τr.
Proof.
  intros HlcD Hτ.
  assert (Hlc : lc_context_ty τx /\ cty_lc_at 1 τr).
  { destruct Hτ as [Hτ|Hτ]; pose proof (basic_context_ty_lvars_lc D _ HlcD Hτ) as H;
      exact H. }
  destruct Hτ as [[Hv [Hs1 Hs2]]|[Hv [Hs1 Hs2]]];
    cbn [context_ty_lvars context_ty_lvars_at] in Hv; unfold context_ty_lvars in *;
    (split; [split; [set_solver|exact Hs1]| ]; split; [set_solver| ];
     split; [exact Hs2|exact Hlc]).
Qed.

Lemma ext_bctl_open D τr y :
  lc_lvars D -> LVFree y ∉ D ->
  context_ty_lvars_at 1 τr ⊆ D -> context_ty_shape_ok τr ->
  basic_context_ty_lvars ({[LVFree y]} ∪ D) (cty_open 0 y τr).
Proof.
  intros Hlc Hy Hsub Hsh. split.
  - pose proof (cty_lvars_open_body_closed_no_fresh D τr y Hlc Hy Hsub) as H.
    intros lv Hlv. destruct (decide (lv = LVFree y)) as [->|Hne]; [set_solver| ].
    apply elem_of_union_r. apply Hsub. apply H. set_solver.
  - apply context_ty_shape_ok_open. exact Hsh.
Qed.

Lemma ext_fv_cty_from_bctl D τ :
  basic_context_ty_lvars D τ -> fv_cty τ ⊆ lvars_fv D.
Proof.
  intros [Hv _] a Ha. apply lvars_fv_elem. apply Hv.
  apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Ha.
Qed.

Lemma ext_vt_arrow_body g Σg τx τr z (m : WfWorldT) :
  lty_env_closed Σg -> LVFree z ∉ dom Σg -> z ∉ world_dom (m : WorldT) ->
  z ∉ fv_value v1 -> z ∉ fv_cty τx -> z ∉ fv_cty τr ->
  lvars_fv (dom Σg) ⊆ world_dom (m : WorldT) ->
  m ⊨ basic_world_formula Σg ->
  basic_tm_has_ltype Σg (tret v1) (erase_ty (CTArrow τx τr)) ->
  basic_tm_has_ltype Σg (tret v2) (erase_ty (CTArrow τx τr)) ->
  basic_context_ty_lvars (dom Σg) (CTArrow τx τr) ->
  ext_swapc m z v1 ⊨ arrow_value_denote_gas_with ty_denote_gas g
    (<[LVFree z := erase_ty (CTArrow τx τr)]> Σg) τx τr (tret (vfvar z)) ->
  ext_swapc m z v2 ⊨ arrow_value_denote_gas_with ty_denote_gas g
    (<[LVFree z := erase_ty (CTArrow τx τr)]> Σg) τx τr (tret (vfvar z)).
Proof.
  intros Hcl HzΣ Hzm Hz1 Hzx Hzr Hdomm Hbw Hty1 Hty2 Hτ Hsrc.
  assert (Hz2 : z ∉ fv_value v2) by (rewrite <- Hfv12; exact Hz1).
  destruct (ext_bctl_arrow _ τx τr Hcl (or_introl Hτ)) as [Hτx [Hτr1 [Hshr [Hlcx Hlcr]]]].
  pose proof (ext_typing_fv _ _ _ Hty1) as Hfv1. cbn [fv_tm] in Hfv1.
  pose proof (ext_typing_fv _ _ _ Hty2) as Hfv2. cbn [fv_tm] in Hfv2.
  pose proof (ext_fv_cty_from_bctl _ _ Hτx) as Hfvx.
  pose proof (basic_world_formula_wfworld_closed_on_dom _ _ Hbw) as Hclm.
  set (Tf := erase_ty (CTArrow τx τr)) in *.
  set (Tx := erase_ty τx).
  set (Σz := <[LVFree z := Tf]> Σg).
  assert (HclΣz : lty_env_closed Σz) by (apply lty_env_closed_insert_free; exact Hcl).
  set (mu := ext_swapc m z v1) in *. set (mf := ext_swapc m z v2).
  cbn [arrow_value_denote_gas_with] in Hsrc |- *. fold Σz in Hsrc |- *.
  set (P := ty_denote_gas g (typed_lty_env_bind Σz (erase_ty τx)) (cty_shift 0 τx) (tret (vbvar 0))) in *.
  set (Q := ty_denote_gas g (typed_lty_env_bind Σz (erase_ty τx)) τr
    (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0))) in *.
  assert (Hdommf : world_dom (mf : WorldT) = world_dom (m : WorldT) ∪ {[z]}) by apply ext_swapc_dom.
  assert (Hdommu : world_dom (mu : WorldT) = world_dom (m : WorldT) ∪ {[z]}) by apply ext_swapc_dom.
  assert (Hscope : formula_scoped_in_world mf (FForall (FImpl P Q))).
  { pose proof (res_models_scoped _ _ Hsrc) as Hs. unfold formula_scoped_in_world in *.
    rewrite Hdommf. rewrite Hdommu in Hs. exact Hs. }
  assert (Hres2 : mf ⊨ expr_result_formula (tret v2) (LVFree z)).
  { apply ext_swapc_result; try assumption; [set_solver| ].
    eapply wfworld_closed_on_mono; [ |exact Hclm]. exact Hfv2. }
  eapply res_models_forall_rev_intro; [exact Hscope| ].
  exists (Lapp ∪ world_dom (m : WorldT) ∪ {[z]} ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τr ∪
    lvars_fv (dom Σg)).
  intros y Hy myf Hdomy Hrestry.
  assert (HyL : y ∉ Lapp) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hyz : y <> z) by set_solver.
  assert (Hyx : y ∉ fv_cty τx) by set_solver.
  assert (Hyr : y ∉ fv_cty τr) by set_solver.
  assert (HyΣg : LVFree y ∉ dom Σg).
  { intros Hin. apply Hy. apply elem_of_union_r. apply lvars_fv_elem. exact Hin. }
  assert (HyΣz : LVFree y ∉ dom Σz).
  { subst Σz. rewrite dom_insert_L. intros Hin. apply elem_of_union in Hin as [Hin|Hin];
      [apply elem_of_singleton in Hin; congruence|exact (HyΣg Hin)]. }
  assert (Hle : mf ⊑ myf) by (rewrite <- Hrestry; apply res_restrict_le).
  pose proof (formula_scoped_forall_open_res_le mf myf y _ Hscope Hle
    (opened_world_dom_contains_slot mf myf y Hdomy)) as Hosc.
  rewrite formula_open_impl in Hosc |- *.
  eapply res_models_impl_intro; [exact Hosc| ].
  intros HPf.
  assert (HPeq : formula_open 0 y P =
      ty_denote_gas g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y))).
  { subst P. apply formula_open_ty_denote_gas_bind_ret_bvar0; assumption. }
  assert (HQeq : formula_open 0 y Q =
      ty_denote_gas g (<[LVFree y := Tx]> Σz) (cty_open 0 y τr)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  { subst Q. apply formula_open_ty_denote_gas_bind_tapp_shift_bvar0; try assumption.
    - cbn [fv_tm fv_value]. set_solver.
    - constructor. constructor. }
  change (myf ⊨ formula_open 0 y P) in HPf. change (myf ⊨ formula_open 0 y Q).
  rewrite HPeq in HPf. rewrite HQeq.
  set (n := res_restrict myf (world_dom (m : WorldT) ∪ {[y]})).
  assert (Hdomn : world_dom (n : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
  { subst n. rewrite res_restrict_dom, Hdomy, Hdommf. set_solver. }
  assert (Hzn : z ∉ world_dom (n : WorldT)) by (rewrite Hdomn; set_solver).
  assert (Hmyf : myf = ext_swapc n z v2).
  {
    assert (Hresy : myf ⊨ expr_result_formula (tret v2) (LVFree z))
      by (eapply res_models_kripke; [exact Hle|exact Hres2]).
    assert (Hcly : wfworld_closed_on (fv_value v2) myf).
    { eapply wfworld_closed_on_le; [ |exact Hle| ].
      - rewrite Hdommf. set_solver.
      - subst mf. eapply wfworld_closed_on_le; [ |apply ext_swapc_le; exact Hzm| ].
        + set_solver.
        + eapply wfworld_closed_on_mono; [ |exact Hclm]. exact Hfv2. }
    rewrite (ext_result_swapc myf z v2 Hz2 Hlc2 Hcly Hresy) at 1.
    subst n. f_equal. f_equal. rewrite Hdomy, Hdommf. apply set_eq. intros a.
    destruct (decide (a = z)); destruct (decide (a = y)); set_solver.
  }
  assert (Hnm : res_restrict n (world_dom (m : WorldT)) = m).
  {
    subst n. rewrite res_restrict_restrict_eq.
    replace ((world_dom (m : WorldT) ∪ {[y]}) ∩ world_dom (m : WorldT))
      with (world_dom (mf : WorldT) ∩ world_dom (m : WorldT)) by (rewrite Hdommf; set_solver).
    rewrite <- res_restrict_restrict_eq, Hrestry.
    subst mf. rewrite ext_swapc_restrict_off by exact Hzm. apply ext_restrict_self.
  }
  set (myu := ext_swapc n z v1).
  assert (Hdomyu : world_dom (myu : WorldT) = world_dom (mu : WorldT) ∪ {[y]}).
  { subst myu. rewrite ext_swapc_dom, Hdomn, Hdommu. set_solver. }
  assert (Hrestryu : res_restrict myu (world_dom (mu : WorldT)) = mu).
  {
    subst myu. rewrite Hdommu, ext_swapc_restrict_on by set_solver.
    subst mu. f_equal.
    rewrite <- Hnm at 2. subst n. rewrite !res_restrict_restrict_eq. f_equal.
    apply set_eq. intros a. destruct (decide (a = z)); destruct (decide (a = y)); set_solver.
  }
  assert (HPu : myu ⊨ ty_denote_gas g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y))).
  {
    eapply res_models_projection; [ |exact HPf].
    pose proof (formula_fv_ty_denote_gas_subset_relevant g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y))) as Hfvφ.
    assert (Hzφ : z ∉ formula_fv (ty_denote_gas g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y)))).
    { intros Hin. apply Hfvφ in Hin. cbn [fv_tm fv_value] in Hin. set_solver. }
    rewrite Hmyf. subst myu. rewrite !ext_swapc_restrict_off by exact Hzφ. reflexivity.
  }
  assert (Hymu : y ∉ world_dom (mu : WorldT)) by (rewrite Hdommu; set_solver).
  pose proof (result_first_forall_impl_open_elim mu myu y P Q Hsrc Hymu Hdomyu Hrestryu
    ltac:(rewrite HPeq; exact HPu)) as HQu.
  rewrite HQeq in HQu.
  (* rearrange the environment for the application swap *)
  assert (Henv : <[LVFree y := Tx]> Σz =
      <[LVFree z := Tx →ₜ erase_ty (cty_open 0 y τr)]> (<[LVFree y := Tx]> Σg)).
  { subst Σz Tf. rewrite cty_open_preserves_erasure.
    apply lty_env_insert_free_commute. exact Hyz. }
  rewrite Henv in HQu |- *.
  rewrite Hmyf.
  assert (HrelΣ2 : n ⊨ basic_world_formula
      (relevant_env (<[LVFree y := Tx]> Σz) τx (tret (vfvar y)))).
  {
    pose proof (ty_denote_gas_guard_formula _ _ _ _ _ HPf) as Hg.
    destruct (ext_guard_parts _ _ _ _ Hg) as [_ [Hsc2 [Hbw2 _]]].
    assert (Hfvsub : formula_fv (basic_world_formula
        (relevant_env (<[LVFree y := Tx]> Σz) τx (tret (vfvar y)))) ⊆
        world_dom (m : WorldT) ∪ {[y]}).
    { rewrite formula_fv_basic_world_formula.
      unfold relevant_env, lty_env_restrict_lvars. rewrite storeA_restrict_dom.
      intros a Ha. apply lvars_fv_elem in Ha. apply elem_of_intersection in Ha as [_ Ha].
      apply elem_of_union in Ha as [Ha|Ha].
      + apply elem_of_union_l. apply Hdomm. apply Hfvx.
        rewrite <- context_ty_lvars_fv. apply lvars_fv_elem. exact Ha.
      + cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at] in Ha.
        apply elem_of_singleton in Ha. inversion Ha. set_solver. }
    subst n. apply (proj1 (res_models_minimal_on _ myf _ Hfvsub)). exact Hbw2.
  }
  assert (Hmn : m ⊑ n) by (rewrite <- Hnm; apply res_restrict_le).
  assert (Hsub : Σg ⊆ <[LVFree y := Tx]> Σg).
  { apply insert_subseteq. apply not_elem_of_dom. exact HyΣg. }
  assert (HTf : Tf = Tx →ₜ erase_ty (cty_open 0 y τr)).
  { subst Tf Tx. rewrite cty_open_preserves_erasure. reflexivity. }
  apply (ext_vt_cs_app g (<[LVFree y := Tx]> Σg) (cty_open 0 y τr) Tx y z n); try assumption.
  - apply lty_env_closed_insert_free. exact Hcl.
  - rewrite dom_insert_L. intros Hin. apply elem_of_union in Hin as [Hin|Hin];
      [apply elem_of_singleton in Hin; congruence|exact (HzΣ Hin)].
  - congruence.
  - pose proof (cty_open_fv_subset 0 y τr). set_solver.
  - apply lookup_insert_eq.
  - rewrite ext_lvars_fv_insert, Hdomn. set_solver.
  - eapply ext_bw_insert; [eapply res_models_kripke; [exact Hmn|exact Hbw]|exact HrelΣ2| ].
    unfold relevant_env, lty_env_restrict_lvars.
    apply storeA_restrict_lookup_some_2; [apply lookup_insert_eq| ].
    apply elem_of_union_r. cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at]. set_solver.
  - rewrite <- HTf. eapply basic_tm_has_ltype_weaken; [exact Hty1|exact Hsub].
  - rewrite <- HTf. eapply basic_tm_has_ltype_weaken; [exact Hty2|exact Hsub].
  - rewrite dom_insert_L. apply ext_bctl_open; assumption.
Qed.

Lemma ext_open_env_atoms_one y :
  open_env_atoms (<[0%nat := y]> (∅ : gmap nat atom)) = {[y]}.
Proof.
  rewrite open_env_atoms_insert by apply lookup_empty.
  rewrite open_env_atoms_empty. set_solver.
Qed.

Lemma ext_product_dropz (m' w : WfWorldT) z v Hc Hc2 :
  res_product m' (ext_swapc w z v) Hc =
  res_product (res_restrict m' (world_dom (m' : WorldT) ∖ {[z]})) (ext_swapc w z v) Hc2.
Proof.
  destruct (decide (z ∈ world_dom (m' : WorldT))) as [Hz|Hz].
  - apply ext_product_absorb. exact Hz.
  - apply res_product_l_eq. rewrite <- (ext_restrict_self m') at 1.
    f_equal. set_solver.
Qed.

Lemma ext_vt_wand_body g Σg τx τr z (m : WfWorldT) :
  lty_env_closed Σg -> LVFree z ∉ dom Σg -> z ∉ world_dom (m : WorldT) ->
  z ∉ fv_value v1 -> z ∉ fv_cty τx -> z ∉ fv_cty τr ->
  lvars_fv (dom Σg) ⊆ world_dom (m : WorldT) ->
  m ⊨ basic_world_formula Σg ->
  basic_tm_has_ltype Σg (tret v1) (erase_ty (CTWand τx τr)) ->
  basic_tm_has_ltype Σg (tret v2) (erase_ty (CTWand τx τr)) ->
  basic_context_ty_lvars (dom Σg) (CTWand τx τr) ->
  ext_swapc m z v1 ⊨ wand_value_denote_gas_with ty_denote_gas g
    (<[LVFree z := erase_ty (CTWand τx τr)]> Σg) τx τr (tret (vfvar z)) ->
  ext_swapc m z v2 ⊨ wand_value_denote_gas_with ty_denote_gas g
    (<[LVFree z := erase_ty (CTWand τx τr)]> Σg) τx τr (tret (vfvar z)).
Proof.
  intros Hcl HzΣ Hzm Hz1 Hzx Hzr Hdomm Hbw Hty1 Hty2 Hτ Hsrc.
  assert (Hz2 : z ∉ fv_value v2) by (rewrite <- Hfv12; exact Hz1).
  destruct (ext_bctl_arrow _ τx τr Hcl (or_intror Hτ)) as [Hτx [Hτr1 [Hshr [Hlcx Hlcr]]]].
  pose proof (ext_typing_fv _ _ _ Hty1) as Hfv1. cbn [fv_tm] in Hfv1.
  pose proof (ext_fv_cty_from_bctl _ _ Hτx) as Hfvx.
  set (Tf := erase_ty (CTWand τx τr)) in *.
  set (Tx := erase_ty τx).
  set (Σz := <[LVFree z := Tf]> Σg).
  assert (HclΣz : lty_env_closed Σz) by (apply lty_env_closed_insert_free; exact Hcl).
  set (mu := ext_swapc m z v1) in *. set (mf := ext_swapc m z v2).
  cbn [wand_value_denote_gas_with] in Hsrc |- *. fold Σz in Hsrc |- *.
  set (P := ty_denote_gas g (typed_lty_env_bind Σz (erase_ty τx)) (cty_shift 0 τx) (tret (vbvar 0))) in *.
  set (Q := ty_denote_gas g (typed_lty_env_bind Σz (erase_ty τx)) τr
    (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0))) in *.
  assert (Hdommf : world_dom (mf : WorldT) = world_dom (m : WorldT) ∪ {[z]}) by apply ext_swapc_dom.
  assert (Hdommu : world_dom (mu : WorldT) = world_dom (m : WorldT) ∪ {[z]}) by apply ext_swapc_dom.
  assert (Hscope : formula_scoped_in_world mf (FBWand 1 P Q)).
  { pose proof (res_models_scoped _ _ Hsrc) as Hs. unfold formula_scoped_in_world in *.
    rewrite Hdommf. rewrite Hdommu in Hs. exact Hs. }
  apply res_models_fbwand_intro; [exact Hscope| ].
  exists (Lapp ∪ world_dom (m : WorldT) ∪ {[z]} ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τr ∪
    lvars_fv (dom Σg)).
  intros η m' Hc Hbind Hfresh Hdomp HPf.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
  rewrite ext_open_env_atoms_one in Hfresh, Hdomp.
  rewrite !formula_open_env_singleton in HPf |- *.
  assert (Hy : y ∉ Lapp ∪ world_dom (m : WorldT) ∪ {[z]} ∪ fv_value v1 ∪ fv_cty τx ∪
    fv_cty τr ∪ lvars_fv (dom Σg)) by set_solver.
  assert (HyL : y ∉ Lapp) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hyz : y <> z) by set_solver.
  assert (Hyx : y ∉ fv_cty τx) by set_solver.
  assert (Hyr : y ∉ fv_cty τr) by set_solver.
  assert (HyΣg : LVFree y ∉ dom Σg).
  { intros Hin. apply Hy. apply elem_of_union_r. apply lvars_fv_elem. exact Hin. }
  assert (HyΣz : LVFree y ∉ dom Σz).
  { subst Σz. rewrite dom_insert_L. intros Hin. apply elem_of_union in Hin as [Hin|Hin];
      [apply elem_of_singleton in Hin; congruence|exact (HyΣg Hin)]. }
  assert (HPeq : formula_open 0 y P =
      ty_denote_gas g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y))).
  { subst P. apply formula_open_ty_denote_gas_bind_ret_bvar0; assumption. }
  assert (HQeq : formula_open 0 y Q =
      ty_denote_gas g (<[LVFree y := Tx]> Σz) (cty_open 0 y τr)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  { subst Q. apply formula_open_ty_denote_gas_bind_tapp_shift_bvar0; try assumption.
    - cbn [fv_tm fv_value]. set_solver.
    - constructor. constructor. }
  change (m' ⊨ formula_open 0 y P) in HPf.
  change (res_product m' mf Hc ⊨ formula_open 0 y Q).
  rewrite HPeq in HPf. rewrite HQeq.
  rewrite res_product_dom, Hdommf in Hdomp.
  assert (Hym' : y ∈ world_dom (m' : WorldT)) by set_solver.
  set (m'' := res_restrict m' (world_dom (m' : WorldT) ∖ {[z]})).
  assert (Hdom'' : world_dom (m'' : WorldT) = world_dom (m' : WorldT) ∖ {[z]})
    by (subst m''; rewrite res_restrict_dom; set_solver).
  assert (Hz'' : z ∉ world_dom (m'' : WorldT)) by (rewrite Hdom''; set_solver).
  assert (Hc''u : world_compat (m'' : WorldT) (mu : WorldT)).
  { subst m'' mu. eapply ext_swapc_compat_restrict; [ |exact Hc]. set_solver. }
  assert (Hc''f : world_compat (m'' : WorldT) (mf : WorldT)).
  { subst m'' mf. eapply ext_swapc_compat_restrict; [ |exact Hc]. set_solver. }
  assert (Hc0 : world_compat (m'' : WorldT) (m : WorldT)).
  { eapply ext_swapc_compat_base; [exact Hz''|exact Hc''u]. }
  set (n := res_product m'' m Hc0).
  assert (Hfvm : fv_value v1 ⊆ world_dom (m : WorldT)) by set_solver.
  assert (Hfvm2 : fv_value v2 ⊆ world_dom (m : WorldT)) by (rewrite <- Hfv12; exact Hfvm).
  assert (Hnu : res_product m'' mu Hc''u = ext_swapc n z v1).
  { subst mu n. apply ext_swapc_product; assumption. }
  assert (Hnf : res_product m' mf Hc = ext_swapc n z v2).
  { change (res_product m' (ext_swapc m z v2) Hc = ext_swapc n z v2).
    rewrite (ext_product_dropz m' m z v2 Hc Hc''f).
    subst n. apply ext_swapc_product; assumption. }
  assert (HPfv : formula_fv (ty_denote_gas g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y))) ⊆
      world_dom (m' : WorldT) ∖ {[z]}).
  { pose proof (res_models_scoped _ _ HPf) as Hs. unfold formula_scoped_in_world in Hs.
    pose proof (formula_fv_ty_denote_gas_subset_relevant g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y))) as Hfvφ.
    intros a Ha. apply elem_of_difference. split; [exact (Hs a Ha)| ].
    apply Hfvφ in Ha. cbn [fv_tm fv_value] in Ha. set_solver. }
  assert (HP'' : m'' ⊨ ty_denote_gas g (<[LVFree y := Tx]> Σz) τx (tret (vfvar y))).
  { subst m''. apply (proj1 (res_models_minimal_on _ m' _ HPfv)). exact HPf. }
  assert (Hdomu : world_dom (res_product m'' mu Hc''u : WorldT) = world_dom (mu : WorldT) ∪ {[y]}).
  { rewrite res_product_dom, Hdom'', Hdommu. apply set_eq. intros a.
    destruct (decide (a = z)); set_solver. }
  assert (Hymu : y ∉ world_dom (mu : WorldT)) by (rewrite Hdommu; set_solver).
  pose proof (res_models_fbwand_open_one_named_fresh mu m'' y P Q Hc''u Hsrc Hymu Hdomu
    ltac:(rewrite HPeq; exact HP'')) as HQu.
  rewrite HQeq, Hnu in HQu. rewrite Hnf.
  assert (Henv : <[LVFree y := Tx]> Σz =
      <[LVFree z := Tx →ₜ erase_ty (cty_open 0 y τr)]> (<[LVFree y := Tx]> Σg)).
  { subst Σz Tf. rewrite cty_open_preserves_erasure.
    apply lty_env_insert_free_commute. exact Hyz. }
  rewrite Henv in HQu |- *.
  assert (Hmn : m ⊑ n) by (subst n; apply res_product_le_r).
  assert (Hm''n : m'' ⊑ n) by (subst n; apply res_product_le_l).
  assert (Hdomn : world_dom (n : WorldT) = world_dom (m'' : WorldT) ∪ world_dom (m : WorldT))
    by (subst n; apply res_product_dom).
  assert (HrelΣ2 : n ⊨ basic_world_formula
      (relevant_env (<[LVFree y := Tx]> Σz) τx (tret (vfvar y)))).
  {
    pose proof (ty_denote_gas_guard_formula _ _ _ _ _ HP'') as Hg.
    destruct (ext_guard_parts _ _ _ _ Hg) as [_ [_ [Hbw2 _]]].
    eapply res_models_kripke; [exact Hm''n|exact Hbw2].
  }
  assert (Hsub : Σg ⊆ <[LVFree y := Tx]> Σg).
  { apply insert_subseteq. apply not_elem_of_dom. exact HyΣg. }
  assert (HTf : Tf = Tx →ₜ erase_ty (cty_open 0 y τr)).
  { subst Tf Tx. rewrite cty_open_preserves_erasure. reflexivity. }
  apply (ext_vt_cs_app g (<[LVFree y := Tx]> Σg) (cty_open 0 y τr) Tx y z n); try assumption.
  - apply lty_env_closed_insert_free. exact Hcl.
  - rewrite dom_insert_L. intros Hin. apply elem_of_union in Hin as [Hin|Hin];
      [apply elem_of_singleton in Hin; congruence|exact (HzΣ Hin)].
  - rewrite Hdomn. set_solver.
  - congruence.
  - pose proof (cty_open_fv_subset 0 y τr). set_solver.
  - apply lookup_insert_eq.
  - rewrite ext_lvars_fv_insert, Hdomn, Hdom''. set_solver.
  - eapply ext_bw_insert; [eapply res_models_kripke; [exact Hmn|exact Hbw]|exact HrelΣ2| ].
    unfold relevant_env, lty_env_restrict_lvars.
    apply storeA_restrict_lookup_some_2; [apply lookup_insert_eq| ].
    apply elem_of_union_r. cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at]. set_solver.
  - rewrite <- HTf. eapply basic_tm_has_ltype_weaken; [exact Hty1|exact Hsub].
  - rewrite <- HTf. eapply basic_tm_has_ltype_weaken; [exact Hty2|exact Hsub].
  - rewrite dom_insert_L. apply ext_bctl_open; assumption.
Qed.

Hypothesis Hnotbase : forall Σ b, basic_tm_has_ltype Σ (tret v1) (TBase b) -> False.

Lemma ext_open_bind_ret z g Σ T τ :
  lty_env_closed Σ -> LVFree z ∉ dom Σ -> z ∉ fv_cty τ -> lc_context_ty τ ->
  T = erase_ty τ ->
  formula_open 0 z (ty_denote_gas g (typed_lty_env_bind Σ T) (cty_shift 0 τ) (tret (vbvar 0))) =
  ty_denote_gas g (<[LVFree z := T]> Σ) τ (tret (vfvar z)).
Proof. intros ? ? ? ? ->. apply formula_open_ty_denote_gas_bind_ret_bvar0; assumption. Qed.

Lemma ext_vt_main τ : forall g Δ (m : WfWorldT),
  basic_tm_has_ltype Δ (tret v2) (erase_ty τ) ->
  m ⊨ ty_denote_gas g Δ τ (tret v1) ->
  m ⊨ ty_denote_gas g Δ τ (tret v2).
Proof.
  induction τ as [b φ|b φ|τ1 IH1 τ2 IH2|τ1 IH1 τ2 IH2|τ1 IH1 τ2 IH2
    |τx IHx τr IHr|τx IHx τr IHr|τ1 IH1];
    intros g Δ m Hty Hden; (destruct g as [ |g]; [eapply ext_vt_zero; eassumption| ]).
  all: pose proof (ty_denote_gas_guard_formula _ _ _ _ _ Hden) as Hg.
  all: destruct (ext_guard_parts _ _ _ _ Hg) as [Hcl [Hdomm [Hbw [Hty1 Hτ]]]].
  all: assert (Hzero2 : m ⊨ ty_denote_gas 0 Δ _ (tret v2)) by
         (eapply ext_vt_zero; [apply ty_denote_gas_zero_of_guard; exact Hg|exact Hty]).
  all: pose proof (ty_denote_gas_scope_from_zero_any (S g) _ _ _ m Hzero2) as Hscope.
  all: cbn [ty_denote_gas] in Hden, Hscope |- *.
  all: rewrite res_models_and_iff in Hden |- *.
  all: apply (proj1 (formula_scoped_and_iff _ _ _)) in Hscope as [_ Hscope].
  all: destruct Hden as [_ Hbody].
  all: split; [eapply ext_vt_guard; eassumption| ].
  all: match type of Hg with
       | _ ⊨ ty_guard_formula _ ?τ _ =>
           pose proof (ext_vt_typing_restrict Δ τ _ Hty) as Hty2;
           rewrite <- ext_vt_relevant in Hty2;
           try rewrite <- ext_vt_relevant in Hscope;
           try rewrite <- ext_vt_relevant;
           set (Σg := relevant_env Δ τ (tret v1)) in *
       end.
  - exfalso. exact (Hnotbase _ _ Hty1).
  - exfalso. exact (Hnotbase _ _ Hty1).
  - (* inter *)
    destruct (ext_bctl_binary _ τ1 τ2 (or_intror (or_introl Hτ))) as [_ [_ He12]].
    cbn [erase_ty] in Hty.
    rewrite res_models_and_iff in Hbody |- *. destruct Hbody as [Hb1 Hb2].
    split; [apply IH1; assumption| ].
    apply IH2; [rewrite <- He12; exact Hty|exact Hb2].
  - (* union *)
    destruct (ext_bctl_binary _ τ1 τ2 (or_intror (or_intror Hτ))) as [_ [_ He12]].
    cbn [erase_ty] in Hty.
    apply (proj1 (res_models_or_iff _ _ _ (res_models_scoped _ _ Hbody))) in Hbody.
    apply (res_models_or_iff _ _ _ Hscope).
    destruct Hbody as [Hb1|Hb2]; [left; apply IH1; assumption| ].
    right. apply IH2; [rewrite <- He12; exact Hty|exact Hb2].
  - (* sum *)
    destruct (ext_bctl_binary _ τ1 τ2 (or_introl Hτ)) as [Hτ1 [Hτ2 He12]].
    pose proof (basic_context_ty_lvars_lc _ _ Hcl Hτ1) as Hlcτ1.
    pose proof (basic_context_ty_lvars_lc _ _ Hcl Hτ2) as Hlcτ2.
    apply (ext_vt_forall_swap Σg (CTSum τ1 τ2) m _ Hg Hscope); [ |exact Hbody].
    exists (lvars_fv (dom Σg) ∪ fv_value v1 ∪ fv_cty τ1 ∪ fv_cty τ2).
    intros z Hz Hzm Hu.
    assert (HzΣ : LVFree z ∉ dom Σg) by (intros Hin; apply Hz; apply elem_of_union_l;
      apply elem_of_union_l; apply elem_of_union_l; apply lvars_fv_elem; exact Hin).
    rewrite formula_open_plus in Hu |- *.
    rewrite (ext_open_bind_ret z g Σg (erase_ty τ1) τ1) in Hu |- * by (try assumption; try reflexivity; set_solver).
    rewrite (ext_open_bind_ret z g Σg (erase_ty τ1) τ2) in Hu |- * by (try assumption; set_solver).
    apply (ext_vt_sum_body g Σg τ1 τ2 z m (IH1 g) (IH2 g)); try assumption; set_solver.
  - (* arrow *)
    destruct (ext_bctl_arrow _ τx τr Hcl (or_introl Hτ)) as [_ [_ [_ [Hlcx Hlcr]]]].
    apply (ext_vt_forall_swap Σg (CTArrow τx τr) m _ Hg Hscope); [ |exact Hbody].
    exists (lvars_fv (dom Σg) ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τr).
    intros z Hz Hzm Hu.
    assert (HzΣ : LVFree z ∉ dom Σg) by (intros Hin; apply Hz; apply elem_of_union_l;
      apply elem_of_union_l; apply elem_of_union_l; apply lvars_fv_elem; exact Hin).
    rewrite formula_open_result_first_arrow_value_ret_bvar0 in Hu |- * by (try assumption; set_solver).
    apply (ext_vt_arrow_body g Σg τx τr z m); try assumption; set_solver.
  - (* wand *)
    destruct (ext_bctl_arrow _ τx τr Hcl (or_intror Hτ)) as [_ [_ [_ [Hlcx Hlcr]]]].
    apply (ext_vt_forall_swap Σg (CTWand τx τr) m _ Hg Hscope); [ |exact Hbody].
    exists (lvars_fv (dom Σg) ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τr).
    intros z Hz Hzm Hu.
    assert (HzΣ : LVFree z ∉ dom Σg) by (intros Hin; apply Hz; apply elem_of_union_l;
      apply elem_of_union_l; apply elem_of_union_l; apply lvars_fv_elem; exact Hin).
    rewrite formula_open_result_first_wand_value_ret_bvar0 in Hu |- * by (try assumption; set_solver).
    apply (ext_vt_wand_body g Σg τx τr z m); try assumption; set_solver.
  - (* persist *)
    assert (Hτ1 : basic_context_ty_lvars (dom Σg) τ1) by exact Hτ.
    pose proof (basic_context_ty_lvars_lc _ _ Hcl Hτ1) as Hlcτ1.
    apply (ext_vt_forall_swap Σg (CTPersist τ1) m _ Hg Hscope); [ |exact Hbody].
    exists (lvars_fv (dom Σg) ∪ fv_value v1 ∪ fv_cty τ1).
    intros z Hz Hzm Hu.
    assert (HzΣ : LVFree z ∉ dom Σg) by (intros Hin; apply Hz; apply elem_of_union_l;
      apply elem_of_union_l; apply lvars_fv_elem; exact Hin).
    rewrite formula_open_persist in Hu |- *.
    rewrite (ext_open_bind_ret z g Σg (erase_ty (CTPersist τ1)) τ1) in Hu |- * by (try assumption; try reflexivity; set_solver).
    apply (ext_vt_persist_body g Σg τ1 z m (IH1 g)); try assumption; set_solver.
Qed.
End ExtValueTransport.

Lemma ext_fv_close_value x v :
  lc_value v -> fv_value (close_value x 0 v) = fv_value v ∖ {[x]}.
Proof.
  intros Hlc. pose proof (close_rm_fv_value x 0 v) as Hx.
  pose proof (open_fv_value' (close_value x 0 v) (vfvar x) 0) as H1.
  pose proof (open_fv_value (close_value x 0 v) (vfvar x) 0) as H2.
  rewrite open_close_var_value in H1, H2 by exact Hlc. cbn [fv_value] in H2.
  apply set_eq. intros a. split; [set_solver| ].
  intros Ha. apply elem_of_difference in Ha as [Ha Hax]. apply H2 in Ha. set_solver.
Qed.

Lemma ext_fv_close_tm x e :
  lc_tm e -> fv_tm (close_tm x 0 e) = fv_tm e ∖ {[x]}.
Proof.
  intros Hlc. pose proof (close_rm_fv_tm x 0 e) as Hx.
  pose proof (open_fv_tm' (close_tm x 0 e) (vfvar x) 0) as H1.
  pose proof (open_fv_tm (close_tm x 0 e) (vfvar x) 0) as H2.
  rewrite open_close_var_tm in H1, H2 by exact Hlc. cbn [fv_value] in H2.
  apply set_eq. intros a. split; [set_solver| ].
  intros Ha. apply elem_of_difference in Ha as [Ha Hax]. apply H2 in Ha. set_solver.
Qed.

Lemma ext_fv_subst_lower x u e :
  lc_tm e -> lc_value u -> fv_tm e ∖ {[x]} ⊆ fv_tm (tm_subst x u e).
Proof.
  intros Hlc Hu.
  rewrite <- (open_close_var_tm x e Hlc) at 2.
  rewrite subst_intro_tm by (apply close_rm_fv_tm || exact Hu).
  rewrite <- ext_fv_close_tm by exact Hlc.
  apply open_fv_tm'.
Qed.

Lemma ext_fix_unfolding_fv self arg sx t body :
  lc_tm body ->
  fv_value (ext_fix_unfolding self arg sx t body) =
  fv_value (fixfun_named self arg sx t body).
Proof.
  intros Hb.
  set (fx := fixfun_named self arg sx t body).
  assert (Hfx_lc : lc_value fx) by (apply ext_fixfun_named_lc; exact Hb).
  assert (Hfx : fv_value fx = (fv_tm body ∖ {[self]}) ∖ {[arg]}).
  { subst fx. unfold fixfun_named. cbn [fv_value].
    rewrite ext_fv_close_value by (apply ext_lc_lam_named; exact Hb).
    unfold lam_named. cbn [fv_value]. rewrite ext_fv_close_tm by exact Hb. reflexivity. }
  assert (HS : lc_tm (tm_subst self fx body)) by (apply subst_lc_tm; assumption).
  unfold ext_fix_unfolding, lam_named. cbn [fv_value].
  rewrite ext_fv_close_tm by exact HS.
  pose proof (fv_of_subst_tm self fx body) as Hup.
  pose proof (ext_fv_subst_lower self fx body Hb Hfx_lc) as Hlow.
  fold fx in Hup, Hlow |- *.
  rewrite Hfx in *. apply set_eq. intros a. split; set_solver.
Qed.

Lemma ext_lam_not_base Σ s e b :
  basic_tm_has_ltype Σ (tret (vlam s e)) (TBase b) -> False.
Proof. intros H. inversion H; subst. match goal with H : basic_value_has_ltype _ _ _ |- _ => inversion H end. Qed.

(** The generalized shape: every target type.  Base types are vacuous (a
    function value has no base type), and [-∗], [⊕], [□] are handled by the
    world-level value transport [ext_vt_main]. *)
Fixpoint fix_unroll_shape_ext (τ : context_ty) : Prop :=
  match τ with
  | CTOver _ _ | CTUnder _ _ | CTArrow _ _ | CTWand _ _ => True
  | CTInter τ1 τ2 | CTUnion τ1 τ2 | CTSum τ1 τ2 =>
      fix_unroll_shape_ext τ1 /\ fix_unroll_shape_ext τ2
  | CTPersist τ1 => fix_unroll_shape_ext τ1
  end.

Lemma fix_unroll_shape_ext_all τ : fix_unroll_shape_ext τ.
Proof. induction τ; cbn [fix_unroll_shape_ext]; tauto. Qed.

Lemma fix_unroll_shape_ext_of_shape τ : fix_unroll_shape τ -> fix_unroll_shape_ext τ.
Proof. intros _. apply fix_unroll_shape_ext_all. Qed.

(** World-level transport: any denotation of the unfolding at any type is a
    denotation of the [fix] value. *)
Lemma ext_fix_unroll_value_transport self arg sx t body τ g Δ (m : WfWorldT) :
  lc_tm body ->
  basic_tm_has_ltype Δ (tret (fixfun_named self arg sx t body)) (erase_ty τ) ->
  m ⊨ ty_denote_gas g Δ τ (tret (ext_fix_unfolding self arg sx t body)) ->
  m ⊨ ty_denote_gas g Δ τ (tret (fixfun_named self arg sx t body)).
Proof.
  intros Hb Hty Hden.
  set (fx := fixfun_named self arg sx t body) in *.
  set (unf := ext_fix_unfolding self arg sx t body) in *.
  assert (Hfx_lc : lc_value fx) by (apply ext_fixfun_named_lc; exact Hb).
  assert (Hunf_lc : lc_value unf).
  { apply ext_lc_lam_named. apply subst_lc_tm; assumption. }
  apply (ext_vt_main unf fx Hunf_lc Hfx_lc (ext_fix_unfolding_fv self arg sx t body Hb)
    ({[self]} ∪ {[arg]} ∪ fv_value unf)); [ | | exact Hty | exact Hden].
  - intros n y Hy Hyn Hcl.
    assert (Hfveq : fv_value unf = fv_value fx) by exact (ext_fix_unfolding_fv self arg sx t body Hb).
    assert (Hcl' : wfworld_closed_on (fv_value fx ∪ fv_value unf ∪ {[y]}) n).
    { eapply wfworld_closed_on_mono; [ |exact Hcl]. rewrite Hfveq. set_solver. }
    destruct (ext_fix_unroll_tm_equiv n self arg sx t body y Hb
      ltac:(set_solver) ltac:(set_solver) ltac:(set_solver) Hyn Hcl') as [Heq Htot].
    fold fx unf in Heq, Htot.
    split.
    + intros σ v Hσ. symmetry. apply Heq. exact Hσ.
    + intros σ Hσ. symmetry. apply Htot. exact Hσ.
  - intros Σ0 b0 H. subst unf. unfold ext_fix_unfolding, lam_named in H.
    exact (ext_lam_not_base _ _ _ _ H).
Qed.

(** Soundness of T-FixUnroll for every target type (in particular for
    top-level [-∗], [⊕], [□] and their combinations with [⊓]/[∪]). *)
Theorem ext_fix_unroll_named_sound_ext Σ Γ self arg sx t body τ :
  fix_unroll_shape_ext τ ->
  lc_tm body ->
  context_typing_wf Σ Γ (tret (fixfun_named self arg sx t body)) τ ->
  context_typing_wf Σ Γ
    (tret (lam_named arg sx (tm_subst self (fixfun_named self arg sx t body) body))) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ
      (tret (lam_named arg sx (tm_subst self (fixfun_named self arg sx t body) body)))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tret (fixfun_named self arg sx t body)).
Proof.
  intros _ Hb Hwf_fix _ IH m Hctx.
  unfold ty_denote_under, ty_denote in IH |- *.
  apply ext_fix_unroll_value_transport; [exact Hb| |exact (IH m Hctx)].
  apply basic_tm_has_ltype_of_atom_env_typing.
  exact (context_typing_wf_basic_typing _ _ _ _ Hwf_fix).
Qed.
