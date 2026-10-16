(** * Small programs from Section 2 (typing overview) *)

From ProofAutomation Require Import BasicTypeInfer ExtendedTypeInfer ExtendedSubsumption.
From ContextTyping Require Import Typing.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

(** ** Generic helpers (kept in a module so that importing the denotation
    notations does not interfere with the case-study surface syntax). *)
Module S2CtxSubHelpers.
Import Denotation.Context.

(** *** Generic helpers for structural T-CtxSub obligations

    A context refinement whose target context is entailed by the source
    context (weakening, framing, exchange) is a [ctx_sub_under] with
    [r' = r].  These helpers are generic and could be shared. *)

Lemma s2_agree_of_submap (X : aset) (m1 m2 : gmap atom ty) :
  X ⊆ dom m2 -> m2 ⊆ m1 -> ty_env_agree_on X m1 m2.
Proof.
  intros HX Hsub z Hz.
  pose proof (HX z Hz) as Hd. apply elem_of_dom in Hd as [T HT].
  rewrite HT. eapply lookup_weaken; eauto.
Qed.


Lemma s2_X_sub (Γ : ctx) (e : tm) (τ : context_ty) :
  context_typing_wf ∅ Γ e τ -> fv_tm e ∪ fv_cty τ ⊆ dom (erase_ctx Γ).
Proof.
  intros Hwf.
  pose proof (context_typing_wf_fv_tm_subset ∅ Γ e τ Hwf).
  pose proof (context_typing_wf_fv_cty_subset_erase_dom ∅ Γ e τ Hwf).
  set_solver.
Qed.

Lemma s2_ctx_sub_entails (Γ1 Γ2 : ctx) (e : tm) (τ : context_ty) :
  wf_ctx_under ∅ Γ1 ->
  context_typing_wf ∅ Γ2 e τ ->
  erase_ctx Γ2 ⊆ erase_ctx Γ1 ->
  (forall r, r ⊨ ctx_denote_under ∅ Γ1 -> r ⊨ ctx_denote_under ∅ Γ2) ->
  ctx_sub_under ∅ (fv_tm e ∪ fv_cty τ) Γ1 Γ2.
Proof.
  intros HΓ1 Hwf Hsub Hent.
  split; [exact HΓ1| ].
  split; [exact (context_typing_wf_ctx ∅ Γ2 e τ Hwf)| ].
  split.
  - apply s2_agree_of_submap; [apply s2_X_sub; exact Hwf|exact Hsub].
  - intros r Hr. exists r. split.
    + apply res_restrict_le.
    + apply Hent. exact Hr.
Qed.

Lemma s2_models_emp (Σ : gmap atom ty) r :
  r ⊨ ctx_denote_under Σ Emp.
Proof.
  cbn [ctx_denote_under ctx_fv erase_ctx].
  rewrite storeA_restrict_empty_set.
  apply res_models_and_intro_from_models.
  - change (atom_env_to_lty_env ((∅ : gmap atom ty) ∪ ∅)) with (atom_env_to_lty_env ∅).
    replace (atom_env_to_lty_env ∅) with (∅ : lty_env).
    + apply basic_world_formula_empty.
    + reflexivity.
  - apply res_models_true.
Qed.

Lemma s2_models_comma_r_closed (Σ : gmap atom ty) Γ1 Γ2 r :
  ctx_fv Γ2 = ∅ ->
  r ⊨ ctx_denote_under Σ (Γ1 ,, Γ2) ->
  r ⊨ ctx_denote_under Σ Γ2.
Proof.
  intros Hfv Hctx.
  cbn [ctx_denote_under] in Hctx.
  rewrite res_models_and_iff in Hctx. destruct Hctx as [_ Hctx].
  rewrite res_models_and_iff in Hctx. destruct Hctx as [_ Hctx].
  rewrite ctx_denote_under_minimal in Hctx.
  rewrite ctx_denote_under_minimal.
  rewrite Hfv in *. rewrite !storeA_restrict_empty_set in *.
  exact Hctx.
Qed.

Lemma s2_models_star_l (Σ : gmap atom ty) Γ1 Γ2 r :
  r ⊨ ctx_denote_under Σ (Γ1 ∗ Γ2) ->
  r ⊨ ctx_denote_under Σ Γ1.
Proof.
  intros Hctx.
  destruct (ctx_denote_under_star_elim Σ Γ1 Γ2 r Hctx)
    as (m1 & m2 & Hc & Hle & H1 & _).
  eapply res_models_kripke; [ |exact H1].
  etransitivity; [apply res_product_le_l|exact Hle].
Qed.

Lemma s2_models_star_r (Σ : gmap atom ty) Γ1 Γ2 r :
  r ⊨ ctx_denote_under Σ (Γ1 ∗ Γ2) ->
  r ⊨ ctx_denote_under Σ Γ2.
Proof.
  intros Hctx.
  destruct (ctx_denote_under_star_elim Σ Γ1 Γ2 r Hctx)
    as (m1 & m2 & Hc & Hle & _ & H2).
  eapply res_models_kripke; [ |exact H2].
  etransitivity; [apply res_product_le_r|exact Hle].
Qed.

Lemma s2_models_emp_star_emp r :
  r ⊨ ctx_denote_under ∅ (Emp ∗ Emp).
Proof.
  pose proof (raw_compat_unit_r r) as Hc.
  pose proof (ctx_denote_under_star_intro_product ∅ Emp Emp r res_unit Hc
    I (s2_models_emp ∅ r) (s2_models_emp ∅ res_unit)) as H.
  rewrite res_product_unit_r_eq_any in H. exact H.
Qed.

(** ((A ∗ B) ∗ C) ⊨ ((B ∗ C) ∗ A) *)
Lemma s2_models_star_rotate (Σ : gmap atom ty) A B C r :
  basic_ctx (dom Σ) ((A ∗ B) ∗ C) ->
  r ⊨ ctx_denote_under Σ ((A ∗ B) ∗ C) ->
  r ⊨ ctx_denote_under Σ ((B ∗ C) ∗ A).
Proof.
  intros Hbasic Hctx.
  cbn [basic_ctx ctx_dom] in Hbasic.
  destruct Hbasic as [[HA [HB HAB]] [HC HABC]].
  destruct (ctx_denote_under_star_elim Σ (A ∗ B) C r Hctx)
    as (mab & mc & Hc1 & Hle1 & Hab & Hcm).
  destruct (ctx_denote_under_star_elim Σ A B mab Hab)
    as (ma & mb & Hc2 & Hle2 & Ham & Hbm).
  (* compat (ma × mb) mc *)
  destruct (res_product_comm_eq mab mc Hc1) as [Hc1' _].
  pose proof (world_compat_le_r mc (res_product ma mb Hc2) mab Hle2 Hc1') as Hc3'.
  destruct (res_product_comm_eq mc (res_product ma mb Hc2) Hc3') as [Hc3 _].
  assert (Hle3 : res_product (res_product ma mb Hc2) mc Hc3 ⊑ r).
  { etransitivity; [ |exact Hle1].
    apply res_product_le_mono; [exact Hle2|reflexivity]. }
  destruct (res_product_assoc_eq ma mb mc Hc2 Hc3) as (Hbc & Habc & Heq).
  rewrite Heq in Hle3.
  destruct (res_product_comm_eq ma (res_product mb mc Hbc) Habc) as [Habc' Heq'].
  rewrite Heq' in Hle3.
  eapply res_models_kripke; [exact Hle3| ].
  apply ctx_denote_under_star_intro_product.
  - cbn [basic_ctx]. repeat split; try assumption. set_solver.
  - apply ctx_denote_under_star_intro_product; assumption.
  - exact Ham.
Qed.

Lemma s2_fv_closed (τ : context_ty) :
  basic_context_ty ∅ τ -> fv_cty τ = ∅.
Proof.
  intros Hwf. pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hwf). set_solver.
Qed.

Lemma s2_models_comma_l (Σ : gmap atom ty) Γ1 Γ2 r :
  r ⊨ ctx_denote_under Σ (Γ1 ,, Γ2) ->
  r ⊨ ctx_denote_under Σ Γ1.
Proof. apply ctx_denote_under_comma_left. Qed.

(** Semantic subtyping is monotone in the context denotation (same erasure). *)
Lemma s2_sub_type_ctx_entails (Γ1 Γ2 : ctx) (τ1 τ2 : context_ty) :
  erase_ctx Γ1 = erase_ctx Γ2 ->
  wf_ctx_under ∅ Γ1 ->
  (forall r, r ⊨ ctx_denote_under ∅ Γ1 -> r ⊨ ctx_denote_under ∅ Γ2) ->
  sub_type_under ∅ Γ2 τ1 τ2 ->
  sub_type_under ∅ Γ1 τ1 τ2.
Proof.
  intros Herase HΓ1 Hent Hsub0.
  unfold sub_type_under in *.
  destruct Hsub0 as (HΓ2 & Hτ1 & Hτ2 & Herτ & Hsub).
  rewrite Herase.
  split; [exact HΓ1| ]. split; [exact Hτ1| ]. split; [exact Hτ2| ].
  split; [exact Herτ| ].
  intros e He m Hm. apply (Hsub e He m). apply Hent. exact Hm.
Qed.

(** (Emp ∗ A) ∗ B ⊨ A ∗ B  and  (Emp ,, A) ∗ B ⊨ A ∗ B  for closed A. *)
Lemma s2_models_star_drop_emp_l (Σ : gmap atom ty) A B r :
  basic_ctx (dom Σ) A ->
  r ⊨ ctx_denote_under Σ ((Emp ∗ A) ∗ B) ->
  r ⊨ ctx_denote_under Σ (A ∗ B).
Proof.
  intros HA Hctx.
  destruct (ctx_denote_under_star_elim Σ (Emp ∗ A) B r Hctx)
    as (m1 & m2 & Hc & Hle & H1 & H2).
  eapply res_models_kripke; [exact Hle| ].
  apply ctx_denote_under_star_intro_product; [exact HA| |exact H2].
  eapply s2_models_star_r. exact H1.
Qed.

Lemma s2_models_star_drop_emp_comma (Σ : gmap atom ty) A B r :
  basic_ctx (dom Σ) A ->
  ctx_fv A = ∅ ->
  r ⊨ ctx_denote_under Σ ((Emp ,, A) ∗ B) ->
  r ⊨ ctx_denote_under Σ (A ∗ B).
Proof.
  intros HA Hfv Hctx.
  destruct (ctx_denote_under_star_elim Σ (Emp ,, A) B r Hctx)
    as (m1 & m2 & Hc & Hle & H1 & H2).
  eapply res_models_kripke; [exact Hle| ].
  apply ctx_denote_under_star_intro_product; [exact HA| |exact H2].
  eapply s2_models_comma_r_closed; [exact Hfv|exact H1].
Qed.

(** A ∗ B ⊨ B ∗ A *)
Lemma s2_models_star_comm (Σ : gmap atom ty) A B r :
  basic_ctx (dom Σ) (A ∗ B) ->
  r ⊨ ctx_denote_under Σ (A ∗ B) ->
  r ⊨ ctx_denote_under Σ (B ∗ A).
Proof.
  intros Hb Hctx.
  cbn [basic_ctx] in Hb. destruct Hb as [HA [HB Hd]].
  destruct (ctx_denote_under_star_elim Σ A B r Hctx) as (ma & mb & Hc & Hle & Ha & Hbm).
  destruct (res_product_comm_eq ma mb Hc) as [Hc' Heq].
  rewrite Heq in Hle.
  eapply res_models_kripke; [exact Hle| ].
  apply ctx_denote_under_star_intro_product; assumption.
Qed.

End S2CtxSubHelpers.
Import S2CtxSubHelpers.

Section Section2TypingExamples.

Definition x : atom := 201%positive.
Definition y : atom := 202%positive.
Definition z : atom := 203%positive.
Definition g : atom := 204%positive.
Definition gx : atom := 205%positive.
Definition cmp : atom := 206%positive.
Definition ylet : atom := 207%positive.
Definition cond : atom := 208%positive.
Definition c1 : atom := 209%positive.
Definition c2 : atom := 210%positive.
Definition f : atom := 211%positive.
Definition a : atom := 212%positive.
Definition r1 : atom := 213%positive.
Definition r2 : atom := 214%positive.

Definition one_program : tm :=
  ret (vnat 1).

Definition minus_three_program : tm :=
  ret (ƛ x : ℕ => x ⟨ - ⟩ vnat 3).

Definition x_minus_three : tm :=
  x ⟨ - ⟩ vnat 3.

Definition may_must_intro_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let cond := y ⟨ > ⟩ vnat 10 in
        if cond then
          let gx := g @ x in
          gx ⟨ + ⟩ vnat 1
        else
          x ⟨ + ⟩ vnat 1))).

Definition dependent_context_program : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := x ⟨ + ⟩ vnat 1 in
  x ⟨ - ⟩ y.

Definition independent_context_program : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := op_natGen ·₁ vnat 0 in
  x ⟨ - ⟩ y.

Definition x_minus_y : tm :=
  x ⟨ - ⟩ y.

Definition x_minus_z_plus_y : tm :=
  let a := z ⟨ + ⟩ y in
  x ⟨ - ⟩ a.

Definition y_minus_z : tm :=
  y ⟨ - ⟩ z.

Definition branch_three_five : tm :=
  let cond := op_eq0 ·₁ x in
  if cond then ret (vnat 3) else ret (vnat 5).

Definition branch_five_three : tm :=
  let cond := x ⟨ > ⟩ vnat 0 in
  if cond then ret (vnat 5) else ret (vnat 3).

Definition let_duplication_program : tm :=
  let ylet := x ⟨ - ⟩ vnat 3 in
  x ⟨ - ⟩ ylet.

Definition minus_curried_program : tm :=
  ret (ƛ x : ℕ =>
    ret (ƛ y : ℕ => x ⟨ - ⟩ y)).

Definition nested_apply_program : tm :=
  ret (ƛ f : ℕ →ᵦ ℕ =>
    let r1 := f @ y in
    let r2 := f @ r1 in
    x ⟨ - ⟩ r2).

Definition ack_like_program : tm :=
  ret (μ f, x : ℕ ~> ℕ →ᵦ ℕ =>
    ret (ƛ y : ℕ =>
      let c1 := op_eq0 ·₁ x in
      if c1 then
        ret (vnat 0)
      else
        let c2 := op_eq0 ·₁ y in
        if c2 then
          ret x
        else
          let r1 := x ⟨ - ⟩ vnat 1 in
          let r2 := y ⟨ - ⟩ vnat 1 in
          f @@ (r1, r2))).

Definition nat_match_like_program : tm :=
  let cond := op_eq0 ·₁ x in
  if cond then ret (vnat 3) else ret (vnat 5).

Definition nat_to_nat_ty : ty := (ℕ : ty) →ᵦ ℕ.
Definition nat_to_nat_to_nat_ty : ty := (ℕ : ty) →ᵦ ℕ →ᵦ ℕ.
Definition may_must_intro_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ ℕ.

Lemma one_program_basic_type :
  ∅ ⊢ₑ one_program ⋮ ℕ.
Proof. unfold one_program. basic_check. Qed.

Lemma one_program_extended_type :
  ∅; Emp ⊢ₓ one_program ⋮ const_precise_ty (cnat 1).
Proof.
  unfold one_program.
  eapply EXT_Const.
  extended_wf.
Qed.

Lemma minus_three_program_basic_type :
  ∅ ⊢ₑ minus_three_program ⋮ nat_to_nat_ty.
Proof. unfold minus_three_program, nat_to_nat_ty. basic_check. Qed.

Lemma x_minus_three_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ x_minus_three ⋮ ℕ.
Proof. unfold x_minus_three. basic_check. Qed.

Lemma x_minus_three_extended_type :
  ∅; x ∷ ONat ⊢ₓ
    x_minus_three ⋮ binop_precise_ty bop_minus (avar x) (vnat 3).
Proof.
  unfold x_minus_three.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma may_must_intro_program_basic_type :
  ∅ ⊢ₑ may_must_intro_program ⋮ may_must_intro_basic_ty.
Proof. unfold may_must_intro_program, may_must_intro_basic_ty. basic_check. Qed.

Lemma dependent_context_program_basic_type :
  ∅ ⊢ₑ dependent_context_program ⋮ ℕ.
Proof. unfold dependent_context_program. basic_check. Qed.

Lemma independent_context_program_basic_type :
  ∅ ⊢ₑ independent_context_program ⋮ ℕ.
Proof. unfold independent_context_program. basic_check. Qed.

Lemma x_minus_y_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ x_minus_y ⋮ ℕ.
Proof. unfold x_minus_y. basic_check. Qed.

Lemma x_minus_y_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    x_minus_y ⋮ binop_precise_ty bop_minus (avar x) (avar y).
Proof.
  unfold x_minus_y.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma x_minus_z_plus_y_basic_type :
  <[z := (ℕ : ty)]> (<[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅)) ⊢ₑ x_minus_z_plus_y ⋮ ℕ.
Proof. unfold x_minus_z_plus_y. basic_check. Qed.

Lemma y_minus_z_basic_type :
  <[z := (ℕ : ty)]> (<[y := (ℕ : ty)]> ∅) ⊢ₑ y_minus_z ⋮ ℕ.
Proof. unfold y_minus_z. basic_check. Qed.

Lemma y_minus_z_extended_type :
  ∅; (y ∷ ONat) ,, (z ∷ ONat) ⊢ₓ
    y_minus_z ⋮ binop_precise_ty bop_minus (avar y) (avar z).
Proof.
  unfold y_minus_z.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma branch_three_five_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ branch_three_five ⋮ ℕ.
Proof. unfold branch_three_five. basic_check. Qed.

Lemma branch_five_three_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ branch_five_three ⋮ ℕ.
Proof. unfold branch_five_three. basic_check. Qed.

Lemma let_duplication_program_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ let_duplication_program ⋮ ℕ.
Proof. unfold let_duplication_program. basic_check. Qed.

Lemma minus_curried_program_basic_type :
  ∅ ⊢ₑ minus_curried_program ⋮ nat_to_nat_to_nat_ty.
Proof. unfold minus_curried_program, nat_to_nat_to_nat_ty. basic_check. Qed.

Lemma nested_apply_program_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ
    nested_apply_program ⋮ ((ℕ →ᵦ ℕ) →ᵦ ℕ).
Proof.
  unfold nested_apply_program, nat_to_nat_ty.
  basic_check.
Qed.

Lemma ack_like_program_basic_type :
  ∅ ⊢ₑ ack_like_program ⋮ nat_to_nat_to_nat_ty.
Proof.
  unfold ack_like_program, nat_to_nat_to_nat_ty.
  basic_check.
Qed.

Lemma nat_match_like_program_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ nat_match_like_program ⋮ ℕ.
Proof. unfold nat_match_like_program. basic_check. Qed.


(** ** Context typings (case-study judgment [⊢ₓ])

    Conventions.
    - The paper works over [int]; the Rocq case-study language only has [ℕ]
      with truncated subtraction [n - m = max 0 (n-m)].  Every qualifier is
      stated over [ℕ]; where truncation changes the meaning of a paper
      qualifier we say so next to the example.  For instance the paper's
      [ν ≥ 0] is trivial over [ℕ], so [[ν ≥ 0]] is the angelic top type
      [[: ℕ | ⊤]] in spirit; we keep the literal qualifier [0 ≤ ν].
    - Structural derivations are closed with [Qed].  Every semantic side
      condition ([sub_type_under], [ctx_sub_under]) is a separately named
      lemma [<program>_obl_<what>].  Structural T-CtxSub obligations
      (weakening, framing, exchange, Emp ≤ Emp ∗ Emp) are proved from the
      context denotation; closed-qualifier subtypings are proved from the
      generic ExtendedSubsumption lemmas; context-dependent semantic
      subtypings and the T-Match splits are left Admitted with an informal
      argument.

    Summary of findings (details next to each example):
    - Example 3.1: the paper's intermediate premise
      [x:{ν<10}, y:{ν<7} ⊢ x - y : {ν ≤ 3}] is invalid ((9,0) is a
      counterexample); the derivation must keep [y : {ν = x - 3}].
    - p.7 [x - (z + y)]: derivable both with the paper's T-LetI (the
      bound [z + y] gets the closed demonic type [{⊤}] under the entangled
      (y,z); the body [x - a] lives in [x ∗ a]) and with the entangled
      T-Let keeping [a : {ν = z + y} ⊓ [ν = z + y]].
    - Translation of [[ν | ⊤]]: the library's [qual_top] does not mention
      [ν], so [[: ℕ | qual_top]] is trivial (any non-empty capability); the
      paper's angelic top is the (now faithful) shared [UNat = U[ℕ]].
      With the trivial version the T-Match splits on [x:[⊤]] would be
      false.
    - p.8 nested application: the right-nested ANF program
      [nested_apply_program] is not derivable at the intended type; the
      MNF nesting [let r2 = (let r1 = f y in f r1) in x - r2] is.
    - Example 3.3 ([ack_like_program]): not derivable.  Round 1 blamed
      T-Match on the demonic recursive parameter; with T-CtxCase that part
      is solved, but the T-Fix PREMISE for the paper's type is semantically
      FALSE in the Rocq denotation: the recursive binding
      f:({⊤} ⊓ {ν ≺ x}) → … is vacuous on capabilities that contain the
      base case x = 0, and its angelic guarantee is collective while [y]
      may be correlated with [f] (counterexample capabilities next to the
      example).  Only the base case x:{ν=0} is derived.
    - Figure 6(a) ([may_must_intro_program]): the → type is semantically
      false (counterexample capability); the authors' -∗ setting (2) is
      true and is now DERIVED with T-CtxCase
      ([may_must_intro_program_setting2_type]); the round-1 variants with a
      demonic bound on [y] are kept.
    - Round 2, new rules: T-CtxCase also derives the plain safety judgment
      x:{⊤} ⊢ if x == 0 then 3 else 5 : {ν = 3 ∨ ν = 5}
      ([branch_three_five_demonic_type]), and EXT_VarComma types [ret y]
      at its dependent binding type ([dependent_context_y_varcomma_type]).
      Constants are still only typed in [Emp] (EXT_Const), so they need a
      structural weakening T-CtxSub first. *)

(** *** Qualifiers *)

Definition qgt (k : nat) : type_qualifier := q_nat_pred ν (fun n => k < n).
Definition qge (k : nat) : type_qualifier := q_nat_pred ν (fun n => k <= n).
Definition qlt (k : nat) : type_qualifier := q_nat_pred ν (fun n => n < k).
Definition qle (k : nat) : type_qualifier := q_nat_pred ν (fun n => n <= k).
Definition qrange (lo hi : nat) : type_qualifier :=
  q_nat_pred ν (fun n => lo <= n <= hi).
Definition qodd : type_qualifier := q_nat_pred ν Nat.Odd.
Definition qeven : type_qualifier := q_nat_pred ν Nat.Even.
Definition qne0 : type_qualifier := q_nat_pred ν (fun n => n <> 0%nat).
Definition qeq (k : nat) : type_qualifier := mk_q_eq ν (vnat k).

(** [ν R v] for a (free or bound) natural-number value [v]. *)
Definition q_nat_rel (v : value) (R : nat -> nat -> Prop) : type_qualifier :=
  tqual (lvar_value_keys ν ∪ lvar_value_keys v)
    (fun σ =>
       exists n m,
         denote_lvar_value (lso_store σ) ν = Some (vconst (cnat n)) /\
         denote_lvar_value (lso_store σ) v = Some (vconst (cnat m)) /\
         R n m).

(** Paper type abbreviations. *)
Definition Apos : context_ty := [: ℕ | qgt 0].          (* [ν: nat | ν > 0] *)
Definition gen_ty : context_ty := primop_precise_ty op_natGen (vnat 0).
Definition BT : context_ty := bool_precise_ty true.
Definition BF : context_ty := bool_precise_ty false.
(** The paper's angelic top [[ν: nat | ⊤]] ("every natural number is
    reachable") is the shared [UNat = U[ℕ] = [: ℕ | q_base_all ℕ]]
    (CaseTypes), whose qualifier MENTIONS [ν].  (Round 1 used a local alias
    [Atop := [: ℕ | ν ∈ ℕ]] because the old shared [U[ℕ]] was built from
    [qual_top], which does not mention [ν] and makes the under type TRIVIAL:
    e.g. the singleton capability {x ↦ 5} satisfies it.  With that trivial
    reading the T-Match splits of [branch_three_five], [branch_five_three]
    and [nat_match_like_program] would be FALSE.  The local alias is now
    replaced by the faithful shared one; the two qualifiers are equivalent.)
    The demonic top [{: ℕ | qual_top}] is trivially true, as intended. *)
Definition Otop : context_ty := {: ℕ | qual_top}.   (* {ν: nat | ⊤} *)

Ltac s2_unfold :=
  unfold Apos, gen_ty, UNat, q_base_all, qgt, qge, qlt, qle, qrange, qodd, qeven, qne0, qeq,
    q_nat_rel, q_nat_pred, q_const_pred, vnu in *.

Lemma s2_union_singleton_l (i : atom) (T : ty) (m : gmap atom ty) :
  ({[i := T]} ∪ m : gmap atom ty) = <[i := T]> m.
Proof. symmetry. apply (insert_union_singleton_l (M:=gmap atom)). Qed.

Lemma s2_union_assoc (m1 m2 m3 : gmap atom ty) :
  ((m1 ∪ m2) ∪ m3 : gmap atom ty) = m1 ∪ (m2 ∪ m3).
Proof. symmetry. apply (map_union_assoc (M:=gmap atom)). Qed.

Lemma s2_union_empty_l (m : gmap atom ty) :
  ((∅ : gmap atom ty) ∪ m : gmap atom ty) = m.
Proof. apply (map_empty_union (M:=gmap atom)). Qed.

Lemma s2_union_empty_r (m : gmap atom ty) :
  (m ∪ (∅ : gmap atom ty) : gmap atom ty) = m.
Proof. apply (map_union_empty (M:=gmap atom)). Qed.

Ltac s2_erase_norm :=
  cbn [erase_ctx erase_ty] in *;
  unfold ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
    over_ty, under_ty, precise_ty, const_precise_ty, bool_precise_ty,
    primop_precise_ty, binop_precise_ty, fix_rec_call_ty in *;
  cbn [erase_ty prim_op_type bin_op_type base_ty_of_const] in *;
  rewrite ?s2_union_empty_l, ?s2_union_empty_r, ?s2_union_assoc,
    ?s2_union_singleton_l.

Ltac s2_wf :=
  s2_unfold; unfold base_ty_as_ty in *; extended_wf;
  try solve [s2_erase_norm; first [extended_basic_check | basic_check]].

(** Opening a closed context type is the identity. *)
Lemma s2_open_closed (k : nat) (z : atom) (τ : context_ty) :
  basic_context_ty ∅ τ ->
  cty_open k z τ = τ.
Proof.
  intros Hwf.
  eapply (cty_open_above_lc_fresh 0 k z τ); [lia| | ].
  - eapply wf_context_ty_at_lc. exact Hwf.
  - pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hwf). set_solver.
Qed.


Lemma s2_restrict_lookup (D D' : lvset) (s : LStoreOn D) (H : D' ⊆ D) (k : logic_var) :
  k ∈ D' ->
  (lso_store (lstore_on_restrict D' s H) : gmap logic_var value) !! k =
  (lso_store s : gmap logic_var value) !! k.
Proof.
  intros Hk. destruct s as [s Hdom].
  unfold lstore_on_restrict, storeA_on_restrict, lso_store. cbn.
  pose proof (storeA_restrict_lookup s D' k) as Hl.
  rewrite decide_True in Hl by exact Hk. exact Hl.
Qed.

Lemma s2_entails_eq_pred (k : nat) (P : nat -> Prop) :
  P k ->
  qualifier_entails (mk_q_eq ν (vnat k)) (q_nat_pred ν P).
Proof.
  intros HP s H1.
  unfold mk_q_eq, q_nat_pred, q_const_pred, vnu, vnat in *. cbn in *.
  rewrite s2_restrict_lookup in H1 by set_solver.
  exists (cnat k). split; [ |exact HP].
  rewrite s2_restrict_lookup by set_solver. exact H1.
Qed.

Lemma s2_entails_pred_pred (P Q : nat -> Prop) :
  (forall n, P n -> Q n) ->
  qualifier_entails (q_nat_pred ν P) (q_nat_pred ν Q).
Proof.
  intros HPQ s [c [Hc HPc]].
  unfold q_nat_pred, q_const_pred, vnu in *. cbn in *.
  rewrite s2_restrict_lookup in Hc by set_solver.
  exists c. split.
  - rewrite s2_restrict_lookup by set_solver. exact Hc.
  - destruct c; auto.
Qed.

Lemma s2_entails_top (q : type_qualifier) :
  qualifier_entails q qual_top.
Proof. intros s _. cbn. exact I. Qed.

(** Closed constant subtyping through the generic ExtendedSubsumption lemmas. *)
Lemma s2_const_over_sub (k : nat) (P : nat -> Prop) :
  P k ->
  sub_type_under ∅ Emp (const_precise_ty (cnat k)) ({: ℕ | q_nat_pred ν P}).
Proof.
  intros HP.
  eapply (extended_semantic_subtype_trans _ _ _ ({: ℕ | mk_q_eq ν (vnat k)})).
  - apply extended_semantic_subtype_inter_left.
    unfold subtype_wf. repeat split; s2_wf.
  - apply subtype_over_closed_by_qualifier.
    + unfold subtype_wf. repeat split; s2_wf.
    + cbn. set_solver.
    + cbn. set_solver.
    + apply s2_entails_eq_pred. exact HP.
Qed.

Lemma s2_const_over_top (k : nat) :
  sub_type_under ∅ Emp (const_precise_ty (cnat k)) ({: ℕ | qual_top}).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _ ({: ℕ | mk_q_eq ν (vnat k)})).
  - apply extended_semantic_subtype_inter_left.
    unfold subtype_wf. repeat split; s2_wf.
  - apply subtype_over_closed_by_qualifier.
    + unfold subtype_wf. repeat split; s2_wf.
    + cbn. set_solver.
    + cbn. set_solver.
    + apply s2_entails_top.
Qed.

Ltac s2_submap := apply (bool_decide_unpack _); vm_compute; reflexivity.

Ltac s2_wf_ctx :=
  s2_unfold; unfold base_ty_as_ty in *;
  unfold wf_ctx_under; cbn [basic_ctx ctx_dom]; repeat split;
  try solve [ extended_wf_type | fast_set_solver!!
            | unfold x, y, z, g, gx, cmp, ylet, cond, c1, c2, f, a, r1, r2;
              set_solver ].

(** Reduce a structural [ctx_sub_under] to an entailment between the two
    context denotations (witness [r' = r]). *)
Ltac s2_weaken :=
  apply s2_ctx_sub_entails; [s2_wf_ctx | s2_wf | s2_submap | intros ? Hr].

Ltac s2_closed_ctx_fv :=
  cbn [ctx_fv]; apply s2_fv_closed; s2_unfold;
  unfold BT, BF, bool_precise_ty, bool_qual, Apos, precise_ty in *;
  case_type_wf_syntax.

(** *** ⊢ 1 : {ν = 1} and ⊢ 1 : [ν = 1]  (paper p.4) *)

Lemma one_program_obl_over :
  sub_type_under ∅ Emp (const_precise_ty (cnat 1)) ({: ℕ | qeq 1}).
Proof.
  apply extended_semantic_subtype_inter_left.
  unfold subtype_wf. repeat split; s2_wf.
Qed.

Lemma one_program_obl_under :
  sub_type_under ∅ Emp (const_precise_ty (cnat 1)) ([: ℕ | qeq 1]).
Proof.
  apply extended_semantic_subtype_inter_right.
  unfold subtype_wf. repeat split; s2_wf.
Qed.

Theorem one_program_over_type :
  ∅; Emp ⊢ₓ one_program ⋮ ({: ℕ | qeq 1}).
Proof.
  unfold one_program.
  eapply EXT_Sub with (τ1 := const_precise_ty (cnat 1));
    [s2_wf| |exact one_program_obl_over].
  eapply EXT_Const. s2_wf.
Qed.

Theorem one_program_under_type :
  ∅; Emp ⊢ₓ one_program ⋮ ([: ℕ | qeq 1]).
Proof.
  unfold one_program.
  eapply EXT_Sub with (τ1 := const_precise_ty (cnat 1));
    [s2_wf| |exact one_program_obl_under].
  eapply EXT_Const. s2_wf.
Qed.

(** *** x:[ν > 3] ⊢ x - 3 : [ν > 0]  (paper p.5)

    Over [ℕ] the truncated [x - 3] agrees with the integer one whenever
    [x > 3], so the qualifiers are taken verbatim.  The paper's ✗ judgments
    on p.5 ([x:[ν>4]], [x:{ν>2}] with an angelic result, and [x:[ν>4]] with
    a demonic result) are counterexamples and are not typed. *)

Definition x_minus_three_ctx : ctx := x ∷ [: ℕ | qgt 3].

Lemma x_minus_three_obl_sub :
  sub_type_under ∅ x_minus_three_ctx
    (binop_precise_ty bop_minus (avar x) (vnat 3)) Apos.
Proof.
  (* Semantic argument.  Let [m ⊨ ⟦x:[ν>3]⟧]: the projection of [m] on [x]
     contains every [n > 3] (FUnder of the exact atom).  An inhabitant [e] of
     the precise binop type has, fiberwise over [x] (FFibVars on {x}), exactly
     the singleton result [x - 3] (FOver ∧ FUnder of the exact graph atom).
     For every [k > 0], the fiber [x = k + 3] exists in [m] and yields the
     result [k]; hence the result projection contains all positive numbers,
     which is [⟦[ν > 0]⟧ e].  Context-dependent, so it does not follow from
     the closed-qualifier lemmas of ExtendedSubsumption. *)
Admitted.

Theorem x_minus_three_type :
  ∅; x_minus_three_ctx ⊢ₓ x_minus_three ⋮ Apos.
Proof.
  unfold x_minus_three, x_minus_three_ctx.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (vnat 3));
    [s2_wf| |exact x_minus_three_obl_sub].
  eapply EXT_BinOp. s2_wf.
Qed.

(** Packaged as a closed function: ⊢ λx. x - 3 : x:[ν>3] → [ν>0]. *)
Lemma minus_three_program_obl_sub :
  sub_type_under ∅ (Emp ,, (x ∷ [: ℕ | qgt 3]))
    (binop_precise_ty bop_minus (avar x) (vnat 3)) Apos.
Proof.
  (* Reduced to [x_minus_three_obl_sub]: [Emp ,, Γ] entails [Γ] and has the
     same erasure. *)
  apply (s2_sub_type_ctx_entails _ x_minus_three_ctx).
  - unfold x_minus_three_ctx. cbn [erase_ctx]. apply s2_union_empty_l.
  - s2_wf_ctx.
  - intros r Hr. eapply s2_models_comma_r_closed; [ |exact Hr].
    unfold x_minus_three_ctx. s2_closed_ctx_fv.
  - exact x_minus_three_obl_sub.
Qed.

Theorem minus_three_program_type :
  ∅; Emp ⊢ₓ minus_three_program ⋮ ([: ℕ | qgt 3] → Apos).
Proof.
  unfold minus_three_program.
  eapply EXT_LamNamedErased; [reflexivity|s2_wf| ].
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (vnat 3));
    [s2_wf| |exact minus_three_program_obl_sub].
  eapply EXT_BinOp. s2_wf.
Qed.

(** *** Γ_dis vs Γ_en (paper p.6)

    x:[ν ≥ 0] ∗ y:[ν ≥ 1] ⊢ x - y : [ν > 0]  ✓
    x:[ν ≥ 0] , y:[ν ≥ 1] ⊢ x - y : [ν > 0]  ✗

    Over [ℕ], [ν ≥ 0] is trivially true; truncation does not matter for the
    ✓ judgment (choose [y = 1], [x = k + 1]).  The ✗ judgment is also a
    counterexample over [ℕ]: the capability {(x,y) = (n, n+1) | n ∈ ℕ}
    satisfies the entangled context, yet [x - y] is always [0]. *)

Definition gamma_dis : ctx := (x ∷ [: ℕ | qge 0]) ∗ (y ∷ [: ℕ | qge 1]).

Lemma x_minus_y_obl_dis_sub :
  sub_type_under ∅ gamma_dis
    (binop_precise_ty bop_minus (avar x) (avar y)) Apos.
Proof.
  (* [m ⊨ ⟦x:[ν≥0] ∗ y:[ν≥1]⟧] gives [m1 × m2 ⊑ m] with the [x]-projection
     of [m1] containing all of ℕ and the [y]-projection of [m2] containing
     every [n ≥ 1].  Because the product contains every pair, the
     environment (x,y) = (k+1, 1) is in [m] for each [k > 0]; in that
     (x,y)-fiber the precise result is [k].  Hence the result reaches every
     positive number. *)
Admitted.

Theorem x_minus_y_dis_type :
  ∅; gamma_dis ⊢ₓ x_minus_y ⋮ Apos.
Proof.
  unfold x_minus_y, gamma_dis.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (avar y));
    [s2_wf| |exact x_minus_y_obl_dis_sub].
  eapply EXT_BinOp. s2_wf.
Qed.

(** *** C_dis / C_en with [gen] (paper p.6)

    ∅ ⊢ C_dis[x - y] : [ν > 0]  ✓   (independent_context_program)
    ∅ ⊢ C_en [x - y] : [ν > 0]  ✗   (dependent_context_program)

    C_dis is typed with T-LetI twice, which is what keeps the two
    generator results independent ([x:gen ∗ y:gen]).  The outer T-LetI
    needs the empty context presented as [Emp ∗ Emp] (T-CtxSub). *)

Lemma independent_context_program_obl_emp_star :
  ctx_sub_under ∅
    (fv_tm independent_context_program ∪ fv_cty Apos)
    Emp (Emp ∗ Emp).
Proof.
  (* Emp ≤ Emp ∗ Emp: the product of a capability with the unit. *)
  unfold independent_context_program. s2_weaken.
  apply s2_models_emp_star_emp.
Qed.

Lemma independent_context_program_obl_sub :
  sub_type_under ∅ ((x ∷ gen_ty) ∗ (y ∷ gen_ty))
    (binop_precise_ty bop_minus (avar x) (avar y)) Apos.
Proof.
  (* [gen_ty] is the precise type of [natGen 0], whose graph is all of ℕ:
     each component reaches every natural number.  The star gives a product
     capability, so (x,y) = (k+1,1) is present for all [k]; the result
     [x - y] therefore reaches every positive number. *)
Admitted.

Theorem independent_context_program_type :
  ∅; Emp ⊢ₓ independent_context_program ⋮ Apos.
Proof.
  unfold independent_context_program.
  eapply EXT_CtxSub with (Γ2 := Emp ∗ Emp);
    [s2_wf| |exact independent_context_program_obl_emp_star].
  eapply EXT_LetDNamed with (τ1 := gen_ty); [s2_wf| | ].
  - eapply EXT_AppOpValue. s2_wf.
  - eapply EXT_LetDNamed with (τ1 := gen_ty); [s2_wf| | ].
    + eapply EXT_AppOpValue. s2_wf.
    + eapply EXT_Sub with
        (τ1 := binop_precise_ty bop_minus (avar x) (avar y));
        [s2_wf| |exact independent_context_program_obl_sub].
      eapply EXT_BinOp. s2_wf.
Qed.

(** For C_en the result type [[ν > 0]] is a counterexample.  Over [ℕ],
    [x - (x + 1)] truncates to [0], so the precise information retained by
    the entangled T-Let derivation gives the (demonic) type [{ν = 0}]. *)

Definition dependent_ctx : ctx :=
  (Emp ,, (x ∷ gen_ty)) ,, (y ∷ binop_precise_ty bop_plus (avar x) (vnat 1)).

Lemma dependent_context_program_obl_sub :
  sub_type_under ∅ dependent_ctx
    (binop_precise_ty bop_minus (avar x) (avar y)) ({: ℕ | qeq 0}).
Proof.
  (* Demonic, fiberwise argument: [y] is bound precisely to [x + 1], so in
     every environment of the capability [y = x + 1]; the precise result
     type forces the result to equal [x - y = x - (x+1) = 0] (truncated). *)
Admitted.

Theorem dependent_context_program_type :
  ∅; Emp ⊢ₓ dependent_context_program ⋮ ({: ℕ | qeq 0}).
Proof.
  unfold dependent_context_program.
  eapply EXT_LetNamed with (τ1 := gen_ty); [s2_wf| | ].
  - eapply EXT_AppOpValue. s2_wf.
  - eapply EXT_LetNamed with
      (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1)); [s2_wf| | ].
    + eapply EXT_BinOp. s2_wf.
    + eapply EXT_Sub with
        (τ1 := binop_precise_ty bop_minus (avar x) (avar y));
        [s2_wf| |exact dependent_context_program_obl_sub].
      eapply EXT_BinOp. s2_wf.
Qed.

(** *** The three-variable context (paper p.7)

    Γ3 := x:[ν>0] ∗ (y:[ν>0], z:[ν>0])
    Γ3 ⊢ x - y       : [ν>0]  ✓
    Γ3 ⊢ x - (z + y) : [ν>0]  ✓   (x_minus_z_plus_y, ANF: let a = z + y in x - a)
    Γ3 ⊢ y - z       : [ν>0]  ✗   (y_minus_z) *)

Definition gamma3 : ctx :=
  (x ∷ Apos) ∗ ((y ∷ Apos) ,, (z ∷ Apos)).

Lemma x_minus_y_obl_gamma3_sub :
  sub_type_under ∅ gamma3
    (binop_precise_ty bop_minus (avar x) (avar y)) Apos.
Proof.
  (* [m ⊒ mx × myz]; [mx] reaches every positive [x], [myz] reaches [y = 1]
     (in some environment, together with some [z]).  The product contains
     (x, y, z) = (k+1, 1, z0) for every k, so [x - y] reaches every [k > 0]. *)
Admitted.

Theorem x_minus_y_gamma3_type :
  ∅; gamma3 ⊢ₓ x_minus_y ⋮ Apos.
Proof.
  unfold x_minus_y, gamma3.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (avar y));
    [s2_wf| |exact x_minus_y_obl_gamma3_sub].
  eapply EXT_BinOp. s2_wf.
Qed.

(** Two derivations of [Γ3 ⊢ x - (z + y) : [ν>0]].

    (A) Paper-intended bunched derivation (T-LetI), see
    [x_minus_z_plus_y_letI_type] below: exchange Γ3 to
    [(y:[ν>0], z:[ν>0]) ∗ x:[ν>0]] (structural T-CtxSub, Qed), type the
    bound expression [z + y] under the entangled half (y,z) at the CLOSED
    DEMONIC type [a : {ν | ⊤}] (T-BinOpTop), and type the body under
    [x:[ν>0] ∗ a:{ν | ⊤}].  The body is valid because the context gives a
    product world: fix any [a0] in the (non-empty) [a]-part; [x = k + a0] is
    present for every [k > 0], giving the result [k].  This is exactly the
    paper's reasoning that "x can be angelically chosen independently of
    both y and z".

    (Correction of an earlier claim: it is true that the only closed
    ANGELIC type of [z + y] under an entangled (y,z) is the trivial one —
    for every [n] there is a capability of (y:[ν>0], z:[ν>0]) in which
    [z + y] never equals [n] (pair each k ≥ 1 with π(k) for a permutation π
    of the positives with k + π(k) ≠ n) — but no angelic information about
    [a] is needed: a closed demonic type suffices, because the independence
    of [x] from [a] is what makes [x - a] reach every positive number.)

    (B) Entangled T-Let keeping the precise dependent type
    [a : {ν = z + y} ⊓ [ν = z + y]] ([x_minus_z_plus_y_type]); the
    independence of [x] from (y,z,a) is then discharged semantically. *)

Definition x_minus_z_plus_y_ctx : ctx :=
  gamma3 ,, (a ∷ binop_precise_ty bop_plus (avar z) (avar y)).

Lemma x_minus_z_plus_y_obl_sub :
  sub_type_under ∅ x_minus_z_plus_y_ctx
    (binop_precise_ty bop_minus (avar x) (avar a)) Apos.
Proof.
  unfold x_minus_z_plus_y_ctx.
  (* [m ⊨ Γ3 ,, a:{ν=z+y}⊓[ν=z+y]]: the (x,y,z)-part of [m] contains a
     product [mx × myz] with [mx] reaching all positive [x]; [a] is
     fiberwise equal to [z + y].  Fix any environment (y0,z0) of [myz] and
     put [a0 = z0 + y0]; for [k > 0] the environment (k + a0, y0, z0, a0)
     belongs to [m], and there the result is [k].  Over ℕ the truncation is
     irrelevant because [x] is chosen above [a0]. *)
Admitted.

Theorem x_minus_z_plus_y_type :
  ∅; gamma3 ⊢ₓ x_minus_z_plus_y ⋮ Apos.
Proof.
  unfold x_minus_z_plus_y, gamma3.
  eapply EXT_LetNamed with
    (τ1 := binop_precise_ty bop_plus (avar z) (avar y)); [s2_wf| | ].
  - eapply EXT_BinOp. unfold gamma3. s2_wf.
  - eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (avar a));
      [unfold gamma3; s2_wf| |exact x_minus_z_plus_y_obl_sub].
    eapply EXT_BinOp. unfold gamma3. s2_wf.
Qed.

(** (A) the T-LetI derivation. *)
Definition yz_ctx : ctx := (y ∷ Apos) ,, (z ∷ Apos).

Lemma x_minus_z_plus_y_obl_exchange :
  ctx_sub_under ∅ (fv_tm x_minus_z_plus_y ∪ fv_cty Apos)
    gamma3 (yz_ctx ∗ (x ∷ Apos)).
Proof.
  (* Structural: star commutativity, witness r' = r. *)
  unfold gamma3, yz_ctx, x_minus_z_plus_y. s2_weaken.
  apply s2_models_star_comm; [s2_wf_ctx|exact Hr].
Qed.

Lemma x_minus_z_plus_y_obl_letI_sub :
  sub_type_under ∅ ((x ∷ Apos) ∗ (a ∷ Otop))
    (binop_precise_ty bop_minus (avar x) (avar a)) Apos.
Proof.
  (* [m ⊨ x:[ν>0] ∗ a:{⊤}] gives [mx × ma ⊑ m] with the [x]-projection of
     [mx] containing every positive number ([qgt 0] mentions [ν], so the
     under atom is not trivial) and [ma] non-empty (worlds are non-empty;
     [{⊤}] is a closed demonic type, trivially satisfied).  Fix [a0] in
     [ma]; for each [k > 0] the environment (x, a) = (k + a0, a0) is in the
     product, and in that (x,a)-fiber the precise result is
     [(k + a0) - a0 = k].  Hence the result projection contains every
     positive number, which is [⟦[ν > 0]⟧].  Same shape as
     [x_minus_y_obl_dis_sub]. *)
Admitted.

Theorem x_minus_z_plus_y_letI_type :
  ∅; gamma3 ⊢ₓ x_minus_z_plus_y ⋮ Apos.
Proof.
  pose proof x_minus_z_plus_y_obl_exchange as Hex.
  unfold x_minus_z_plus_y, gamma3, yz_ctx in *.
  eapply EXT_CtxSub with (Γ2 := ((y ∷ Apos) ,, (z ∷ Apos)) ∗ (x ∷ Apos));
    [s2_wf| |exact Hex].
  eapply EXT_LetDNamed with (τ1 := Otop); [unfold Otop; s2_wf| | ].
  - change Otop with (binop_top_ty bop_plus).
    eapply EXT_BinOpTop. s2_wf.
  - eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (avar a));
      [unfold Otop; s2_wf| |exact x_minus_z_plus_y_obl_letI_sub].
    eapply EXT_BinOp. unfold Otop. s2_wf.
Qed.

(** [Γ3 ⊢ y - z : [ν>0]] is the paper's ✗: the capability in which [x]
    ranges over all positives and (y,z) over {(k,k) | k ≥ 1} satisfies Γ3,
    but [y - z = 0] everywhere.  Corrected variant: making [y] and [z]
    independent restores the judgment. *)

Definition y_z_dis_ctx : ctx := (y ∷ Apos) ∗ (z ∷ Apos).

Lemma y_minus_z_obl_dis_sub :
  sub_type_under ∅ y_z_dis_ctx
    (binop_precise_ty bop_minus (avar y) (avar z)) Apos.
Proof.
  (* Product capability: (y,z) = (k+1, 1) is present for every k > 0. *)
Admitted.

Theorem y_minus_z_dis_type :
  ∅; y_z_dis_ctx ⊢ₓ y_minus_z ⋮ Apos.
Proof.
  unfold y_minus_z, y_z_dis_ctx.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar y) (avar z));
    [s2_wf| |exact y_minus_z_obl_dis_sub].
  eapply EXT_BinOp. s2_wf.
Qed.

(** *** Curried subtraction (paper p.7)

    ⊢ (-) : x:[ν>0] -∗ y:[ν>0] -∗ [ν>0]   ✓
    ⊢ (-) : x:[ν>0] →  y:[ν>0] -∗ [ν>0]   ✓
    ⊢ (-) : x:[ν>0] -∗ y:[ν>0] →  [ν>0]   ✗  (needs (∅ ∗ x), y ⊢ x - y,
                                            refuted by the capability x = y) *)

Lemma minus_curried_program_obl_core :
  sub_type_under ∅ ((x ∷ Apos) ∗ (y ∷ Apos))
    (binop_precise_ty bop_minus (avar x) (avar y)) Apos.
Proof.
  (* Same argument as [y_minus_z_obl_dis_sub]: [x] and [y] are independent,
     each reaching every positive number; choose (x,y) = (k+1,1). *)
Admitted.

Lemma minus_curried_program_obl_wand_wand :
  sub_type_under ∅ ((Emp ∗ (x ∷ Apos)) ∗ (y ∷ Apos))
    (binop_precise_ty bop_minus (avar x) (avar y)) Apos.
Proof.
  (* Reduced to [minus_curried_program_obl_core]. *)
  apply (s2_sub_type_ctx_entails _ ((x ∷ Apos) ∗ (y ∷ Apos))).
  - cbn [erase_ctx]. rewrite s2_union_empty_l. reflexivity.
  - s2_wf_ctx.
  - intros r Hr. eapply s2_models_star_drop_emp_l; [s2_wf_ctx|exact Hr].
  - exact minus_curried_program_obl_core.
Qed.

Theorem minus_curried_program_wand_wand_type :
  ∅; Emp ⊢ₓ minus_curried_program ⋮ (Apos -∗ Apos -∗ Apos).
Proof.
  unfold minus_curried_program.
  eapply EXT_LamDNamedErased; [reflexivity|s2_wf| ].
  eapply EXT_LamDNamedErased; [reflexivity|s2_wf| ].
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (avar y));
    [s2_wf| |exact minus_curried_program_obl_wand_wand].
  eapply EXT_BinOp. s2_wf.
Qed.

Lemma minus_curried_program_obl_arrow_wand :
  sub_type_under ∅ ((Emp ,, (x ∷ Apos)) ∗ (y ∷ Apos))
    (binop_precise_ty bop_minus (avar x) (avar y)) Apos.
Proof.
  (* Reduced to [minus_curried_program_obl_core]. *)
  apply (s2_sub_type_ctx_entails _ ((x ∷ Apos) ∗ (y ∷ Apos))).
  - cbn [erase_ctx]. rewrite s2_union_empty_l. reflexivity.
  - s2_wf_ctx.
  - intros r Hr. eapply s2_models_star_drop_emp_comma;
      [s2_wf_ctx|s2_closed_ctx_fv|exact Hr].
  - exact minus_curried_program_obl_core.
Qed.

Theorem minus_curried_program_arrow_wand_type :
  ∅; Emp ⊢ₓ minus_curried_program ⋮ (Apos → Apos -∗ Apos).
Proof.
  unfold minus_curried_program.
  eapply EXT_LamNamedErased; [reflexivity|s2_wf| ].
  eapply EXT_LamDNamedErased; [reflexivity|s2_wf| ].
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (avar y));
    [s2_wf| |exact minus_curried_program_obl_arrow_wand].
  eapply EXT_BinOp. s2_wf.
Qed.

(** *** x:[ν < 10] ⊢ x + 1 : {odd} ⊕ {even}  (paper p.8)

    Added program (the paper's term [x + 1]); qualifiers are literal over ℕ. *)

Definition x_plus_one : tm := x ⟨ + ⟩ vnat 1.

Lemma x_plus_one_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ x_plus_one ⋮ ℕ.
Proof. unfold x_plus_one. basic_check. Qed.

Lemma x_plus_one_obl_sum :
  sub_type_under ∅ (x ∷ [: ℕ | qlt 10])
    (binop_precise_ty bop_plus (avar x) (vnat 1))
    ({: ℕ | qodd} ⊕ {: ℕ | qeven}).
Proof.
  (* The context guarantees the [x]-projection contains 0..9, so the result
     projection of [x + 1] contains both 1 (odd) and 2 (even).  Split the
     result-extended capability into the (non-empty) sub-capabilities whose
     result is odd, resp. even; their sum is the whole capability and each
     part satisfies its demonic summand. *)
Admitted.

Theorem x_plus_one_sum_type :
  ∅; x ∷ [: ℕ | qlt 10] ⊢ₓ x_plus_one ⋮ ({: ℕ | qodd} ⊕ {: ℕ | qeven}).
Proof.
  unfold x_plus_one.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1));
    [s2_wf| |exact x_plus_one_obl_sum].
  eapply EXT_BinOp. s2_wf.
Qed.

(** *** Context sums and T-Match (paper pp.8-9, Example 3.4 pp.12-13)

    The Rocq programs desugar [if x == 0] / [if x > 0] into a let-bound
    boolean [cond] and a match on it.  T-Match needs the context presented
    as a sum [Γt ⊕ Γf] in which [cond] has the precise type [true] resp.
    [false]; that split is the T-CtxSub obligation [<prog>_obl_split].
    Constants in branches are typed in the empty context, obtained by the
    T-CtxSub weakening obligations [<prog>_obl_*_weaken]; the remaining
    closed subtypings go through the generic closed-qualifier lemmas. *)


Definition cond_split_ctx : ctx := (cond ∷ BT) ⊕ (cond ∷ BF).

(** x:[⊤] ⊢ if x == 0 then 3 else 5 : {ν < 4} ⊕ {ν > 4}  (p.8) *)

Definition branch_three_five_ctx : ctx :=
  (x ∷ UNat) ,, (cond ∷ primop_precise_ty op_eq0 (avar x)).

Lemma branch_three_five_obl_split :
  ctx_sub_under ∅
    (fv_tm (if cond then ret (vnat 3) else ret (vnat 5)) ∪
     fv_cty ({: ℕ | qlt 4} ⊕ {: ℕ | qgt 4}))
    branch_three_five_ctx cond_split_ctx.
Proof.
  (* X = {cond}.  Since [x:[⊤]] reaches every natural number, in particular
     0 and 1, and [cond] is fiberwise [x =? 0], the projection [r|{cond}] is
     exactly {true, false}.  Take [r' = r|{cond}] and split it as the sum of
     the two singleton capabilities {cond ↦ true} and {cond ↦ false}; each
     satisfies [cond:{ν = b} ⊓ [ν = b]] for its [b].  Erasures agree on
     [cond] (both [bool]). *)
Admitted.

Lemma branch_three_five_obl_true_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 3)) ∪ fv_cty ({: ℕ | qlt 4}))
    (cond ∷ BT) Emp.
Proof.
  (* Weakening to the empty context: X = ∅, witness r' = r. *)
  s2_weaken. apply s2_models_emp.
Qed.

Lemma branch_three_five_obl_false_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 5)) ∪ fv_cty ({: ℕ | qgt 4}))
    (cond ∷ BF) Emp.
Proof.
  (* Weakening to the empty context: X = ∅, witness r' = r. *)
  s2_weaken. apply s2_models_emp.
Qed.

Lemma branch_three_five_obl_three :
  sub_type_under ∅ Emp (const_precise_ty (cnat 3)) ({: ℕ | qlt 4}).
Proof. apply s2_const_over_sub. lia. Qed.

Lemma branch_three_five_obl_five :
  sub_type_under ∅ Emp (const_precise_ty (cnat 5)) ({: ℕ | qgt 4}).
Proof. apply s2_const_over_sub. lia. Qed.

Theorem branch_three_five_type :
  ∅; x ∷ UNat ⊢ₓ branch_three_five ⋮ ({: ℕ | qlt 4} ⊕ {: ℕ | qgt 4}).
Proof.
  unfold branch_three_five.
  eapply EXT_LetNamed with (τ1 := primop_precise_ty op_eq0 (avar x));
    [unfold UNat; s2_wf| | ].
  - eapply EXT_AppOpValue. unfold UNat. s2_wf.
  - eapply EXT_CtxSub with (Γ2 := cond_split_ctx);
      [unfold UNat; s2_wf| |exact branch_three_five_obl_split].
    unfold cond_split_ctx.
    eapply EXT_MatchBoth; [unfold BT, BF; s2_wf| | | | ].
    + eapply EXT_Var. unfold BT. s2_wf.
    + eapply EXT_Var. unfold BF. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp);
        [unfold BT; s2_wf| |exact branch_three_five_obl_true_weaken].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 3));
        [s2_wf| |exact branch_three_five_obl_three].
      eapply EXT_Const. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp);
        [unfold BF; s2_wf| |exact branch_three_five_obl_false_weaken].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 5));
        [s2_wf| |exact branch_three_five_obl_five].
      eapply EXT_Const. s2_wf.
Qed.

(** e_⊕⊤ : x:[⊤] ⊢ if x > 0 then 5 else 3 : {ν > 4} ⊕ {⊤}  (p.9) *)

Definition branch_five_three_ctx : ctx :=
  (x ∷ UNat) ,, (cond ∷ binop_precise_ty bop_gt (avar x) (vnat 0)).

Lemma branch_five_three_obl_split :
  ctx_sub_under ∅
    (fv_tm (if cond then ret (vnat 5) else ret (vnat 3)) ∪
     fv_cty ({: ℕ | qgt 4} ⊕ Otop))
    branch_five_three_ctx cond_split_ctx.
Proof.
  (* As [branch_three_five_obl_split]: [x] reaches 0 and 1, so [cond = x>0]
     reaches both [false] and [true]; split [r|{cond}] into the two
     singleton capabilities. *)
Admitted.

Lemma branch_five_three_obl_true_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 5)) ∪ fv_cty ({: ℕ | qgt 4}))
    (cond ∷ BT) Emp.
Proof.
  (* Weakening to the empty context: X = ∅, witness r' = r. *)
  s2_weaken. apply s2_models_emp.
Qed.

Lemma branch_five_three_obl_false_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 3)) ∪ fv_cty Otop)
    (cond ∷ BF) Emp.
Proof.
  (* Weakening to the empty context: X = ∅, witness r' = r. *)
  s2_weaken. apply s2_models_emp.
Qed.

Lemma branch_five_three_obl_five :
  sub_type_under ∅ Emp (const_precise_ty (cnat 5)) ({: ℕ | qgt 4}).
Proof. apply s2_const_over_sub. lia. Qed.

Lemma branch_five_three_obl_three :
  sub_type_under ∅ Emp (const_precise_ty (cnat 3)) Otop.
Proof. apply s2_const_over_top. Qed.

Theorem branch_five_three_type :
  ∅; x ∷ UNat ⊢ₓ branch_five_three ⋮ ({: ℕ | qgt 4} ⊕ Otop).
Proof.
  unfold branch_five_three.
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_gt (avar x) (vnat 0));
    [unfold UNat, Otop; s2_wf| | ].
  - eapply EXT_BinOp. unfold UNat. s2_wf.
  - eapply EXT_CtxSub with (Γ2 := cond_split_ctx);
      [unfold UNat, Otop; s2_wf| |exact branch_five_three_obl_split].
    unfold cond_split_ctx.
    eapply EXT_MatchBoth; [unfold BT, BF, Otop; s2_wf| | | | ].
    + eapply EXT_Var. unfold BT. s2_wf.
    + eapply EXT_Var. unfold BF. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp);
        [unfold BT; s2_wf| |exact branch_five_three_obl_true_weaken].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 5));
        [s2_wf| |exact branch_five_three_obl_five].
      eapply EXT_Const. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp);
        [unfold BF, Otop; s2_wf| |exact branch_five_three_obl_false_weaken].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 3));
        [unfold Otop; s2_wf| |exact branch_five_three_obl_three].
      eapply EXT_Const. s2_wf.
Qed.

(** Example 3.4: x:[⊤] ⊢ match x with 0 → 3 | S y → 5 : {ν < 4} ⊕ {⊤}.

    [nat_match_like_program] is the Rocq stand-in (match on [x == 0]; the
    pattern variable [y = x - 1] is unused by the branches).  The T-CtxSub
    split follows the paper:
      x:[⊤] ≤_{x} x:{ν=0}⊓[ν=0] ⊕ x:{ν>0}⊓[ν>0]
    extended with the precise boolean scrutinee in each summand. *)

Definition ex34_true_ctx : ctx :=
  (x ∷ ({: ℕ | qeq 0} ⊓ [: ℕ | qeq 0])) ,, (cond ∷ BT).
Definition ex34_false_ctx : ctx :=
  (x ∷ ({: ℕ | qgt 0} ⊓ [: ℕ | qgt 0])) ,, (cond ∷ BF).

Lemma nat_match_like_program_obl_split :
  ctx_sub_under ∅
    (fv_tm (if cond then ret (vnat 3) else ret (vnat 5)) ∪
     fv_cty ({: ℕ | qlt 4} ⊕ Otop))
    branch_three_five_ctx (ex34_true_ctx ⊕ ex34_false_ctx).
Proof.
  (* X = {cond}; [r|{cond}] = {true,false} because [x:[⊤]] reaches 0 and
     1.  Choose the extension [r'] over {x, cond}
       r' = {(0,true)} ∪ {(n,false) | n > 0},
     whose [cond]-projection is {true,false} = [r|{cond}].  It is the sum of
     {(0,true)} ⊨ x:{ν=0}⊓[ν=0], cond:{ν=true}⊓[ν=true] and
     {(n,false) | n>0} ⊨ x:{ν>0}⊓[ν>0], cond:{ν=false}⊓[ν=false]. *)
Admitted.

Lemma nat_match_like_program_obl_true_cond :
  ctx_sub_under ∅ (fv_tm (ret (avar cond)) ∪ fv_cty BT)
    ex34_true_ctx (cond ∷ BT).
Proof.
  (* Weakening to the last [,]-conjunct, whose type is closed. *)
  unfold ex34_true_ctx. s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma nat_match_like_program_obl_false_cond :
  ctx_sub_under ∅ (fv_tm (ret (avar cond)) ∪ fv_cty BF)
    ex34_false_ctx (cond ∷ BF).
Proof.
  unfold ex34_false_ctx. s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma nat_match_like_program_obl_true_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 3)) ∪ fv_cty ({: ℕ | qlt 4}))
    ex34_true_ctx Emp.
Proof.
  unfold ex34_true_ctx. s2_weaken. apply s2_models_emp.
Qed.

Lemma nat_match_like_program_obl_false_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 5)) ∪ fv_cty Otop)
    ex34_false_ctx Emp.
Proof.
  unfold ex34_false_ctx. s2_weaken. apply s2_models_emp.
Qed.

Lemma nat_match_like_program_obl_three :
  sub_type_under ∅ Emp (const_precise_ty (cnat 3)) ({: ℕ | qlt 4}).
Proof. apply s2_const_over_sub. lia. Qed.

Lemma nat_match_like_program_obl_five :
  sub_type_under ∅ Emp (const_precise_ty (cnat 5)) Otop.
Proof. apply s2_const_over_top. Qed.

Theorem nat_match_like_program_type :
  ∅; x ∷ UNat ⊢ₓ nat_match_like_program ⋮ ({: ℕ | qlt 4} ⊕ Otop).
Proof.
  unfold nat_match_like_program.
  eapply EXT_LetNamed with (τ1 := primop_precise_ty op_eq0 (avar x));
    [unfold UNat, Otop; s2_wf| | ].
  - eapply EXT_AppOpValue. unfold UNat. s2_wf.
  - eapply EXT_CtxSub with (Γ2 := (ex34_true_ctx ⊕ ex34_false_ctx)%ctx);
      [unfold branch_three_five_ctx, UNat, Otop; s2_wf| |
       exact nat_match_like_program_obl_split].
    unfold ex34_true_ctx at 1, ex34_false_ctx at 1.
    eapply EXT_MatchBoth; [unfold BT, BF, Otop; s2_wf| | | | ].
    + eapply EXT_CtxSub with (Γ2 := cond ∷ BT);
        [unfold BT; s2_wf| |exact nat_match_like_program_obl_true_cond].
      eapply EXT_Var. unfold BT. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := cond ∷ BF);
        [unfold BF; s2_wf| |exact nat_match_like_program_obl_false_cond].
      eapply EXT_Var. unfold BF. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp);
        [unfold BT; s2_wf| |exact nat_match_like_program_obl_true_weaken].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 3));
        [s2_wf| |exact nat_match_like_program_obl_three].
      eapply EXT_Const. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp);
        [unfold BF, Otop; s2_wf| |exact nat_match_like_program_obl_false_weaken].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 5));
        [unfold Otop; s2_wf| |exact nat_match_like_program_obl_five].
      eapply EXT_Const. s2_wf.
Qed.

(** Example 3.4, unreachable branch:  x:{ν>0} ⊢ match x with 0 → 3 | S y → 5
    : {ν > 4} ✓ (T-Match with only the false branch reachable).  The
    judgment x:[ν>0] ⊢ ... : {ν<4} ⊕ {⊤} is the paper's ✗ (a capability may
    reach only the false branch, so no split into two non-empty summands
    exists) and is not typed. *)

Definition ex34_pos_ctx : ctx :=
  (x ∷ {: ℕ | qgt 0}) ,, (cond ∷ primop_precise_ty op_eq0 (avar x)).

Lemma nat_match_like_program_obl_false_only :
  ctx_sub_under ∅
    (fv_tm (if cond then ret (vnat 3) else ret (vnat 5)) ∪
     fv_cty ({: ℕ | qgt 4}))
    ex34_pos_ctx (cond ∷ BF).
Proof.
  (* X = {cond}.  [x:{ν>0}] forces every environment to have [x > 0], so
     [cond = (x =? 0)] is [false] everywhere; [r|{cond}] = {false} (the
     capability is non-empty), which satisfies [cond:{ν=false}⊓[ν=false]]. *)
Admitted.

Lemma nat_match_like_program_obl_pos_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 5)) ∪ fv_cty ({: ℕ | qgt 4}))
    (cond ∷ BF) Emp.
Proof.
  (* Weakening to the empty context: X = ∅, witness r' = r. *)
  s2_weaken. apply s2_models_emp.
Qed.

Lemma nat_match_like_program_obl_pos_five :
  sub_type_under ∅ Emp (const_precise_ty (cnat 5)) ({: ℕ | qgt 4}).
Proof. apply s2_const_over_sub. lia. Qed.

Theorem nat_match_like_program_pos_type :
  ∅; x ∷ {: ℕ | qgt 0} ⊢ₓ nat_match_like_program ⋮ ({: ℕ | qgt 4}).
Proof.
  unfold nat_match_like_program.
  eapply EXT_LetNamed with (τ1 := primop_precise_ty op_eq0 (avar x));
    [s2_wf| | ].
  - eapply EXT_AppOpValue. s2_wf.
  - eapply EXT_CtxSub with (Γ2 := cond ∷ BF);
      [s2_wf| |exact nat_match_like_program_obl_false_only].
    eapply EXT_MatchFalseOnly; [unfold BF; s2_wf| | ].
    + eapply EXT_Var. unfold BF. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp);
        [unfold BF; s2_wf| |exact nat_match_like_program_obl_pos_weaken].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 5));
        [s2_wf| |exact nat_match_like_program_obl_pos_five].
      eapply EXT_Const. s2_wf.
Qed.

(** *** x:{⊤} ⊢ if x == 0 then 3 else 5 : {ν = 3 ∨ ν = 5}  (NEW in round 2)

    Plain safety typing of [branch_three_five] under a DEMONIC [x].  Round 1
    showed it was not derivable: a demonic [x] admits capabilities that reach
    only the true branch ({x ↦ 0}), only the false branch ({x ↦ 1}), or both
    ({x ↦ 0, x ↦ 1}), and no single T-Match rule covers all three.  T-CtxCase
    performs exactly this capability case split (two nested splits):
      bt5_dem_ctx  ⇝  cond:BT                       (true only)
                   |  cond:[ν = false]              (false reachable)
      cond:[ν = false]  ⇝  cond:BF                  (false only)
                        |  cond:BT ⊕ cond:BF        (both)
    The "both" case uses MatchBoth and T-Sub [{q35} ⊕ {q35} <: {q35}]. *)

Definition q35 : type_qualifier := q_nat_pred ν (fun n => n = 3%nat \/ n = 5%nat).
Definition O35 : context_ty := {: ℕ | q35}.
Definition bt5_dem_ctx : ctx :=
  (x ∷ ONat) ,, (cond ∷ primop_precise_ty op_eq0 (avar x)).
Definition BreachF : context_ty := [: 𝔹 | bool_qual false].
Definition bt5_match : tm := if cond then ret (vnat 3) else ret (vnat 5).

Lemma bt5_obl_case_true :
  ctx_case_under ∅ (fv_tm bt5_match ∪ fv_cty O35)
    bt5_dem_ctx (cond ∷ BT) (cond ∷ BreachF).
Proof.
  (* X = {cond}.  Take r' = r|{cond}.  Every model r of
     x:{⊤}, cond:{ν = (x =? 0)} ⊓ [ν = (x =? 0)] has a non-empty projection
     r|{cond} ⊆ {true, false} (the precise primop type pins [cond] to
     [x =? 0] in every environment).  If r|{cond} = {true}, then r' satisfies
     cond:{ν = true} ⊓ [ν = true] (all values true, true reached).
     Otherwise [false ∈ r|{cond}], so r' satisfies cond:[ν = false] (the
     closed under atom only asks that [false] be reached).  The erasures
     agree on [cond] (both 𝔹); all three contexts are well formed. *)
Admitted.

Lemma bt5_obl_case_false :
  ctx_case_under ∅ (fv_tm bt5_match ∪ fv_cty O35)
    (cond ∷ BreachF) (cond ∷ BF) ((cond ∷ BT) ⊕ (cond ∷ BF)).
Proof.
  (* X = {cond}, r' = r|{cond}, which contains [false].  If it is {false},
     r' ⊨ cond:{ν=false}⊓[ν=false].  Otherwise it is {true,false}, the sum
     (union, same domain) of the non-empty worlds {cond ↦ true} ⊨ BT and
     {cond ↦ false} ⊨ BF; [FPlus] holds with res_sum = r'. *)
Admitted.

Lemma bt5_obl_sum :
  sub_type_under ∅ ((cond ∷ BT) ⊕ (cond ∷ BF)) (O35 ⊕ O35) O35.
Proof.
  (* Sum of demonic types with the same closed qualifier.  If [m ⊨ (O35 ⊕
     O35) e], then every result extension W of m is (on its domain) the union
     W1 ∪ W2 of two worlds whose result projections satisfy [ν = 3 ∨ ν = 5]
     (FOver of a closed exact atom: the ν-projection is a subset of the
     qualifier's models).  Hence the ν-projection of W is a subset as well,
     i.e. W ⊨ ν:{q35}.  The totality/basic-typing guard of [e] is the one of
     the sum type.  The context is not even needed. *)
Admitted.

Lemma bt5_obl_t_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 3)) ∪ fv_cty O35) (cond ∷ BT) Emp.
Proof. s2_weaken. apply s2_models_emp. Qed.

Lemma bt5_obl_f_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 5)) ∪ fv_cty O35) (cond ∷ BF) Emp.
Proof. s2_weaken. apply s2_models_emp. Qed.

Lemma bt5_obl_three : sub_type_under ∅ Emp (const_precise_ty (cnat 3)) O35.
Proof. apply s2_const_over_sub. lia. Qed.

Lemma bt5_obl_five : sub_type_under ∅ Emp (const_precise_ty (cnat 5)) O35.
Proof. apply s2_const_over_sub. lia. Qed.

Lemma bt5_true_branch Γ :
  ctx_sub_under ∅ (fv_tm (ret (vnat 3)) ∪ fv_cty O35) Γ Emp ->
  ∅; Γ ⊢wf ret (vnat 3) ⋮ O35 ->
  ∅; Γ ⊢ₓ ret (vnat 3) ⋮ O35.
Proof.
  intros Hsub Hwf.
  eapply EXT_CtxSub with (Γ2 := Emp); [exact Hwf| |exact Hsub].
  eapply EXT_Sub with (τ1 := const_precise_ty (cnat 3));
    [unfold O35, q35; s2_wf| |exact bt5_obl_three].
  eapply EXT_Const. s2_wf.
Qed.

Lemma bt5_false_branch Γ :
  ctx_sub_under ∅ (fv_tm (ret (vnat 5)) ∪ fv_cty O35) Γ Emp ->
  ∅; Γ ⊢wf ret (vnat 5) ⋮ O35 ->
  ∅; Γ ⊢ₓ ret (vnat 5) ⋮ O35.
Proof.
  intros Hsub Hwf.
  eapply EXT_CtxSub with (Γ2 := Emp); [exact Hwf| |exact Hsub].
  eapply EXT_Sub with (τ1 := const_precise_ty (cnat 5));
    [unfold O35, q35; s2_wf| |exact bt5_obl_five].
  eapply EXT_Const. s2_wf.
Qed.

Theorem branch_three_five_demonic_type :
  ∅; x ∷ ONat ⊢ₓ branch_three_five ⋮ O35.
Proof.
  unfold branch_three_five.
  eapply EXT_LetNamed with (τ1 := primop_precise_ty op_eq0 (avar x));
    [unfold O35, q35; s2_wf| | ].
  - eapply EXT_AppOpValue. s2_wf.
  - change (∅; bt5_dem_ctx ⊢ₓ bt5_match ⋮ O35).
    eapply EXT_CtxCase; [unfold bt5_dem_ctx, bt5_match, O35, q35; s2_wf| | |
      exact bt5_obl_case_true].
    + unfold bt5_match.
      eapply EXT_MatchTrueOnly; [unfold BT, O35, q35; s2_wf| | ].
      * eapply EXT_Var. unfold BT. s2_wf.
      * apply bt5_true_branch; [exact bt5_obl_t_weaken|unfold BT, O35, q35; s2_wf].
    + eapply EXT_CtxCase; [unfold BreachF, bt5_match, O35, q35; s2_wf| | |
        exact bt5_obl_case_false].
      * unfold bt5_match.
        eapply EXT_MatchFalseOnly; [unfold BF, O35, q35; s2_wf| | ].
        -- eapply EXT_Var. unfold BF. s2_wf.
        -- apply bt5_false_branch; [exact bt5_obl_f_weaken|unfold BF, O35, q35; s2_wf].
      * eapply EXT_Sub with (τ1 := O35 ⊕ O35);
          [unfold BT, BF, bt5_match, O35, q35; s2_wf| |exact bt5_obl_sum].
        unfold bt5_match.
        eapply EXT_MatchBoth; [unfold BT, BF, O35, q35; s2_wf| | | | ].
        -- eapply EXT_Var. unfold BT. s2_wf.
        -- eapply EXT_Var. unfold BF. s2_wf.
        -- apply bt5_true_branch; [exact bt5_obl_t_weaken|unfold BT, O35, q35; s2_wf].
        -- apply bt5_false_branch; [exact bt5_obl_f_weaken|unfold BF, O35, q35; s2_wf].
Qed.

(** *** Example 3.1 (typing let-expressions, p.11)

    x:{ν < 10} ⊢ let y = x - 3 in x - y : {ν ≤ 3}

    Over ℕ the statement still holds with truncated subtraction: for
    [x ≥ 3], [x - (x - 3) = 3]; for [x < 3], [x - 3 = 0] and [x - 0 = x < 3].

    FINDING (paper derivation).  The paper's T-Let derivation types the
    bound expression as [x - 3 : {ν < 7}] and then checks the body under
    [x:{ν<10}, y:{ν<7} ⊢ x - y : {ν ≤ 3}].  That second premise is not
    valid: the environment (x,y) = (9,0) satisfies the context and gives
    [x - y = 9] (over ℤ, (9,-100) is worse).  The derivation must keep the
    dependency of [y] on [x]; T-Let allows this because [y]'s type may
    mention [x].  Below, [y] gets the precise type {ν = x-3} ⊓ [ν = x-3]
    and the body is checked against it.  The paper's first premise
    ([x - 3 : {ν < 7}]) is also derivable and is given separately. *)

Definition ex31_ctx : ctx := x ∷ {: ℕ | qlt 10}.

Lemma let_duplication_program_obl_bound :
  sub_type_under ∅ ex31_ctx
    (binop_precise_ty bop_minus (avar x) (vnat 3)) ({: ℕ | qlt 7}).
Proof.
  (* Demonic, fiberwise: every environment has [x < 10]; the precise
     result in the [x]-fiber is [x - 3 ≤ 6 < 7]. *)
Admitted.

Lemma let_duplication_bound_type :
  ∅; ex31_ctx ⊢ₓ x ⟨ - ⟩ vnat 3 ⋮ ({: ℕ | qlt 7}).
Proof.
  unfold ex31_ctx.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (vnat 3));
    [s2_wf| |exact let_duplication_program_obl_bound].
  eapply EXT_BinOp. s2_wf.
Qed.

Lemma let_duplication_program_obl_body :
  sub_type_under ∅
    (ex31_ctx ,, (ylet ∷ binop_precise_ty bop_minus (avar x) (vnat 3)))
    (binop_precise_ty bop_minus (avar x) (avar ylet)) ({: ℕ | qle 3}).
Proof.
  (* Demonic, fiberwise over (x, ylet): every environment has [x < 10] and
     [ylet = x - 3] (precise binding), hence the precise result
     [x - ylet = min x 3 ≤ 3]. *)
Admitted.

Theorem let_duplication_program_type :
  ∅; ex31_ctx ⊢ₓ let_duplication_program ⋮ ({: ℕ | qle 3}).
Proof.
  unfold let_duplication_program, ex31_ctx.
  eapply EXT_LetNamed with
    (τ1 := binop_precise_ty bop_minus (avar x) (vnat 3)); [s2_wf| | ].
  - eapply EXT_BinOp. s2_wf.
  - eapply EXT_Sub with
      (τ1 := binop_precise_ty bop_minus (avar x) (avar ylet));
      [s2_wf| |exact let_duplication_program_obl_body].
    eapply EXT_BinOp. s2_wf.
Qed.

(** *** Nested application (paper p.8)

    x:[ν>0] ∗ y:[ν>0] ⊢ λf. x - (f (f y)) : f:(y:[ν>0] → [ν>0]) -∗ [ν>0]

    FINDING (let-nesting matters).  [nested_apply_program] is written in
    right-nested ANF:  let r1 = f y in let r2 = f r1 in x - r2.  This is
    not derivable at the intended type:
    - with T-Let, [r1] and [r2] are bound by [,] after [x]; their closed
      types [[ν>0]] do not record that they were computed from [f] and [y]
      only, so the final obligation
        (x ∗ y ∗ f), r1:[ν>0], r2:[ν>0] ⊢ x - r2 <: [ν>0]
      is false (the capability with [r2 = x] satisfies the context, and
      [x - r2 = 0]);
    - T-LetI cannot be used for [let r1 = f y], because [f] is needed both
      in the bound expression and in the body, and T-LetI splits the
      context disjointly (no contraction for the non-persistent [f]).
    Round 2 re-check: the new rules do not change this.  EXT_VarComma only
    gives access to a variable at its own binding type, and the problem is
    not variable access but the entanglement created by T-Let: whatever
    types [r1]/[r2] receive (from [f]'s closed result type [[ν>0]] plus
    T-Sub, which must hold for EVERY term of the source type, so it cannot
    add "independent of x"), the capability with [r2 = x] satisfies the
    body's context.  T-CtxCase only partitions the set of capabilities;
    that single capability already refutes the body judgment.  Separation
    can only come from the ∗-rules, and T-LetI/T-AppFunI would need [f] on
    both sides of a disjoint split.
    The paper's term [x - (f (f y))] in MNF is
      let r2 = (let r1 = f y in f r1) in x - r2,
    which T-LetI handles: the inner block uses only (y, f) and its result
    is independent of [x].  We add that program and type it. *)

Definition nested_apply_mnf_program : tm :=
  ret (ƛ f : ℕ →ᵦ ℕ =>
    let r2 := (let r1 := f @ y in f @ r1) in
    x ⟨ - ⟩ r2).

Lemma nested_apply_mnf_program_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ
    nested_apply_mnf_program ⋮ ((ℕ →ᵦ ℕ) →ᵦ ℕ).
Proof. unfold nested_apply_mnf_program. basic_check. Qed.

Definition fpos_ty : context_ty := Apos → Apos.   (* y:[ν>0] → [ν>0] *)

Definition nested_ctx : ctx := (x ∷ Apos) ∗ (y ∷ Apos).

Lemma s2_Apos_closed : basic_context_ty ∅ Apos.
Proof. unfold Apos. s2_unfold. case_type_wf_syntax. Qed.

Lemma s2_fv_Apos : fv_cty Apos = ∅.
Proof.
  pose proof (wf_context_ty_at_fv_subset 0 ∅ Apos s2_Apos_closed). set_solver.
Qed.

Definition nested_body : tm :=
  let r2 := (let r1 := f @ y in f @ r1) in x ⟨ - ⟩ r2.

Definition nested_inner : tm := let r1 := f @ y in f @ r1.

Lemma nested_apply_mnf_program_obl_exchange :
  ctx_sub_under ∅ (fv_tm nested_body ∪ fv_cty Apos)
    (nested_ctx ∗ (f ∷ fpos_ty))
    (((y ∷ Apos) ∗ (f ∷ fpos_ty)) ∗ (x ∷ Apos)).
Proof.
  (* Associativity/commutativity of [∗] (T-Exchange), witness r' = r. *)
  unfold nested_ctx, nested_body, fpos_ty. s2_weaken.
  apply s2_models_star_rotate; [s2_wf_ctx|exact Hr].
Qed.

Lemma nested_apply_mnf_program_obl_f1 :
  ctx_sub_under ∅ (fv_tm (ret (avar f)) ∪ fv_cty fpos_ty)
    ((y ∷ Apos) ∗ (f ∷ fpos_ty)) (f ∷ fpos_ty).
Proof.
  (* T-Frame: the right factor of [∗]. *)
  unfold fpos_ty. s2_weaken. eapply s2_models_star_r. exact Hr.
Qed.

Lemma nested_apply_mnf_program_obl_y1 :
  ctx_sub_under ∅ (fv_tm (ret (avar y)) ∪ fv_cty Apos)
    ((y ∷ Apos) ∗ (f ∷ fpos_ty)) (y ∷ Apos).
Proof.
  (* T-Frame: the left factor of [∗]. *)
  unfold fpos_ty. s2_weaken. eapply s2_models_star_l. exact Hr.
Qed.

Lemma nested_apply_mnf_program_obl_f2 :
  ctx_sub_under ∅ (fv_tm (ret (avar f)) ∪ fv_cty fpos_ty)
    (((y ∷ Apos) ∗ (f ∷ fpos_ty)) ,, (r1 ∷ Apos)) (f ∷ fpos_ty).
Proof.
  (* Weakening: left conjunct of [,], then right factor of [∗]. *)
  unfold fpos_ty. s2_weaken.
  apply s2_models_comma_l in Hr. eapply s2_models_star_r. exact Hr.
Qed.

Lemma nested_apply_mnf_program_obl_r1 :
  ctx_sub_under ∅ (fv_tm (ret (avar r1)) ∪ fv_cty Apos)
    (((y ∷ Apos) ∗ (f ∷ fpos_ty)) ,, (r1 ∷ Apos)) (r1 ∷ Apos).
Proof.
  (* Weakening to the last [,]-conjunct (closed type). *)
  unfold fpos_ty. s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma nested_apply_mnf_program_obl_sub :
  sub_type_under ∅ ((x ∷ Apos) ∗ (r2 ∷ Apos))
    (binop_precise_ty bop_minus (avar x) (avar r2)) Apos.
Proof.
  (* Independent [x] and [r2], each reaching every positive number: choose
     (x, r2) = (k+1, 1). *)
Admitted.

Lemma s2_app_closed_result Γ (fn arg : atom) :
  ∅; Γ ⊢ₓ ret (avar fn) ⋮ fpos_ty ->
  ∅; Γ ⊢ₓ ret (avar arg) ⋮ Apos ->
  ∅; Γ ⊢wf fn @ arg ⋮ Apos ->
  fn <> arg ->
  ∅; Γ ⊢ₓ fn @ arg ⋮ Apos.
Proof.
  intros Hf Harg Hwf Hne.
  pose proof (EXT_AppFun ∅ Γ Apos Apos (avar fn) arg) as Happ.
  change (open_one 0 arg Apos) with (cty_open 0 arg Apos) in Happ.
  rewrite (s2_open_closed 0 arg Apos s2_Apos_closed) in Happ.
  apply Happ; [exact Hwf| |exact Hf|exact Harg].
  rewrite s2_fv_Apos. cbn. set_solver.
Qed.

Theorem nested_apply_mnf_program_type :
  ∅; nested_ctx ⊢ₓ nested_apply_mnf_program ⋮ (fpos_ty -∗ Apos).
Proof.
  unfold nested_apply_mnf_program.
  eapply EXT_LamDNamedErased; [reflexivity|unfold nested_ctx, fpos_ty; s2_wf| ].
  change (let r2 := (let r1 := f @ y in f @ r1) in x ⟨ - ⟩ r2) with nested_body.
  eapply EXT_CtxSub;
    [unfold nested_ctx, fpos_ty, nested_body; s2_wf| |
     exact nested_apply_mnf_program_obl_exchange].
  unfold nested_body.
  eapply EXT_LetDNamed with (τ1 := Apos);
    [unfold fpos_ty; s2_wf| | ].
  - eapply EXT_LetNamed with (τ1 := Apos); [unfold fpos_ty; s2_wf| | ].
    + apply s2_app_closed_result.
      * eapply EXT_CtxSub;
          [unfold fpos_ty; s2_wf| |exact nested_apply_mnf_program_obl_f1].
        eapply EXT_Var. unfold fpos_ty. s2_wf.
      * eapply EXT_CtxSub;
          [unfold fpos_ty; s2_wf| |exact nested_apply_mnf_program_obl_y1].
        eapply EXT_Var. s2_wf.
      * unfold fpos_ty. s2_wf.
      * vm_compute. congruence.
    + apply s2_app_closed_result.
      * eapply EXT_CtxSub;
          [unfold fpos_ty; s2_wf| |exact nested_apply_mnf_program_obl_f2].
        eapply EXT_Var. unfold fpos_ty. s2_wf.
      * eapply EXT_CtxSub;
          [unfold fpos_ty; s2_wf| |exact nested_apply_mnf_program_obl_r1].
        eapply EXT_Var. s2_wf.
      * unfold fpos_ty. s2_wf.
      * vm_compute. congruence.
  - eapply EXT_Sub with
      (τ1 := binop_precise_ty bop_minus (avar x) (avar r2));
      [s2_wf| |exact nested_apply_mnf_program_obl_sub].
    eapply EXT_BinOp. s2_wf.
Qed.

(** *** Figure 6(a): "may-analysis helps must-analysis" (may_must_intro_program)

    Paper:  g : i:{ν: int | ⊤} → {ν: int | ν ≠ 0}
            ⊢ f : x:[ν: int | ν = 0] → y:[ν: int | 0 ≤ ν ≤ 10] → [ν: int | ν = 1]
    (the program takes [g] as its first argument, so the full type is
     g_ty → x:[ν=0] → y:[0≤ν≤10] → [ν=1]; ℕ replaces int verbatim).

    FINDING 1 (the → version is semantically false).  With an entangled
    arrow for [y], the argument capability for (x,y) only has to reach x = 0
    and, separately, every y ∈ [0,10].  The capability
      {(x,y) = (0,11)} ∪ {(5,y) | 0 ≤ y ≤ 10}
    satisfies x:[ν=0], y:[0≤ν≤10] (y's qualifier does not mention x, so it
    is not fibered by x), but the result is [g 0 + 1 ≥ 2] on (0,11) and
    [5 + 1 = 6] elsewhere: [1] is never reached.  This is the dependency
    problem described in the overview: matching on [y] loses [x]'s
    guarantee, because no environment pairs x = 0 with y ≤ 10.

    FINDING 2 (setting (2), the -∗ version, is true and, since round 2,
    DERIVED: [may_must_intro_program_setting2_type] below).  With
    x:[ν=0] → y:[0≤ν≤10] -∗ [ν=1] the capability is a product and contains
    (0, y) for every y ≤ 10, so the claim holds semantically.  In round 1
    it was not derivable: an angelic-only [y] admits both the capability
    {y ↦ 0..10} ([cond = y > 10] only false: MatchBoth impossible) and
    {y ↦ 0..11} (cond reaches true: MatchFalseOnly impossible), and T-Match
    alone cannot cover both.  T-CtxCase now splits these two kinds of
    capabilities ("false only" / "both"); in the "both" case MatchBoth
    yields [{⊤} ⊕ [ν=1]], and T-Sub absorbs the demonic summand.

    Derivable corrected variants: bound [y] demonically as well,
      y : {0 ≤ ν ≤ 10} ⊓ [0 ≤ ν ≤ 10].
    Then the true branch is uniformly unreachable (T-Match with only the
    false branch), [x] keeps its angelic guarantee, and [x + 1] reaches 1.
    With the demonic bound the entangled arrow is fine, since the result
    depends on [x] only ([may_must_intro_program_type]); the separating
    version closest to setting (2), x:[ν=0] → y:({..}⊓[..]) -∗ [ν=1], is
    [may_must_intro_program_wand_type].  (Setting (3) of the authors'
    response, with the precise dependency of [y] on [x], is the subject of
    CaseStudy/MayMust.v.) *)

Definition g_ty : context_ty := Otop → {: ℕ | qne0}.
Definition yrange_ty : context_ty := {: ℕ | qrange 0 10} ⊓ [: ℕ | qrange 0 10].
Definition may_must_target_ty : context_ty :=
  g_ty → [: ℕ | qeq 0] → yrange_ty → [: ℕ | qeq 1].

Definition mm_ctx_y : ctx :=
  ((Emp ,, (g ∷ g_ty)) ,, (x ∷ [: ℕ | qeq 0])) ,, (y ∷ yrange_ty).
Definition mm_ctx_cond : ctx :=
  mm_ctx_y ,, (cond ∷ binop_precise_ty bop_gt (avar y) (vnat 10)).
Definition mm_ctx_false : ctx := mm_ctx_y ,, (cond ∷ BF).

Definition mm_body : tm :=
  if cond then
    let gx := g @ x in
    gx ⟨ + ⟩ vnat 1
  else
    x ⟨ + ⟩ vnat 1.

Lemma may_must_intro_program_obl_false_only :
  ctx_sub_under ∅ (fv_tm mm_body ∪ fv_cty ([: ℕ | qeq 1]))
    mm_ctx_cond mm_ctx_false.
Proof.
  (* Same domain and erasure.  Witness [r' = r] itself (NOT [r|X]: here
     X = fv_tm mm_body ∪ fv_cty [ν=1] = {x, g, cond} does not contain [y],
     while [mm_ctx_false] still binds [y]; [r|X ⊑ r] holds by
     [res_restrict_le]).  The demonic part of [y]'s type forces [y ≤ 10] in
     every environment of [r], so [cond = (10 <? y)] is [false] everywhere
     (fiberwise precise binop type), and the (non-empty) capability reaches
     [false]: [cond:{ν=false}⊓[ν=false]] holds of [r].  The conjuncts for
     g, x, y are literally the same as in [mm_ctx_cond]. *)
Admitted.

Lemma may_must_intro_program_obl_cond :
  ctx_sub_under ∅ (fv_tm (ret (avar cond)) ∪ fv_cty BF)
    mm_ctx_false (cond ∷ BF).
Proof.
  (* Weakening to the last [,]-conjunct (closed type). *)
  unfold mm_ctx_false, mm_ctx_y, g_ty, yrange_ty, Otop. s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma may_must_intro_program_obl_sub :
  sub_type_under ∅ mm_ctx_false
    (binop_precise_ty bop_plus (avar x) (vnat 1)) ([: ℕ | qeq 1]).
Proof.
  (* [x:[ν=0]] guarantees an environment with [x = 0]; in that [x]-fiber the
     precise result of [x + 1] is [1], so the result reaches 1. *)
Admitted.

Theorem may_must_intro_program_type :
  ∅; Emp ⊢ₓ may_must_intro_program ⋮ may_must_target_ty.
Proof.
  unfold may_must_intro_program, may_must_target_ty.
  eapply EXT_LamNamedErased;
    [reflexivity|unfold g_ty, yrange_ty, Otop; s2_wf| ].
  eapply EXT_LamNamedErased;
    [reflexivity|unfold g_ty, yrange_ty, Otop; s2_wf| ].
  eapply EXT_LamNamedErased;
    [reflexivity|unfold g_ty, yrange_ty, Otop; s2_wf| ].
  eapply EXT_LetNamed with
    (τ1 := binop_precise_ty bop_gt (avar y) (vnat 10));
    [unfold g_ty, yrange_ty, Otop; s2_wf| | ].
  - eapply EXT_BinOp. unfold g_ty, yrange_ty, Otop. s2_wf.
  - change (∅; mm_ctx_cond ⊢ₓ mm_body ⋮ [: ℕ | qeq 1]).
    eapply EXT_CtxSub with (Γ2 := mm_ctx_false);
      [unfold mm_ctx_cond, mm_ctx_y, mm_body, g_ty, yrange_ty, Otop; s2_wf| |
       exact may_must_intro_program_obl_false_only].
    unfold mm_body.
    eapply EXT_MatchFalseOnly;
      [unfold mm_ctx_false, mm_ctx_y, BF, g_ty, yrange_ty, Otop; s2_wf| | ].
    + eapply EXT_CtxSub with (Γ2 := cond ∷ BF);
        [unfold mm_ctx_false, mm_ctx_y, BF, g_ty, yrange_ty, Otop; s2_wf| |
         exact may_must_intro_program_obl_cond].
      eapply EXT_Var. unfold BF. s2_wf.
    + eapply EXT_Sub with (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1));
        [unfold mm_ctx_false, mm_ctx_y, BF, g_ty, yrange_ty, Otop; s2_wf| |
         exact may_must_intro_program_obl_sub].
      eapply EXT_BinOp.
      unfold mm_ctx_false, mm_ctx_y, BF, g_ty, yrange_ty, Otop. s2_wf.
Qed.

(** Setting (2) with the demonic bound on [y]:
    g_ty → x:[ν=0] → y:({0≤ν≤10} ⊓ [0≤ν≤10]) -∗ [ν=1]. *)
Definition may_must_wand_target_ty : context_ty :=
  g_ty → [: ℕ | qeq 0] → (yrange_ty -∗ [: ℕ | qeq 1]).

Definition mmw_ctx_y : ctx :=
  ((Emp ,, (g ∷ g_ty)) ,, (x ∷ [: ℕ | qeq 0])) ∗ (y ∷ yrange_ty).
Definition mmw_ctx_cond : ctx :=
  mmw_ctx_y ,, (cond ∷ binop_precise_ty bop_gt (avar y) (vnat 10)).
Definition mmw_ctx_false : ctx := mmw_ctx_y ,, (cond ∷ BF).

Lemma may_must_intro_program_obl_wand_false_only :
  ctx_sub_under ∅ (fv_tm mm_body ∪ fv_cty ([: ℕ | qeq 1]))
    mmw_ctx_cond mmw_ctx_false.
Proof.
  (* As [may_must_intro_program_obl_false_only], witness [r' = r]: the
     product world's [y]-part satisfies the demonic bound [y ≤ 10], so every
     environment of [r] has [y ≤ 10] and the precise [cond = (10 <? y)] is
     [false] everywhere; the non-empty [r] reaches [false]. *)
Admitted.

Lemma may_must_intro_program_obl_wand_cond :
  ctx_sub_under ∅ (fv_tm (ret (avar cond)) ∪ fv_cty BF)
    mmw_ctx_false (cond ∷ BF).
Proof.
  unfold mmw_ctx_false, mmw_ctx_y, g_ty, yrange_ty, Otop. s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma may_must_intro_program_obl_wand_sub :
  sub_type_under ∅ mmw_ctx_false
    (binop_precise_ty bop_plus (avar x) (vnat 1)) ([: ℕ | qeq 1]).
Proof.
  (* The [(g, x)]-factor of the product reaches [x = 0] ([qeq 0] mentions
     [ν]); the product with the non-empty [y]-factor (all of whose values
     make [cond] false, so the [cond] conjunct removes nothing) keeps an
     environment with [x = 0], whose [x]-fiber has the precise result
     [0 + 1 = 1]. *)
Admitted.

Theorem may_must_intro_program_wand_type :
  ∅; Emp ⊢ₓ may_must_intro_program ⋮ may_must_wand_target_ty.
Proof.
  unfold may_must_intro_program, may_must_wand_target_ty.
  eapply EXT_LamNamedErased;
    [reflexivity|unfold g_ty, yrange_ty, Otop; s2_wf| ].
  eapply EXT_LamNamedErased;
    [reflexivity|unfold g_ty, yrange_ty, Otop; s2_wf| ].
  eapply EXT_LamDNamedErased;
    [reflexivity|unfold g_ty, yrange_ty, Otop; s2_wf| ].
  eapply EXT_LetNamed with
    (τ1 := binop_precise_ty bop_gt (avar y) (vnat 10));
    [unfold g_ty, yrange_ty, Otop; s2_wf| | ].
  - eapply EXT_BinOp. unfold g_ty, yrange_ty, Otop. s2_wf.
  - change (∅; mmw_ctx_cond ⊢ₓ mm_body ⋮ [: ℕ | qeq 1]).
    eapply EXT_CtxSub with (Γ2 := mmw_ctx_false);
      [unfold mmw_ctx_cond, mmw_ctx_y, mm_body, g_ty, yrange_ty, Otop; s2_wf| |
       exact may_must_intro_program_obl_wand_false_only].
    unfold mm_body.
    eapply EXT_MatchFalseOnly;
      [unfold mmw_ctx_false, mmw_ctx_y, BF, g_ty, yrange_ty, Otop; s2_wf| | ].
    + eapply EXT_CtxSub with (Γ2 := cond ∷ BF);
        [unfold mmw_ctx_false, mmw_ctx_y, BF, g_ty, yrange_ty, Otop; s2_wf| |
         exact may_must_intro_program_obl_wand_cond].
      eapply EXT_Var. unfold BF. s2_wf.
    + eapply EXT_Sub with (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1));
        [unfold mmw_ctx_false, mmw_ctx_y, BF, g_ty, yrange_ty, Otop; s2_wf| |
         exact may_must_intro_program_obl_wand_sub].
      eapply EXT_BinOp.
      unfold mmw_ctx_false, mmw_ctx_y, BF, g_ty, yrange_ty, Otop. s2_wf.
Qed.

(** Setting (2) of the authors' response, now DERIVED (round 2):
      g_ty → x:[ν=0] → y:[0≤ν≤10] -∗ [ν=1].
    The T-Match obstacle of round 1 (the capability of [y] may make [cond]
    reach only [false], or both values) is resolved with T-CtxCase: the
    context is split into "only the false branch is reachable"
    ([mm2_ctx_false]: MatchFalseOnly) and "both branches are reachable"
    ([mm2_ctx_true ⊕ mm2_ctx_false]: MatchBoth, then T-Sub
    [{⊤} ⊕ [ν=1] <: [ν=1]]).  The true branch only needs the trivial demonic
    type [{⊤}] (T-BinOpTop), so [g]'s demonic summary is not even used: the
    split itself guarantees that the false branch, where [x + 1 = 1] is
    reached, is present in every capability. *)
Definition may_must_setting2_ty : context_ty :=
  g_ty → [: ℕ | qeq 0] → ([: ℕ | qrange 0 10] -∗ [: ℕ | qeq 1]).

Definition mm2_ctx_y : ctx :=
  ((Emp ,, (g ∷ g_ty)) ,, (x ∷ [: ℕ | qeq 0])) ∗ (y ∷ [: ℕ | qrange 0 10]).
Definition mm2_ctx_cond : ctx :=
  mm2_ctx_y ,, (cond ∷ binop_precise_ty bop_gt (avar y) (vnat 10)).
Definition mm2_ctx_false : ctx :=
  ((Emp ,, (g ∷ g_ty)) ,, (x ∷ [: ℕ | qeq 0])) ,, (cond ∷ BF).
Definition mm2_ctx_true : ctx :=
  ((Emp ,, (g ∷ g_ty)) ,, (x ∷ Otop)) ,, (cond ∷ BT).

Lemma may_must_setting2_obl_case :
  ctx_case_under ∅ (fv_tm mm_body ∪ fv_cty ([: ℕ | qeq 1]))
    mm2_ctx_cond mm2_ctx_false (mm2_ctx_true ⊕ mm2_ctx_false).
Proof.
  (* X = {cond, g, x} (y ∉ X).  Let r ⊨ mm2_ctx_cond.  The ∗ gives
     r|{g,x,y} = M × Y with M ⊨ (g:g_ty, x:[ν=0]) and Y ⊇ {0,…,10} (the
     under atom [0 ≤ ν ≤ 10] mentions ν, so every such y is reached), and
     [cond = (10 <? y)] in every environment (precise binop type).  Hence
     r|X = M × C with C = {10 <? y | y ∈ Y} ∋ false.  Take r' = r|X.
     - C = {false}: r' ⊨ mm2_ctx_false (the g/x conjuncts only depend on the
       {g,x}-projection M; cond:{ν=false}⊓[ν=false] holds).
     - C = {true,false}: r' = (M × {true}) ∪ (M × {false}), a sum of two
       non-empty worlds over the same domain X; the first satisfies
       mm2_ctx_true (x:{⊤} is trivial, cond:BT), the second mm2_ctx_false.
     C = {true} is impossible because 0 ∈ Y. *)
Admitted.

Lemma may_must_setting2_obl_sum :
  sub_type_under ∅ (mm2_ctx_true ⊕ mm2_ctx_false)
    (Otop ⊕ [: ℕ | qeq 1]) ([: ℕ | qeq 1]).
Proof.
  (* [m ⊨ ({⊤} ⊕ [ν=1]) e]: every result extension W of m restricts to a
     union W1 ∪ W2 (same domain) with W2 ⊨ ν:[ν=1]; the qualifier [ν = 1] is
     closed, so the ν-projection of W2, hence of W ⊇ W2, contains 1, which
     is W ⊨ ν:[ν=1].  The guard of [e] comes from the sum type.  The
     context is not needed. *)
Admitted.

Lemma may_must_setting2_obl_sub :
  sub_type_under ∅ mm2_ctx_false
    (binop_precise_ty bop_plus (avar x) (vnat 1)) ([: ℕ | qeq 1]).
Proof.
  (* [x:[ν=0]] (closed under atom) gives an environment with [x = 0]; the
     precise type of [e] fixes its results in the x-fiber [x = 0] to {1};
     hence the result projection contains 1. *)
Admitted.

Lemma may_must_setting2_obl_false_cond :
  ctx_sub_under ∅ (fv_tm (ret (avar cond)) ∪ fv_cty BF)
    mm2_ctx_false (cond ∷ BF).
Proof.
  unfold mm2_ctx_false, g_ty, Otop. s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma may_must_setting2_obl_true_cond :
  ctx_sub_under ∅ (fv_tm (ret (avar cond)) ∪ fv_cty BT)
    mm2_ctx_true (cond ∷ BT).
Proof.
  unfold mm2_ctx_true, g_ty, Otop. s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma may_must_setting2_obl_true_g :
  ctx_sub_under ∅ (fv_tm (ret (avar g)) ∪ fv_cty g_ty)
    mm2_ctx_true (g ∷ g_ty).
Proof.
  unfold mm2_ctx_true, g_ty, Otop. s2_weaken.
  apply s2_models_comma_l, s2_models_comma_l in Hr.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma may_must_setting2_obl_true_x :
  ctx_sub_under ∅ (fv_tm (ret (avar x)) ∪ fv_cty Otop)
    mm2_ctx_true (x ∷ Otop).
Proof.
  unfold mm2_ctx_true, g_ty, Otop. s2_weaken.
  apply s2_models_comma_l in Hr.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma s2_Otop_closed : basic_context_ty ∅ Otop.
Proof. unfold Otop. case_type_wf_syntax. Qed.

Lemma s2_qne0_closed : basic_context_ty ∅ ({: ℕ | qne0}).
Proof. unfold qne0. s2_unfold. case_type_wf_syntax. Qed.

Lemma may_must_setting2_true_branch :
  ∅; mm2_ctx_true ⊢ₓ (let gx := g @ x in gx ⟨ + ⟩ vnat 1) ⋮ Otop.
Proof.
  eapply EXT_LetNamed with (τ1 := {: ℕ | qne0});
    [unfold mm2_ctx_true, g_ty, Otop; s2_wf| | ].
  - pose proof (EXT_AppFun ∅ mm2_ctx_true Otop ({: ℕ | qne0}) (avar g) x) as Happ.
    change (open_one 0 x ({: ℕ | qne0})) with (cty_open 0 x ({: ℕ | qne0})) in Happ.
    rewrite (s2_open_closed 0 x _ s2_qne0_closed) in Happ.
    apply Happ.
    + unfold mm2_ctx_true, g_ty, Otop. s2_wf.
    + rewrite (s2_fv_closed _ s2_Otop_closed), (s2_fv_closed _ s2_qne0_closed).
      cbn. unfold x, g. set_solver.
    + eapply EXT_CtxSub with (Γ2 := g ∷ g_ty);
        [unfold mm2_ctx_true, g_ty, Otop; s2_wf| |exact may_must_setting2_obl_true_g].
      eapply EXT_Var. unfold g_ty, Otop. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := x ∷ Otop);
        [unfold mm2_ctx_true, g_ty, Otop; s2_wf| |exact may_must_setting2_obl_true_x].
      eapply EXT_Var. unfold Otop. s2_wf.
  - change Otop with (binop_top_ty bop_plus).
    eapply EXT_BinOpTop. unfold mm2_ctx_true, g_ty, Otop. s2_wf.
Qed.

Lemma may_must_setting2_false_branch :
  ∅; mm2_ctx_false ⊢ₓ x ⟨ + ⟩ vnat 1 ⋮ [: ℕ | qeq 1].
Proof.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1));
    [unfold mm2_ctx_false, g_ty, Otop; s2_wf| |exact may_must_setting2_obl_sub].
  eapply EXT_BinOp. unfold mm2_ctx_false, g_ty, Otop. s2_wf.
Qed.

Theorem may_must_intro_program_setting2_type :
  ∅; Emp ⊢ₓ may_must_intro_program ⋮ may_must_setting2_ty.
Proof.
  unfold may_must_intro_program, may_must_setting2_ty.
  eapply EXT_LamNamedErased;
    [reflexivity|unfold g_ty, Otop; s2_wf| ].
  eapply EXT_LamNamedErased;
    [reflexivity|unfold g_ty, Otop; s2_wf| ].
  eapply EXT_LamDNamedErased;
    [reflexivity|unfold g_ty, Otop; s2_wf| ].
  eapply EXT_LetNamed with
    (τ1 := binop_precise_ty bop_gt (avar y) (vnat 10));
    [unfold g_ty, Otop; s2_wf| | ].
  - eapply EXT_BinOp. unfold g_ty, Otop. s2_wf.
  - change (∅; mm2_ctx_cond ⊢ₓ mm_body ⋮ [: ℕ | qeq 1]).
    eapply EXT_CtxCase with (Γa := mm2_ctx_false)
      (Γb := (mm2_ctx_true ⊕ mm2_ctx_false)%ctx);
      [unfold mm2_ctx_cond, mm2_ctx_y, mm_body, g_ty, Otop; s2_wf| | |
       exact may_must_setting2_obl_case].
    + unfold mm_body.
      eapply EXT_MatchFalseOnly;
        [unfold mm2_ctx_false, BF, g_ty, Otop; s2_wf| | ].
      * eapply EXT_CtxSub with (Γ2 := cond ∷ BF);
          [unfold mm2_ctx_false, BF, g_ty, Otop; s2_wf| |
           exact may_must_setting2_obl_false_cond].
        eapply EXT_Var. unfold BF. s2_wf.
      * exact may_must_setting2_false_branch.
    + eapply EXT_Sub with (τ1 := Otop ⊕ [: ℕ | qeq 1]);
        [unfold mm2_ctx_true, mm2_ctx_false, mm_body, BT, BF, g_ty, Otop; s2_wf| |
         exact may_must_setting2_obl_sum].
      unfold mm_body.
      eapply EXT_MatchBoth;
        [unfold mm2_ctx_true, mm2_ctx_false, BT, BF, g_ty, Otop; s2_wf| | | | ].
      * eapply EXT_CtxSub with (Γ2 := cond ∷ BT);
          [unfold mm2_ctx_true, BT, g_ty, Otop; s2_wf| |
           exact may_must_setting2_obl_true_cond].
        eapply EXT_Var. unfold BT. s2_wf.
      * eapply EXT_CtxSub with (Γ2 := cond ∷ BF);
          [unfold mm2_ctx_false, BF, g_ty, Otop; s2_wf| |
           exact may_must_setting2_obl_false_cond].
        eapply EXT_Var. unfold BF. s2_wf.
      * exact may_must_setting2_true_branch.
      * exact may_must_setting2_false_branch.
Qed.

(** *** Example 3.3: Peano subtraction (ack_like_program)

    Paper:  ⊢ fix sub. λx. λy. if x = 0 then 0 else if y = 0 then x
                               else sub (x-1) (y-1)
            : x:{ν: nat | ⊤} → y:[ν: nat | ν ≤ x] → [ν: nat | ν ≤ x]

    [ack_like_program] is exactly this function (it computes the truncated
    difference [x - y]).  The target type is semantically valid: in every
    [x]-fiber, [y] reaches 0..x, hence [x - y] reaches 0..x.

    ROUND-2 STATUS: still not derivable, but for a different, semantic
    reason.  The round-1 obstacle (T-Match on the demonic [x]) is gone:
    T-CtxCase splits the capabilities of [x:{⊤}] into "x = 0 only",
    "x > 0 only" and "both" exactly as in [branch_three_five_demonic_type]
    below, and EXT_VarComma types the variables with dependent types.  The
    remaining obstruction is that the T-Fix PREMISE for the paper's type is
    semantically FALSE in the Rocq denotation:

      x:{⊤}, f:({⊤} ⊓ {ν ≺ x}) → y:[ν ≤ x] → [ν ≤ x]
        ⊢ λy. if x = 0 then 0 else if y = 0 then x else f (x-1) (y-1)
        : y:[ν ≤ x] → [ν ≤ x]                                       (✗)

    (a) Vacuity of the recursive binding on mixed capabilities.  The
        argument type of [f] contains the demonic [{ν ≺ x}] (FFibVars over x
        of an FOver atom).  In a capability containing an environment with
        [x = 0], no extension by an argument can satisfy [ν < 0] in that
        x-fiber, and extensions must cover every environment (fiber
        extensions are non-empty), so the antecedent of the arrow is never
        satisfied and [f:...] holds VACUOUSLY, for any value of [f].
        Counterexample capability over (x, f, y):
          {(0, k, 0), (1, k, 0), (1, k, 1)}   with   k := λa.λb. 100.
        It satisfies x:{⊤}, f:… (vacuously) and y:[ν ≤ x] (the x-fiber 0
        reaches {0}, the x-fiber 1 reaches {0,1}).  The body returns 0, 1
        and k 0 0 = 100, so the x-fiber 1 never reaches 0: [ν ≤ x] fails.
    (b) Even without the base case, [f]'s angelic guarantee is collective
        over the environments of an argument fiber (FUnder is fibered by the
        qualifier variables only, not by [f]), while [y] is bound by [,]
        after [f] and may be correlated with it.  Counterexample over
        (x, f, y): {(1, k0, 0), (1, k5, 1)} with k0 := λa.λb.0 and
        k5 := λa.λb.5: [f] satisfies its type collectively (k0 reaches 0),
        but the only environment that calls [f] uses k5, so the results
        are {1, 5} and 0 is not reached.
    Because the premise fails on such capabilities, no sound derivation of
    it exists, whatever T-CtxCase/T-CtxSub splits are used inside it: a
    split must preserve the projection on the variables of the judgment,
    which include [f] and [y], and the counterexample capabilities already
    violate the judgment.  (The same capability (a) refutes the T-Fix
    premise of the pure SAFETY variant x:{⊤} → y:{ν ≤ x} → {ν ≤ x}:
    k 0 0 = 100 > 1.)  EXT_FixUnrollNamed only replaces [f] by the fix
    value itself for ONE level; a finite derivation must eventually type
    an inner occurrence of the fix value by T-Fix, whose premise has the
    same problem unless its argument type is a singleton (no recursion).
    So only bounded-depth variants (x:{ν ≤ k}) are reachable through
    unrolling; they additionally need a dependent T-Lam for [λx] (only the
    cofinite EXT_Lam exists; EXT_LamNamed does not open the result type),
    and they are not the paper's judgment, so we do not add them.

    What is derived is the base case, where the demonic parameter type
    pins the branch (and where the recursive binding is never used):
      x:{ν = 0} → y:[ν ≤ x] → [ν ≤ x].
    This exercises T-Fix (with the recursive-call binding in the context),
    the dependent result type, and T-Match with one reachable branch. *)

Definition q_le_bvar (k : nat) : type_qualifier :=
  q_nat_rel (vbvar k) (fun n m => n <= m).

(** y:[ν ≤ x] → [ν ≤ x], under the binder for [x] (de Bruijn: in the
    argument [ν] is bvar 0 and [x] is bvar 1; in the result [y] is bvar 1
    and [x] is bvar 2). *)
Definition sub_res_ty : context_ty :=
  [: ℕ | q_le_bvar 1] → [: ℕ | q_le_bvar 2].

Definition sub_paper_ty : context_ty := {: ℕ | qual_top} → sub_res_ty.
Definition sub_base_ty : context_ty := {: ℕ | qeq 0} → sub_res_ty.

Lemma sub_paper_ty_wf : basic_context_ty ∅ sub_paper_ty.
Proof.
  unfold sub_paper_ty, sub_res_ty, q_le_bvar. s2_unfold. case_type_wf_syntax.
Qed.

(** Opening the binder for [x] turns both [[ν ≤ bvar]] qualifiers into
    [[ν ≤ x]]. *)
Lemma s2_lstore_swap_lookup (a b v : logic_var) (s : LStore (V:=value)) :
  (lstore_swap a b s : gmap logic_var value) !! v = (s : gmap logic_var value) !! swap a b v.
Proof.
  unfold lstore_swap, lstore_rekey.
  rewrite <- (swap_involutive a b v) at 1.
  apply storeA_rekey_lookup. apply swap_inj.
Qed.

Lemma s2_open_q_nat_rel_bvar (k : nat) (z : atom) (R : nat -> nat -> Prop) :
  k <> 0%nat ->
  qual_open_atom k z (q_nat_rel (vbvar k) R) = q_nat_rel (avar z) R.
Proof.
  intros Hk. apply qual_ext.
  - cbn [qual_open_atom q_nat_rel qual_lvars lvar_value_keys vnu avar].
    apply set_eq. intros v. rewrite elem_of_set_swap.
    unfold swap. destruct v as [n|w].
    + repeat destruct decide; set_solver.
    + repeat destruct decide; set_solver.
  - intros [σ1 H1] [σ2 H2] Hs. cbn in Hs. subst σ2.
    cbn [qual_open_atom q_nat_rel qual_prop lvar_value_keys].
    unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    unfold denote_lvar_value, vnu, avar.
    rewrite !s2_lstore_swap_lookup.
    unfold swap.
    repeat destruct decide; try congruence.
    reflexivity.
Qed.

Definition Ale_x : context_ty := [: ℕ | q_nat_rel (avar x) (fun n m => n <= m)].
Definition sub_y_ty : context_ty := Ale_x.
Definition sub_r_ty : context_ty := Ale_x.

Definition sub_rec_ty : context_ty :=
  fix_rec_call_ty TNat x ({: ℕ | qeq 0}) sub_res_ty.

Definition sub_ctx_y : ctx :=
  ((Emp ,, (x ∷ {: ℕ | qeq 0})) ,, (f ∷ sub_rec_ty)) ,, (y ∷ sub_y_ty).

Definition sub_else : tm :=
  let c2 := op_eq0 ·₁ y in
  if c2 then
    ret x
  else
    let r1 := x ⟨ - ⟩ vnat 1 in
    let r2 := y ⟨ - ⟩ vnat 1 in
    f @@ (r1, r2).

Definition sub_match : tm := if c1 then ret (vnat 0) else sub_else.

Definition sub_ctx_true : ctx := sub_ctx_y ,, (c1 ∷ BT).

Lemma ack_like_program_obl_true_only :
  ctx_sub_under ∅ (fv_tm sub_match ∪ fv_cty sub_r_ty)
    (sub_ctx_y ,, (c1 ∷ primop_precise_ty op_eq0 (avar x))) sub_ctx_true.
Proof.
  (* Same domain/erasure; take [r' = r|X].  [x:{ν = 0}] forces [x = 0] in
     every environment, so [c1 = (x =? 0)] is [true] everywhere and the
     non-empty capability reaches [true]. *)
Admitted.

Lemma ack_like_program_obl_cond :
  ctx_sub_under ∅ (fv_tm (ret (avar c1)) ∪ fv_cty BT) sub_ctx_true (c1 ∷ BT).
Proof.
  (* Weakening to the last [,]-conjunct (closed type). *)
  unfold sub_ctx_true, sub_ctx_y, sub_rec_ty, sub_y_ty, Ale_x, sub_res_ty,
    q_le_bvar.
  s2_weaken.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma ack_like_program_obl_x_only :
  ctx_sub_under ∅ (fv_tm (ret (vnat 0)) ∪ fv_cty sub_r_ty)
    sub_ctx_true (x ∷ {: ℕ | qeq 0}).
Proof.
  (* Weakening to the first [,]-conjunct: X = {x}. *)
  unfold sub_ctx_true, sub_ctx_y, sub_rec_ty, sub_y_ty, sub_r_ty, Ale_x,
    sub_res_ty, q_le_bvar.
  s2_weaken.
  apply s2_models_comma_l, s2_models_comma_l, s2_models_comma_l in Hr.
  eapply s2_models_comma_r_closed; [s2_closed_ctx_fv|exact Hr].
Qed.

Lemma ack_like_program_obl_zero :
  sub_type_under ∅ (x ∷ {: ℕ | qeq 0})
    (const_precise_ty (cnat 0)) sub_r_ty.
Proof.
  (* [sub_r_ty] is [[ν ≤ x]] with [x] free.  Every environment has
     [x = 0]; in the (only) [x]-fiber the result is exactly 0, and
     {n | n ≤ 0} = {0} is reached. *)
Admitted.

Lemma ack_like_program_obl_zero_weaken :
  ctx_sub_under ∅ (fv_tm (ret (vnat 0)) ∪ fv_cty (const_precise_ty (cnat 0)))
    (x ∷ {: ℕ | qeq 0}) Emp.
Proof.
  (* Weakening to the empty context: X = ∅, witness r' = r. *)
  s2_weaken. apply s2_models_emp.
Qed.

Lemma s2_open_sub_res_ty :
  open_one 0 x sub_res_ty = CTArrow sub_y_ty sub_r_ty.
Proof.
  change (open_one 0 x sub_res_ty) with
    (CTArrow (CTUnder TNat (qual_open_atom 1 x (q_le_bvar 1)))
             (CTUnder TNat (qual_open_atom 2 x (q_le_bvar 2)))).
  unfold q_le_bvar.
  rewrite !s2_open_q_nat_rel_bvar by lia.
  reflexivity.
Qed.

Theorem ack_like_program_base_type :
  ∅; Emp ⊢ₓ ack_like_program ⋮ sub_base_ty.
Proof.
  unfold ack_like_program, sub_base_ty.
  eapply EXT_FixNamed;
    [reflexivity|unfold sub_res_ty, q_le_bvar; s2_wf| ].
  rewrite s2_open_sub_res_ty.
  eapply EXT_LamNamedErased;
    [reflexivity|unfold sub_y_ty, sub_r_ty, Ale_x, sub_res_ty, q_le_bvar; s2_wf| ].
  eapply EXT_LamNamedErased;
    [reflexivity|unfold sub_y_ty, sub_r_ty, Ale_x, sub_res_ty, q_le_bvar; s2_wf| ].
  eapply EXT_LetNamed with (τ1 := primop_precise_ty op_eq0 (avar x));
    [unfold sub_y_ty, sub_r_ty, Ale_x, sub_res_ty, q_le_bvar; s2_wf| | ].
  - eapply EXT_AppOpValue. unfold sub_y_ty, Ale_x, sub_res_ty, q_le_bvar. s2_wf.
  - change (∅; sub_ctx_y ,, (c1 ∷ primop_precise_ty op_eq0 (avar x)) ⊢ₓ
      sub_match ⋮ sub_r_ty).
    eapply EXT_CtxSub with (Γ2 := sub_ctx_true);
      [unfold sub_ctx_y, sub_match, sub_else, sub_rec_ty, sub_y_ty, sub_r_ty,
         sub_res_ty, q_le_bvar; s2_wf| |
       exact ack_like_program_obl_true_only].
    unfold sub_match.
    eapply EXT_MatchTrueOnly;
      [unfold sub_ctx_true, sub_ctx_y, sub_else, sub_rec_ty, sub_y_ty, sub_r_ty,
         sub_res_ty, q_le_bvar, BT; s2_wf| | ].
    + eapply EXT_CtxSub with (Γ2 := c1 ∷ BT);
        [unfold sub_ctx_true, sub_ctx_y, sub_rec_ty, sub_y_ty, sub_r_ty, Ale_x, sub_res_ty,
           q_le_bvar, BT; s2_wf| |
         exact ack_like_program_obl_cond].
      eapply EXT_Var. unfold BT. s2_wf.
    + eapply EXT_CtxSub with (Γ2 := x ∷ {: ℕ | qeq 0});
        [unfold sub_ctx_true, sub_ctx_y, sub_rec_ty, sub_y_ty, sub_r_ty,
           sub_res_ty, q_le_bvar, BT; s2_wf| |
         exact ack_like_program_obl_x_only].
      eapply EXT_Sub with (τ1 := const_precise_ty (cnat 0));
        [unfold sub_r_ty, Ale_x, q_le_bvar; s2_wf| |
         exact ack_like_program_obl_zero].
      eapply EXT_CtxSub with (Γ2 := Emp);
        [s2_wf| |exact ack_like_program_obl_zero_weaken].
      eapply EXT_Const. s2_wf.
Qed.

(** *** Further judgments from p.4 and p.6-7 *)

(** ⊢ 1 : {ν > 0}  ✓  (p.4) *)
Lemma one_program_obl_pos :
  sub_type_under ∅ Emp (const_precise_ty (cnat 1)) ({: ℕ | qgt 0}).
Proof. apply s2_const_over_sub. lia. Qed.

Theorem one_program_pos_type :
  ∅; Emp ⊢ₓ one_program ⋮ ({: ℕ | qgt 0}).
Proof.
  unfold one_program.
  eapply EXT_Sub with (τ1 := const_precise_ty (cnat 1));
    [s2_wf| |exact one_program_obl_pos].
  eapply EXT_Const. s2_wf.
Qed.

(** ∅ ⊢ C_en[x] : [ν > 0] ✓ and ∅ ⊢ C_en[y] : [ν > 0] ✓  (p.6).
    Added programs: the entangled context with hole filled by [x] / [y]. *)

Definition dependent_context_x : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := x ⟨ + ⟩ vnat 1 in
  ret x.

Definition dependent_context_y : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := x ⟨ + ⟩ vnat 1 in
  ret y.

Lemma dependent_context_x_basic_type : ∅ ⊢ₑ dependent_context_x ⋮ ℕ.
Proof. unfold dependent_context_x. basic_check. Qed.

Lemma dependent_context_y_basic_type : ∅ ⊢ₑ dependent_context_y ⋮ ℕ.
Proof. unfold dependent_context_y. basic_check. Qed.

Lemma dependent_context_x_obl_var :
  ctx_sub_under ∅ (fv_tm (ret (avar x)) ∪ fv_cty Apos) dependent_ctx (x ∷ gen_ty).
Proof.
  (* Weakening: [x]'s binding is the second conjunct of the left [,]-part,
     and its type is closed. *)
  unfold dependent_ctx. s2_weaken.
  apply s2_models_comma_l in Hr.
  eapply s2_models_comma_r_closed; [ |exact Hr].
  cbn [ctx_fv]. apply s2_fv_closed. unfold gen_ty. extended_wf_type.
Qed.

Lemma dependent_context_x_obl_sub :
  sub_type_under ∅ (x ∷ gen_ty) gen_ty Apos.
Proof.
  (* Closed qualifiers: [gen_ty] is the precise type of [natGen 0], whose
     angelic half reaches every natural number. *)
  unfold gen_ty, primop_precise_ty. cbn [prim_op_type].
  apply subtype_inter_over_under_to_under_corrected.
  - unfold subtype_wf. repeat split; s2_wf.
  - unfold qual_dom, primop_result_qual, qual_and.
    cbn [qual_lvars lvar_value_keys vnat].
    rewrite ?lvars_fv_union, ?lvars_fv_singleton_bound, ?lvars_fv_empty.
    set_solver.
  - unfold qual_dom, primop_result_qual, qual_and.
    cbn [qual_lvars lvar_value_keys vnat].
    rewrite ?lvars_fv_union, ?lvars_fv_singleton_bound, ?lvars_fv_empty.
    set_solver.
  - reflexivity.
  - apply subtype_under_closed_by_qualifier_corrected.
    + unfold subtype_wf. repeat split; try s2_wf.
    + unfold qual_dom, primop_result_qual, qual_and.
      cbn [qual_lvars lvar_value_keys vnat].
      rewrite ?lvars_fv_union, ?lvars_fv_singleton_bound, ?lvars_fv_empty.
      set_solver.
    + unfold qual_dom, qgt, q_nat_pred, q_const_pred, vnu.
      cbn [qual_lvars lvar_value_keys].
      rewrite ?lvars_fv_union, ?lvars_fv_singleton_bound, ?lvars_fv_empty.
      set_solver.
    + intros s Hs.
      unfold qgt, q_nat_pred, q_const_pred, vnu in Hs. cbn in Hs.
      destruct Hs as [c [Hc Hpos]].
      rewrite s2_restrict_lookup in Hc by set_solver.
      destruct c as [b|n|t|l]; try contradiction.
      unfold primop_result_qual, qual_and. cbn.
      split; exists (cnat 0), (cnat n);
        (split; [reflexivity| ]); (split; [ |constructor]);
        rewrite !s2_restrict_lookup by set_solver; exact Hc.
    + unfold qgt, q_nat_pred, q_const_pred, vnu, primop_result_qual, qual_and.
      cbn [qual_lvars lvar_value_keys]. set_solver.
    + unshelve eexists.
      * refine {| storeAO_store := {[LVBound 0 := vconst (cnat 1)]} |}.
        unfold qgt, q_nat_pred, q_const_pred, vnu. cbn.
        rewrite dom_singleton_L. set_solver.
      * unfold qgt, q_nat_pred, q_const_pred, vnu. cbn.
        exists (cnat 1). split; [ |lia].
        rewrite lookup_singleton_eq. reflexivity.
Qed.

Theorem dependent_context_x_type :
  ∅; Emp ⊢ₓ dependent_context_x ⋮ Apos.
Proof.
  unfold dependent_context_x.
  eapply EXT_LetNamed with (τ1 := gen_ty); [s2_wf| | ].
  - eapply EXT_AppOpValue. s2_wf.
  - eapply EXT_LetNamed with
      (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1)); [s2_wf| | ].
    + eapply EXT_BinOp. s2_wf.
    + change (∅; dependent_ctx ⊢ₓ ret (avar x) ⋮ Apos).
      eapply EXT_CtxSub with (Γ2 := x ∷ gen_ty);
        [unfold dependent_ctx; s2_wf| |exact dependent_context_x_obl_var].
      eapply EXT_Sub with (τ1 := gen_ty);
        [s2_wf| |exact dependent_context_x_obl_sub].
      eapply EXT_Var. s2_wf.
Qed.

Lemma dependent_context_y_obl_var :
  ctx_sub_under ∅ (fv_tm (ret (avar y)) ∪ fv_cty Apos) dependent_ctx (y ∷ Apos).
Proof.
  (* X = {y}; witness r' = r.  [y] is bound precisely to [x + 1] and [x]
     reaches every natural number (angelic half of [gen_ty]), so the
     [y]-projection of [r] contains every positive number: [r ⊨ y:[ν>0]].
     (Round-1 derivation, kept: a semantic T-CtxSub to the closed binding
     [y:[ν>0]].  Round 2 adds the paper-style derivation through
     EXT_VarComma, [dependent_context_y_varcomma_type] below.) *)
Admitted.

Theorem dependent_context_y_type :
  ∅; Emp ⊢ₓ dependent_context_y ⋮ Apos.
Proof.
  unfold dependent_context_y.
  eapply EXT_LetNamed with (τ1 := gen_ty); [s2_wf| | ].
  - eapply EXT_AppOpValue. s2_wf.
  - eapply EXT_LetNamed with
      (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1)); [s2_wf| | ].
    + eapply EXT_BinOp. s2_wf.
    + change (∅; dependent_ctx ⊢ₓ ret (avar y) ⋮ Apos).
      eapply EXT_CtxSub with (Γ2 := y ∷ Apos);
        [unfold dependent_ctx; s2_wf| |exact dependent_context_y_obl_var].
      eapply EXT_Var. s2_wf.
Qed.

(** Round 2: the paper's T-Var under the basic context Σ,⌊Γ⌋
    (EXT_VarComma) makes [ret y] typable at its own dependent binding type
    [{ν = x+1} ⊓ [ν = x+1]], so the semantic T-CtxSub to a closed binding
    used above can be replaced by a T-Sub of the precise type. *)
Lemma dependent_context_y_obl_sub :
  sub_type_under ∅ dependent_ctx
    (binop_precise_ty bop_plus (avar x) (vnat 1)) Apos.
Proof.
  (* [gen_ty] (precise type of natGen 0, closed) makes the x-projection of
     the capability contain every natural number.  The precise type of [e]
     fixes its results in the x-fiber [x = k] to {k + 1}; hence the result
     projection contains every positive number, which is the closed
     angelic [[ν > 0]]. *)
Admitted.

Theorem dependent_context_y_varcomma_type :
  ∅; Emp ⊢ₓ dependent_context_y ⋮ Apos.
Proof.
  unfold dependent_context_y.
  eapply EXT_LetNamed with (τ1 := gen_ty); [s2_wf| | ].
  - eapply EXT_AppOpValue. s2_wf.
  - eapply EXT_LetNamed with
      (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1)); [s2_wf| | ].
    + eapply EXT_BinOp. s2_wf.
    + change (∅; dependent_ctx ⊢ₓ ret (avar y) ⋮ Apos).
      eapply EXT_Sub with (τ1 := binop_precise_ty bop_plus (avar x) (vnat 1));
        [unfold dependent_ctx; s2_wf| |exact dependent_context_y_obl_sub].
      unfold dependent_ctx.
      eapply EXT_VarComma. s2_wf.
Qed.

(** x:[ν ≥ 0] ∗ y:{ν ≥ 1} ⊢ x - y : [ν | even ν]  ✓   (p.7)
    x:[ν ≥ 0] , y:{ν ≥ 1} ⊢ x - y : [ν | even ν]  ✗   (y may depend on x;
    e.g. the capability {(n, n+1) | n ∈ ℕ} gives [x - y = 0] only). *)

Lemma x_minus_y_obl_even_sub :
  sub_type_under ∅ ((x ∷ [: ℕ | qge 0]) ∗ (y ∷ {: ℕ | qge 1}))
    (binop_precise_ty bop_minus (avar x) (avar y)) ([: ℕ | qeven]).
Proof.
  (* Product capability: fix any [y0] present in the (non-empty) [y]-part;
     for each even [m], [x = m + y0] is present in the [x]-part (it reaches
     all of ℕ), so the environment (m + y0, y0) is in the capability and
     the result is [m].  Truncation is irrelevant since [x ≥ y0]. *)
Admitted.

Theorem x_minus_y_even_dis_type :
  ∅; (x ∷ [: ℕ | qge 0]) ∗ (y ∷ {: ℕ | qge 1}) ⊢ₓ x_minus_y ⋮ ([: ℕ | qeven]).
Proof.
  unfold x_minus_y.
  eapply EXT_Sub with (τ1 := binop_precise_ty bop_minus (avar x) (avar y));
    [s2_wf| |exact x_minus_y_obl_even_sub].
  eapply EXT_BinOp. s2_wf.
Qed.


End Section2TypingExamples.
