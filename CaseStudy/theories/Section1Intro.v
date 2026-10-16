(** * Small programs from Section 1 (Introduction) *)

From ProofAutomation Require Import BasicTypeInfer ExtendedSubsumption ExtendedTypeInfer.
From ContextAlgebra Require Import ResourceInterface.
From ContextLogic Require Import FormulaSemantics FormulaConnectives.
From ContextBasicDenotation Require Import BasicTypingFormula.
From Denotation Require Context TypeDenote.
From ContextBasicDenotation Require Import StoreTyping.
From ContextTyping Require Import Typing.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

(** ** Local proof-automation helpers

    These helpers are generic (they mention no Section 1 program) and are
    candidates for [ProofAutomation]; they are kept local because this file
    must not modify shared infrastructure.

    - [intro_qual_open_q_nat2] / [intro_qual_open_q_nat_pred]: opening a
      value-based qualifier replaces the opened de Bruijn value by the atom.
      Needed whenever a dependent arrow result (e.g. [ν ≤ x]) is opened by
      [EXT_Lam].
    - [intro_ctx_sub_under_mono], [intro_ext_ctx_sub]: [T-CtxSub] stated
      with the variable set [dom ⌊Γ2⌋] (any obligation proved for a superset of
      [fv e ∪ fv τ] suffices).
    - tactics [intro_wf] / [intro_basic]: well-formedness and basic typing for
      opened (locally nameless) terms whose free atoms are abstract cofinite
      atoms; the shared [extended_wf] only handles concrete atoms. *)

Definition intro_atomic_value (v : value) : Prop :=
  match v with vbvar _ | vfvar _ | vconst _ => True | _ => False end.

Lemma intro_atomic_open_keys k a v :
  intro_atomic_value v -> a ∉ fv_value v ->
  set_swap (LVBound k) (LVFree a) (lvar_value_keys v) =
  lvar_value_keys (open_value k (vfvar a) v).
Proof.
  destruct v as [c0|b|n|T e|T vf]; cbn; intros Hat Ha; try contradiction.
  - unfold set_swap. rewrite set_map_empty. reflexivity.
  - unfold set_swap. rewrite set_map_singleton_L. f_equal.
    unfold swap. repeat destruct decide; try congruence.
    inversion e; subst. set_solver.
  - unfold set_swap. rewrite set_map_singleton_L.
    destruct (decide (k = n)) as [->|Hne]; cbn.
    + unfold swap. rewrite decide_True by reflexivity. reflexivity.
    + unfold swap. repeat destruct decide; try congruence.
Qed.

Lemma intro_atomic_open_denote k a (s : LStore (V := value)) v :
  intro_atomic_value v -> a ∉ fv_value v ->
  denote_lvar_value (lstore_swap (LVBound k) (LVFree a) s) v =
  denote_lvar_value s (open_value k (vfvar a) v).
Proof.
  intros Hat Ha.
  assert (Hlk : forall z,
    (lstore_swap (LVBound k) (LVFree a) s : gmap logic_var value) !! z =
    (s : gmap logic_var value) !! swap (LVBound k) (LVFree a) z).
  { intros z. unfold lstore_swap, lstore_rekey.
    rewrite <- (swap_involutive (LVBound k) (LVFree a) z) at 1.
    pose proof (swap_inj (LVBound k) (LVFree a)) as Hinj.
    change (kmap (M2:=gmap logic_var) (swap (LVBound k) (LVFree a))
              (s : gmap logic_var value)
      !! swap (LVBound k) (LVFree a) (swap (LVBound k) (LVFree a) z) =
      (s : gmap logic_var value) !! swap (LVBound k) (LVFree a) z).
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=Hinj) (swap (LVBound k) (LVFree a)) s). reflexivity. }
  destruct v as [c0|b|n|T e|T vf]; cbn in *; try contradiction.
  - reflexivity.
  - rewrite Hlk. unfold swap. repeat destruct decide; try congruence.
    inversion e; subst. set_solver.
  - destruct (decide (k = n)) as [->|Hne]; cbn.
    + rewrite Hlk. unfold swap. rewrite decide_True by reflexivity. reflexivity.
    + rewrite Hlk. unfold swap. repeat destruct decide; try congruence.
Qed.

(** Binary nat relation qualifier [R v1 v2]. *)
Definition q_nat2 (v1 v2 : value) (R : nat -> nat -> Prop) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ => exists n m,
       denote_lvar_value (lso_store σ) v1 = Some (vconst (cnat n)) /\
       denote_lvar_value (lso_store σ) v2 = Some (vconst (cnat m)) /\ R n m).

Lemma intro_qual_open_q_nat2 k a v1 v2 R :
  intro_atomic_value v1 -> intro_atomic_value v2 ->
  a ∉ fv_value v1 -> a ∉ fv_value v2 ->
  qual_open_atom k a (q_nat2 v1 v2 R) =
  q_nat2 (open_value k (vfvar a) v1) (open_value k (vfvar a) v2) R.
Proof.
  intros H1 H2 Ha1 Ha2.
  unfold q_nat2. apply qual_ext; cbn [qual_open_atom qual_lvars qual_prop].
  - unfold set_swap. rewrite set_map_union_L.
    rewrite <- !intro_atomic_open_keys by assumption. reflexivity.
  - intros s1 s2 Hs. cbn.
    rewrite !intro_atomic_open_denote by assumption. rewrite Hs. reflexivity.
Qed.

Lemma intro_qual_open_q_nat_pred k a v P :
  intro_atomic_value v -> a ∉ fv_value v ->
  qual_open_atom k a (q_nat_pred v P) = q_nat_pred (open_value k (vfvar a) v) P.
Proof.
  intros H1 Ha1.
  unfold q_nat_pred, q_const_pred.
  apply qual_ext; cbn [qual_open_atom qual_lvars qual_prop].
  - rewrite <- !intro_atomic_open_keys by assumption. reflexivity.
  - intros s1 s2 Hs. cbn.
    rewrite !intro_atomic_open_denote by assumption. rewrite Hs. reflexivity.
Qed.

Lemma intro_cty_open_over k a b q :
  cty_open k a (over_ty b q) = over_ty b (qual_open_atom (S k) a q).
Proof. reflexivity. Qed.

Lemma intro_cty_open_under k a b q :
  cty_open k a (under_ty b q) = under_ty b (qual_open_atom (S k) a q).
Proof. reflexivity. Qed.

Lemma intro_dom_erase_ctx_comma Γ1 Γ2 :
  dom (erase_ctx (CtxComma Γ1 Γ2)) = dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2).
Proof. cbn [erase_ctx]. apply dom_union_L. Qed.

Lemma intro_dom_erase_ctx_star Γ1 Γ2 :
  dom (erase_ctx (CtxStar Γ1 Γ2)) = dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2).
Proof. cbn [erase_ctx]. apply dom_union_L. Qed.

Lemma intro_dom_erase_ctx_sum Γ1 Γ2 :
  dom (erase_ctx (CtxSum Γ1 Γ2)) = dom (erase_ctx Γ1).
Proof. reflexivity. Qed.

Lemma intro_dom_erase_ctx_empty : dom (erase_ctx CtxEmpty) = (∅ : aset).
Proof. cbn [erase_ctx]. apply dom_empty_L. Qed.

(** [T-CtxSub] only needs the refinement on [fv e ∪ fv τ]; a refinement on a
    larger variable set is stronger. *)
Lemma intro_ctx_sub_under_mono Σ (X Y : aset) Γ1 Γ2 :
  Y ⊆ X ->
  ctx_sub_under Σ X Γ1 Γ2 ->
  ctx_sub_under Σ Y Γ1 Γ2.
Proof.
  intros HYX [H1 [H2 [Hagree Hsem]]].
  split; [exact H1| ]. split; [exact H2| ]. split.
  - intros a Ha. apply Hagree. set_solver.
  - intros r Hr. destruct (Hsem r Hr) as [r' [Hle Hr']].
    exists r'. split; [ |exact Hr'].
    etransitivity; [apply res_restrict_mono; exact HYX|exact Hle].
Qed.

Lemma intro_ext_ctx_sub Σ Γ1 Γ2 (X : aset) e τ :
  Σ; Γ1 ⊢wf e ⋮ τ ->
  Σ; Γ2 ⊢ₓ e ⋮ τ ->
  dom (erase_ctx Γ2) ⊆ X ->
  ctx_sub_under Σ X Γ1 Γ2 ->
  Σ; Γ1 ⊢ₓ e ⋮ τ.
Proof.
  intros Hwf Hty HX Hsub.
  eapply EXT_CtxSub; [exact Hwf|exact Hty| ].
  eapply intro_ctx_sub_under_mono; [ |exact Hsub].
  pose proof (extended_typing_wf_under Σ Γ2 e τ Hty) as Hwf2.
  pose proof (context_typing_wf_fv_tm_subset Σ Γ2 e τ Hwf2).
  pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γ2 e τ Hwf2).
  set_solver.
Qed.

(** [T-CtxCase] with a larger variable set (same pattern as
    [intro_ext_ctx_sub]). *)
Lemma intro_ctx_case_under_mono Σ (X Y : aset) Γ Γa Γb :
  Y ⊆ X ->
  ctx_case_under Σ X Γ Γa Γb ->
  ctx_case_under Σ Y Γ Γa Γb.
Proof.
  intros HYX [H1 [H2 [H3 [Haga [Hagb Hsem]]]]].
  split; [exact H1| ]. split; [exact H2| ]. split; [exact H3| ].
  split; [intros a Ha; apply Haga; set_solver| ].
  split; [intros a Ha; apply Hagb; set_solver| ].
  intros r Hr. destruct (Hsem r Hr) as [r' [Hle Hr']].
  exists r'. split; [ |exact Hr'].
  etransitivity; [apply res_restrict_mono; exact HYX|exact Hle].
Qed.

Lemma intro_ext_ctx_case Σ Γ Γa Γb (X : aset) e τ :
  Σ; Γ ⊢wf e ⋮ τ ->
  Σ; Γa ⊢ₓ e ⋮ τ ->
  Σ; Γb ⊢ₓ e ⋮ τ ->
  dom (erase_ctx Γa) ⊆ X ->
  ctx_case_under Σ X Γ Γa Γb ->
  Σ; Γ ⊢ₓ e ⋮ τ.
Proof.
  intros Hwf Ha Hb HX Hcase.
  eapply EXT_CtxCase; [exact Hwf|exact Ha|exact Hb| ].
  eapply intro_ctx_case_under_mono; [ |exact Hcase].
  pose proof (extended_typing_wf_under Σ Γa e τ Ha) as Hwfa.
  pose proof (context_typing_wf_fv_tm_subset Σ Γa e τ Hwfa).
  pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γa e τ Hwfa).
  set_solver.
Qed.

Ltac intro_compute_close :=
  repeat match goal with |- context[close_tm ?a ?k ?e] =>
    let r := eval vm_compute in (close_tm a k e) in
    change (close_tm a k e) with r end.

Ltac intro_norm_dec :=
  repeat (first [rewrite decide_True by reflexivity | rewrite decide_False by lia]).

Ltac intro_norm_open :=
  cbn [open_one open_tm_atom_inst open_cty_atom_inst open_tm open_value
       cty_open Ret];
  repeat rewrite intro_cty_open_over; repeat rewrite intro_cty_open_under;
  repeat rewrite intro_qual_open_q_nat2
    by (unfold avar; cbn; first [exact I | set_solver]);
  repeat rewrite intro_qual_open_q_nat_pred
    by (unfold avar; cbn; first [exact I | set_solver]);
  unfold vnu;
  cbn [open_value];
  intro_norm_dec.

Ltac intro_set :=
  cbn [ctx_dom erase_ctx] in *;
  rewrite ?dom_empty_L, ?dom_union_L, ?dom_singleton_L;
  set_solver.

Ltac intro_norm_erase_dom :=
  repeat first [ rewrite intro_dom_erase_ctx_comma | rewrite intro_dom_erase_ctx_star
               | rewrite intro_dom_erase_ctx_sum | rewrite intro_dom_erase_ctx_empty
               | rewrite erase_ctx_bind_dom ].

Ltac intro_lvars_wf :=
  unfold lvars_wf_at;
  let Hlv := fresh "Hlv" in
  intros [?|?] Hlv; cbn [lvar_wf_at]; set_unfold in Hlv;
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
  repeat match goal with
         | H : LVBound _ = LVBound _ |- _ => inversion H; subst; clear H
         | H : LVFree _ = LVFree _ |- _ => inversion H; subst; clear H
         | H : LVBound _ = LVFree _ |- _ => discriminate H
         | H : LVFree _ = LVBound _ |- _ => discriminate H
         | H : False |- _ => destruct H
         end;
  first [ lia | set_solver ].

Ltac intro_wf_type :=
  intro_norm_erase_dom;
  cbn [ctx_dom];
  unfold q_nat2, q_nat_pred, q_const_pred, vnu, avar, vnat, vbool in *;
  unfold basic_context_ty, ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
    precise_const, const_precise_ty, precise_ty, over_ty, under_ty,
    q_true, q_false, bool_qual, bool_precise_ty, mk_q_eq, qual_top,
    binop_precise_ty, binop_result_qual, binop_top_ty in *;
  cbn [wf_context_ty_at erase_ty qual_vars qual_lvars lvar_value_keys
       bin_op_type base_ty_of_const] in *;
  repeat split; try reflexivity; intro_lvars_wf.

Ltac intro_wf_ctx :=
  unfold wf_ctx_under;
  repeat
    match goal with
    | |- basic_ctx _ CtxEmpty => apply basic_ctx_empty
    | |- basic_ctx _ (CtxBind _ _) =>
        apply basic_ctx_bind; [intro_set | intro_wf_type]
    | |- basic_ctx _ (CtxComma _ _) =>
        cbn [basic_ctx ctx_dom]; repeat split;
        try intro_wf_ctx; try intro_wf_type; try intro_set
    | |- basic_ctx _ (CtxStar _ _) =>
        apply basic_ctx_star; [intro_wf_ctx|intro_wf_ctx|intro_set]
    | |- basic_ctx _ (CtxSum _ _) =>
        apply basic_ctx_sum; [intro_wf_ctx|intro_wf_ctx|reflexivity|reflexivity]
    end.

Lemma intro_erase_ctx_sum Γ1 Γ2 : erase_ctx (CtxSum Γ1 Γ2) = erase_ctx Γ1.
Proof. reflexivity. Qed.

Lemma intro_erase_ctx_bind a τ :
  erase_ctx (CtxBind a τ) = <[a := erase_ty τ]> (∅ : gmap atom ty).
Proof. reflexivity. Qed.

Ltac intro_erase :=
  repeat first
    [ rewrite intro_erase_ctx_sum
    | rewrite erase_ctx_comma_bind_fresh by (intro_norm_erase_dom; intro_set)
    | rewrite erase_ctx_star_bind_fresh by (intro_norm_erase_dom; intro_set)
    | rewrite intro_erase_ctx_bind ];
  cbn [erase_ctx erase_ty over_ty under_ty] in *.

Ltac intro_clear_neq :=
  let Heq := fresh "Heq" in
  intros Heq;
  first [ solve [vm_compute in Heq; congruence] | subst ];
  repeat match goal with
         | H : ?a ∉ _ |- False => apply H; clear H; set_solver
         | H : ?a ∉ _ |- _ => rewrite ?dom_insert_L, ?dom_empty_L in H
         end.

Ltac intro_lookup :=
  first
    [ apply map_lookup_insert
    | match goal with
      | |- <[?y := ?Ty]> ?Γ !! ?x = Some ?T =>
          transitivity (Γ !! x);
          [ apply map_lookup_insert_ne; intro_clear_neq
          | intro_lookup ]
      end ].

Ltac intro_keys_of m :=
  lazymatch m with
  | <[?k := _]> ?m' => let s := intro_keys_of m' in constr:(({[k]} : aset) ∪ s)
  | _ => constr:(∅ : aset)
  end.

Ltac intro_basic :=
  unfold Ret, avar, vnat, vbool, if_named, case_app in *;
  lazymatch goal with
  | |- _ ⊢ₑ tret _ ⋮ _ => apply TT_Ret; intro_basic
  | |- _ ⊢ₑ tbinop _ _ _ ⋮ _ =>
      eapply TT_BinOp; [basic_solve_binop_type | intro_basic | intro_basic]
  | |- _ ⊢ₑ tprim _ _ ⋮ _ => eapply TT_Op; [reflexivity | intro_basic]
  | |- _ ⊢ₑ tapp _ _ ⋮ _ => eapply TT_App; [intro_basic | intro_basic]
  | |- _ ⊢ₑ tmatch _ _ _ ⋮ _ =>
      eapply TT_Match; [intro_basic | intro_basic | intro_basic]
  | |- ?Γ ⊢ₑ tlete _ _ ⋮ _ =>
      let L := intro_keys_of Γ in
      eapply (TT_Let _ _ _ _ _ L);
      [ intro_basic
      | let z := fresh "z" in let Hz := fresh "Hz" in
        intros z Hz;
        cbn [open_one open_tm_atom_inst open_value_atom_inst open_tm open_value]; intro_norm_dec; intro_basic ]
  | |- _ ⊢ᵥ vconst _ ⋮ _ => constructor
  | |- _ ⊢ᵥ vfvar _ ⋮ _ => apply VT_FVar; intro_lookup
  | |- ?Γ ⊢ᵥ vlam _ _ ⋮ _ =>
      let L := intro_keys_of Γ in
      eapply (VT_Lam _ _ _ _ L);
      let z := fresh "z" in let Hz := fresh "Hz" in
      intros z Hz;
      cbn [open_one open_tm_atom_inst open_value_atom_inst open_tm open_value]; intro_norm_dec; intro_basic
  end.

Ltac intro_basic_top :=
  unfold ONat, UNat, OBool, UBool, OTree, UTree, OList, UList, qual_top in *;
  intro_erase;
  unfold binop_precise_ty, binop_top_ty, primop_precise_ty, const_precise_ty,
    precise_ty, bool_precise_ty, over_ty, under_ty in *;
  cbn [erase_ty bin_op_type base_ty_of_const] in *;
  unfold lam_named, let_named in *; intro_compute_close;
  intro_basic.

Ltac intro_wf :=
  unfold context_typing_wf;
  repeat split;
  lazymatch goal with
  | |- wf_ctx_under _ _ => intro_wf_ctx
  | |- basic_ctx _ _ => intro_wf_ctx
  | |- wf_context_ty_at _ _ _ => intro_wf_type
  | |- basic_context_ty _ _ => intro_wf_type
  | |- _ ∉ _ => intro_set
  | |- _ ## _ => intro_set
  | |- _ ⊆ _ => intro_set
  | |- _ ∈ _ => intro_set
  | |- _ ⊢ₑ _ ⋮ _ =>
      first [ intro_basic_top
            | unfold ONat, UNat, qual_top in *; intro_erase;
              unfold over_ty, under_ty in *; cbn [erase_ty] in *; basic_check
            | extended_basic_check ]
  | |- _ = _ => reflexivity
  end.

(** [ctx_sub] target-domain side goal of [intro_ext_ctx_sub]. *)
Ltac intro_dom_sub := intro_norm_erase_dom; clear; set_solver.

(** ** Helpers for structural [T-CtxSub] obligations

    A context refinement whose target denotation is entailed by the source
    denotation holds with the identity capability ([r' = r]). *)
Local Notation ctx_denote_under := Denotation.Context.ctx_denote_under.
Local Notation ty_denote := Denotation.TypeDenote.ty_denote.

Lemma intro_ctx_sub_by_entails Σ (X : aset) Γ1 Γ2 :
  wf_ctx_under Σ Γ1 -> wf_ctx_under Σ Γ2 ->
  Denotation.Context.ty_env_agree_on X (erase_ctx Γ1) (erase_ctx Γ2) ->
  (forall r, res_models r (ctx_denote_under Σ Γ1) ->
             res_models r (ctx_denote_under Σ Γ2)) ->
  ctx_sub_under Σ X Γ1 Γ2.
Proof.
  intros H1 H2 Hag Hent. split; [exact H1| ]. split; [exact H2| ].
  split; [exact Hag| ].
  intros r Hr. exists r. split; [apply res_restrict_le| ]. apply Hent. exact Hr.
Qed.

Lemma intro_closed_fv τ : wf_context_ty_at 0 ∅ τ -> fv_cty τ = ∅.
Proof.
  intros Hwf. pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hwf). set_solver.
Qed.

Ltac intro_wf_goals :=
  repeat split;
  lazymatch goal with
  | |- wf_ctx_under _ _ => intro_wf_ctx
  | |- basic_ctx _ _ => intro_wf_ctx
  | |- wf_context_ty_at _ _ _ => intro_wf_type
  | |- basic_context_ty _ _ => intro_wf_type
  | |- _ ∉ _ => intro_set
  | |- _ ## _ => intro_set
  | |- _ ⊆ _ => intro_set
  | |- _ ∈ _ => intro_set
  | |- _ = _ => reflexivity
  end.

(** Close [H : r ⊨ ⟦x:τ⟧_{Σ1}] against the goal [r ⊨ ⟦x:τ⟧_{Σ2}] when the
    two (concrete) environments compute to the same map. *)
Ltac intro_close_by_env_compute H :=
  match type of H with
  | res_models _ (FAnd (basic_world_formula (atom_env_to_lty_env ?E1))
                       (ty_denote ?D1 _ _)) =>
    match goal with
    | |- res_models _ (FAnd (basic_world_formula (atom_env_to_lty_env ?E2))
                            (ty_denote ?D2 _ _)) =>
        replace E1 with E2 in H by (vm_compute; reflexivity);
        replace D1 with D2 in H by (vm_compute; reflexivity);
        exact H
    end
  end.


Section Section1IntroExamples.

Definition x : atom := 101%positive.
Definition y : atom := 102%positive.
Definition f : atom := 103%positive.
Definition c : atom := 104%positive.
Definition c1 : atom := 105%positive.
Definition c2 : atom := 106%positive.
Definition f1 : atom := 107%positive.
Definition f2 : atom := 108%positive.
Definition inner : atom := 109%positive.

Definition nat_minus_program : tm :=
  ret (ƛ x : ℕ =>
    ret (ƛ y : ℕ =>
      let c := x ⟨ ≤ ⟩ y in
      if c then
        ret (vnat 0)
      else
        x ⟨ - ⟩ y)).

Definition captured_minus_fun : tm :=
  ret (ƛ y : ℕ => x ⟨ - ⟩ y).

Definition higher_order_apply_x : tm :=
  ret (ƛ f : ℕ →ᵦ ℕ => f @ x).

Definition static_alias_counterexample : tm :=
  let x := op_natGen ·₁ vnat 0 in
  (ƛ f : ℕ →ᵦ ℕ => f @ x) @ (ƛ y : ℕ => x ⟨ - ⟩ y).

Definition f2_value : value :=
  ƛ y : ℕ =>
    let c1 := y ⟨ ≤ ⟩ vnat 1 in
    let c2 := vnat 1 ⟨ ≤ ⟩ y in
    let c := c1 ⟨ && ⟩ c2 in
    if c then
      ret x
    else
      ret (vnat 2).

Definition dynamic_dependency_counterexample : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := op_natGen ·₁ vnat 0 in
  (ƛ f : ℕ →ᵦ ℕ =>
    let inner := f @ y in
    f @ inner) @ f2_value.

Definition nat_minus_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ ℕ.

Definition unary_nat_fun_ty : ty :=
  ℕ →ᵦ ℕ.

Definition higher_order_apply_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ.

Lemma f2_value_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ᵥ f2_value ⋮ unary_nat_fun_ty.
Proof.
  unfold f2_value, unary_nat_fun_ty.
  eapply basic_typing_lam_named.
  - basic_type_fresh.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply basic_typing_let_named.
      * basic_type_fresh.
      * basic_check.
      * eapply basic_typing_let_named.
        -- basic_type_fresh.
        -- basic_check.
        -- basic_check.
Qed.

Lemma nat_minus_program_basic_type :
  ∅ ⊢ₑ nat_minus_program ⋮ nat_minus_basic_ty.
Proof.
  unfold nat_minus_program, nat_minus_basic_ty.
  basic_check.
Qed.

Lemma captured_minus_fun_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ captured_minus_fun ⋮ unary_nat_fun_ty.
Proof.
  unfold captured_minus_fun, unary_nat_fun_ty.
  basic_check.
Qed.

Lemma intro_minus_body_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    x ⟨ - ⟩ y ⋮ binop_precise_ty bop_minus (avar x) (avar y).
Proof.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma intro_le_guard_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    x ⟨ ≤ ⟩ y ⋮ binop_precise_ty bop_le (avar x) (avar y).
Proof.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma higher_order_apply_x_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ higher_order_apply_x ⋮ higher_order_apply_basic_ty.
Proof.
  unfold higher_order_apply_x, higher_order_apply_basic_ty.
  basic_check.
Qed.

Lemma static_alias_counterexample_basic_type :
  ∅ ⊢ₑ static_alias_counterexample ⋮ ℕ.
Proof.
  unfold static_alias_counterexample, f2_value.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - basic_check.
  - eapply TT_App.
    + eapply basic_typing_lam_named; [basic_type_fresh|basic_check].
    + eapply basic_typing_lam_named; [basic_type_fresh|basic_check].
Qed.

Lemma dynamic_dependency_counterexample_basic_type :
  ∅ ⊢ₑ dynamic_dependency_counterexample ⋮ ℕ.
Proof.
  unfold dynamic_dependency_counterexample, f2_value.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - basic_check.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply TT_App.
      * eapply basic_typing_lam_named; [basic_type_fresh|basic_check].
      * eapply weakening_value.
        -- apply f2_value_basic_type.
        -- apply insert_subseteq.
           apply not_elem_of_dom. basic_type_fresh.
Qed.

(** * Context-type derivations for the Section 1 examples

    Qualifier translation: the paper's refinements over [int]/[nat] are
    translated to [ℕ] qualifiers built from [q_nat_pred] (unary) and
    [q_nat2] (binary).  The paper's [ν > 0] becomes [0 < n] on naturals;
    [x ≥ ν] becomes [ν ≤ x].  In arrow types the result qualifier refers to
    the argument by de Bruijn index ([vbvar 2] for the outer argument of a
    two-argument arrow, [ν = vbvar 0]). *)

Definition q_pos (v : value) : type_qualifier := q_nat_pred v (fun n => 0 < n).
Definition q_ge2 : type_qualifier := q_nat_pred ν (fun n => 2 <= n).

(** [{ν: nat | ν > 0}] and [[ν: nat | ν > 0]]. *)
Definition pos_over : context_ty := {: ℕ | q_pos ν }.
Definition pos_under : context_ty := [: ℕ | q_pos ν ].

(** (τa)  x:{ν>0} → y:{ν>0} → {ν: nat | x ≥ ν}   (paper p.2 l.62) *)
Definition intro_tau_a : context_ty :=
  pos_over → pos_over → {: ℕ | q_nat2 ν (vbvar 2) le }.

(** (τb)  x:[ν>0] → y:[ν>0] → [ν>0]   (paper p.2 l.63) -- see the finding
    below: this literal type is semantically invalid for subtraction/division
    because "," lets the second argument be entangled with the first. *)
Definition intro_tau_b : context_ty :=
  pos_under → pos_under → pos_under.

(** Corrected τb (paper p.3 l.143):  x:[ν>0] → y:[ν>0] -∗ [ν>0]. *)
Definition intro_tau_b_wand : context_ty :=
  pos_under → (pos_under -∗ pos_under).

Lemma intro_pos_under_closed_open k a :
  cty_open k a pos_under = pos_under.
Proof.
  unfold pos_under, q_pos. rewrite intro_cty_open_under.
  rewrite intro_qual_open_q_nat_pred by (cbn; first [exact I|set_solver]).
  unfold vnu. cbn [open_value]. intro_norm_dec. reflexivity.
Qed.

Lemma intro_pos_under_fv : fv_cty pos_under = ∅.
Proof.
  apply set_eq. intros a. split; [ |set_solver]. intros Ha.
  assert (Hwf : wf_context_ty_at 0 ∅ pos_under)
    by (unfold pos_under, q_pos; intro_wf_type).
  pose proof (wf_context_ty_at_fv_subset 0 ∅ pos_under Hwf) as Hsub.
  set_solver.
Qed.

(** ** A branch-free Peano subtraction (paper-faithful stand-in)

    Rocq's [bop_minus] is truncated subtraction, so [x - y] already returns
    [0] when [x ≤ y]; [nat_sub_program] is extensionally equal to
    [nat_minus_program] but has no [if].  Both τa and the corrected τb are
    derivable for it without any case split (since round 2 they are also
    derivable for [nat_minus_program] itself, via [T-CtxCase]). *)
Definition nat_sub_program : tm :=
  ret (ƛ x : ℕ => ret (ƛ y : ℕ => x ⟨ - ⟩ y)).

Lemma nat_sub_program_basic_type :
  ∅ ⊢ₑ nat_sub_program ⋮ nat_minus_basic_ty.
Proof. unfold nat_sub_program, nat_minus_basic_ty. basic_check. Qed.

(** Semantic obligation (τa result):
      x:{ν>0}, y:{ν>0} ⊢ {ν = x - y} ⊓ [ν = x - y] <: {ν ≤ x}.
    Informal argument: the source denotation contains the over-approximate
    conjunct [∀ν. e ↪ ν ⇒ (x,y)▷ O Atom(ν = x - y)], i.e. inside every
    [(x,y)]-fiber every result equals [x - y] (truncated).  Since
    [x - y ≤ x] holds pointwise for all naturals, every [(x,y)]-fiber's
    results satisfy [ν ≤ x]; an [x]-fiber is a union of [(x,y)]-fibers, so
    the exact atom [Atom(ν ≤ x)] is satisfied by the superset of each
    [x]-fiber obtained by adding all missing [ν ≤ x] valuations: this is
    [x ▷ O Atom(ν ≤ x)].  The guard (wf, basic typing, totality of [e]) is
    shared by both sides since the erasures agree.  The context assumption
    [ν > 0] is not even needed.  This is an instance of the generic
    "over-approximate qualifier entailment with context-dependent
    qualifiers" lemma that [ExtendedSubsumption.subtype_over_closed_by_qualifier]
    covers only for context-closed qualifiers. *)
Lemma nat_sub_program_obl_tau_a_result (a b : atom) :
  a <> b ->
  sub_type_under ∅ ((Emp ,, (a ∷ pos_over)) ,, (b ∷ pos_over))
    (binop_precise_ty bop_minus (vfvar a) (vfvar b))
    ({: ℕ | q_nat2 ν (vfvar a) le }).
Proof.
Admitted.

Theorem nat_sub_program_tau_a :
  ∅; Emp ⊢ₓ nat_sub_program ⋮ intro_tau_a.
Proof.
  unfold nat_sub_program, intro_tau_a, lam_named.
  intro_compute_close.
  eapply (EXT_Lam _ _ pos_over) with (L := ({[x]} ∪ {[y]} : aset)).
  - unfold pos_over, q_pos. intro_wf.
  - intros x' Hx'. unfold pos_over, q_pos. intro_norm_open.
    eapply (EXT_Lam _ _ ({: ℕ | q_nat_pred (vbvar 0) (fun n => 0 < n) }))
      with (L := ({[x]} ∪ {[y]} ∪ {[x']} : aset)).
    + intro_wf.
    + intros y' Hy'. intro_norm_open.
      eapply EXT_Sub.
      * intro_wf.
      * eapply EXT_BinOp. intro_wf.
      * apply nat_sub_program_obl_tau_a_result. intro_clear_neq.
Qed.

(** Semantic obligation (corrected τb result):
      x:[ν>0] ∗ y:[ν>0] ⊢ {ν = x - y} ⊓ [ν = x - y] <: [ν > 0].
    Informal argument: a capability [r] of the independent context projects
    on [{x,y}] to a product [r_x × r_y] with [r_x ⊇ {x ↦ n | n > 0}] and
    [r_y ⊇ {y ↦ m | m > 0}].  For every target [n > 0] the environment
    [x ↦ n+1, y ↦ 1] is in the product, and by the precise source type the
    result in that environment is exactly [n+1-1 = n].  Hence the result
    capability contains, for every [n > 0], an environment mapping [ν] to
    [n]; restricting to those environments gives a sub-capability with exact
    [Atom(ν > 0)], i.e. [U Atom(ν > 0)] ([ν > 0] has no other free
    variables, so no [▷] fibering is involved). *)
Lemma nat_sub_program_obl_tau_b_result (a b : atom) :
  a <> b ->
  sub_type_under ∅ ((Emp ,, (a ∷ pos_under)) ∗ (b ∷ pos_under))
    (binop_precise_ty bop_minus (vfvar a) (vfvar b)) pos_under.
Proof.
Admitted.

Theorem nat_sub_program_tau_b_wand :
  ∅; Emp ⊢ₓ nat_sub_program ⋮ intro_tau_b_wand.
Proof.
  unfold nat_sub_program, intro_tau_b_wand, lam_named.
  intro_compute_close.
  eapply (EXT_Lam _ _ pos_under) with (L := ({[x]} ∪ {[y]} : aset)).
  - unfold pos_under, q_pos. intro_wf.
  - intros x' Hx'. cbn [cty_open open_one open_cty_atom_inst].
    rewrite !intro_pos_under_closed_open.
    intro_norm_open.
    eapply (EXT_LamD _ _ pos_under)
      with (L := ({[x]} ∪ {[y]} ∪ {[x']} : aset)).
    + unfold pos_under, q_pos. intro_wf.
    + intros y' Hy'. rewrite intro_pos_under_closed_open. intro_norm_open.
      eapply EXT_Sub.
      * unfold pos_under, q_pos. intro_wf.
      * eapply EXT_BinOp. unfold pos_under, q_pos. intro_wf.
      * apply nat_sub_program_obl_tau_b_result. intro_clear_neq.
Qed.

(** ** [nat_minus_program] = λx.λy. let c = x ≤ y in if c then 0 else x - y

    τa (round 2).  Round 1 reported [∅; Emp ⊢ₓ nat_minus_program ⋮ intro_tau_a]
    as not derivable: after the two lambdas and the [let], the match is typed
    in [Γ1 = x:{ν>0}, y:{ν>0}, c:({ν = (x ≤ y)} ⊓ [ν = (x ≤ y)])], whose
    models [r1 = {[x↦1, y↦1, c↦true]}] and [r2 = {[x↦2, y↦1, c↦false]}] (and
    mixed ones) block each of T-MatchBoth / T-MatchTrueOnly /
    T-MatchFalseOnly individually.  With the capability case split
    [T-CtxCase] the three situations are typed separately; see
    [nat_minus_program_tau_a] below (after [div_guard_program]).

    FINDING (τb, paper p.2, semantically invalid).  [intro_tau_b] uses [→] for
    the second argument, so the body is checked under the entangled context
    [x:[ν>0], y:[ν>0]].  Counterexample capability:
      r = {[x↦n, y↦m] | 1 ≤ n ≤ m}.
    Its [x]-projection and its [y]-projection both contain every positive
    number, so [r ⊨ ⟦x:[ν>0], y:[ν>0]⟧] (the qualifier of [y] does not mention
    [x], so [,] imposes no per-[x] requirement), but [x - y] (and the paper's
    [div x y]) evaluates to [0] (resp. at most [1]) in every environment, so
    [[ν > 0]] is violated.  This is exactly the paper's own explanation on
    p.3 l.139-146 / p.7 l.331-338; the literal τb on p.2 is therefore not a
    valid typing, the corrected type is [intro_tau_b_wand]. *)

(** Contexts used for the two reachable branches. *)
Definition q_minus_false_y (a : atom) : type_qualifier :=
  q_nat2 ν (vfvar a)
    (fun v n => (2 <= n /\ v = 1%nat) \/ (n < 2 /\ v = 0%nat)).

Definition nat_minus_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_under)) ∗ (b ∷ pos_under)) ,,
    (c0 ∷ binop_precise_ty bop_le (vfvar a) (vfvar b)).

(** True part: no requirement on [x, y]; [c] is precisely [true]. *)
Definition nat_minus_true_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ ONat)) ,, (b ∷ ONat)) ,, (c0 ∷ bool_precise_ty true).

(** False part: [x] reaches every value [≥ 2]; for each such [x] the fiber of
    [y] reaches [1] (and for [x = 1] -- only present if [0] is reachable for
    [y] -- it reaches [0]); [c] is precisely [false]. *)
Definition nat_minus_false_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ [: ℕ | q_ge2 ])) ,, (b ∷ [: ℕ | q_minus_false_y a ])) ,,
    (c0 ∷ bool_precise_ty false).

(** Obligation (branch split, T-CtxSub):
      Γ1 ≤_{x,y,c} Γt ⊕ Γf.
    Informal argument: let [r ⊨ ⟦Γ1⟧].  Its projection on [{x,y}] is a product
    [r_x × r_y] with [r_x, r_y ⊇ {n | n > 0}], and in each environment
    [c = (x ≤ y)].  Take [r' = r|{x,y,c}] and split it into
    [T = {σ ∈ r' | σ(c) = true}] and [F = {σ ∈ r' | σ(c) = false}].  Both are
    non-empty ([x↦1,y↦1] ∈ T, [x↦2,y↦1] ∈ F) and have the same domain, so
    [T + F = r'].  [T ⊨ ⟦Γt⟧]: the [x], [y] bindings are [{⊤}] and [c] is
    exactly [true] in a non-empty capability.  [F ⊨ ⟦Γf⟧]: for every [n ≥ 2],
    [x↦n, y↦1, c↦false ∈ F], so the [x]-projection covers [ν ≥ 2]; in the
    [x]-fiber [n ≥ 2] the value [y = 1] occurs, in the [x]-fiber [n = 1] (which
    only exists when [0 ∈ r_y]) the only [y] value is [0], and [x = 0] never
    occurs in [F]; so every [x]-fiber of [y] contains exactly the qualifier's
    set as a sub-capability ([x ▷ U Atom(...)]); [c] is exactly [false]. *)
Lemma nat_minus_program_obl_split (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ ({[a]} ∪ {[b]} ∪ {[c0]} : aset)
    (nat_minus_ctx a b c0)
    (nat_minus_true_ctx a b c0 ⊕ nat_minus_false_ctx a b c0).
Proof.
Admitted.

(** Obligation (guard in the true part): projection of the last [,]-binding,
    whose type is closed.  Informal argument: [⟦Γ, c:τ⟧ = ⟦Γ⟧ ∧ ⟦c:τ⟧] and
    [⟦c:τ⟧] only mentions [c] (the type [bool_precise_ty true] is closed), so
    [r|{c}] satisfies [⟦c:τ⟧] (formulas are stable under restriction to a
    superset of their free variables). *)
Lemma nat_minus_program_obl_true_guard (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ {[c0]} (nat_minus_true_ctx a b c0)
    (c0 ∷ bool_precise_ty true).
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold nat_minus_true_ctx, pos_under, q_pos, q_minus_false_y, q_ge2, wf_ctx_under.
    intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = c0) by set_solver. subst z.
    unfold nat_minus_true_ctx. intro_erase.
    etransitivity; [apply map_lookup_insert| symmetry; apply map_lookup_insert].
  - intros r Hr. unfold nat_minus_true_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c0 (bool_precise_ty true)) = ∅)
      by (apply intro_closed_fv; intro_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

(** Obligation (guard in the false part): same projection argument. *)
Lemma nat_minus_program_obl_false_guard (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ {[c0]} (nat_minus_false_ctx a b c0)
    (c0 ∷ bool_precise_ty false).
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold nat_minus_false_ctx, pos_under, q_pos, q_minus_false_y, q_ge2, wf_ctx_under.
    intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = c0) by set_solver. subst z.
    unfold nat_minus_false_ctx. intro_erase.
    etransitivity; [apply map_lookup_insert| symmetry; apply map_lookup_insert].
  - intros r Hr. unfold nat_minus_false_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c0 (bool_precise_ty false)) = ∅)
      by (apply intro_closed_fv; intro_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

(** Obligation (constant branch): every satisfiable context refines [Emp] on
    the empty variable set: [r|∅] is the unit capability, which satisfies
    [⟦Emp⟧ = ⊤] (and the empty basic-world formula). *)
Lemma nat_minus_program_obl_true_const (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ ∅ (nat_minus_true_ctx a b c0) Emp.
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold nat_minus_true_ctx, wf_ctx_under. intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. set_solver.
  - intros r _. cbn [ctx_denote_under].
    apply res_models_and_iff. split; [ |apply res_models_true].
    match goal with |- res_models _ (basic_world_formula ?E) =>
      replace E with (∅ : lty_env) by (vm_compute; reflexivity) end.
    apply basic_world_formula_empty.
Qed.

(** Obligation (reachability of the false branch):
      Γf ⊢ {ν = x - y} ⊓ [ν = x - y] <: [ν > 0].
    Informal argument: in any capability of [Γf], for every [n ≥ 2] there is
    an environment with [x ↦ n] and, in that [x]-fiber, one with [y ↦ 1]
    (from [y:[q_minus_false_y x]]); by the precise source type the result
    there is [n - 1].  So all positive numbers are reached:
    [U Atom(ν > 0)]. *)
Lemma nat_minus_program_obl_false_reach (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅ (nat_minus_false_ctx a b c0)
    (binop_precise_ty bop_minus (vfvar a) (vfvar b)) pos_under.
Proof.
Admitted.

(** Obligation (affine sum elimination):
      Γt ⊕ Γf ⊢ ({ν = 0} ⊓ [ν = 0]) ⊕ [ν > 0] <: [ν > 0].
    Informal argument: the sum denotation splits every result capability into
    two non-empty parts whose union is the whole; the second part already
    contains a sub-capability with exactly the positive results, which is also
    a sub-capability of the whole, so [U Atom(ν > 0)] holds. *)
Lemma nat_minus_program_obl_sum_reach (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅ (nat_minus_true_ctx a b c0 ⊕ nat_minus_false_ctx a b c0)
    (const_precise_ty (cnat 0) ⊕ pos_under) pos_under.
Proof.
Admitted.

Theorem nat_minus_program_tau_b_wand :
  ∅; Emp ⊢ₓ nat_minus_program ⋮ intro_tau_b_wand.
Proof.
  unfold nat_minus_program, intro_tau_b_wand, lam_named, let_named.
  intro_compute_close.
  eapply (EXT_Lam _ _ pos_under) with (L := ({[x]} ∪ {[y]} ∪ {[c]} : aset)).
  - unfold pos_under, q_pos. intro_wf.
  - intros x' Hx'. cbn [cty_open open_one open_cty_atom_inst].
    rewrite !intro_pos_under_closed_open.
    intro_norm_open.
    eapply (EXT_LamD _ _ pos_under)
      with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} : aset)).
    + unfold pos_under, q_pos. intro_wf.
    + intros y' Hy'. rewrite intro_pos_under_closed_open. intro_norm_open.
      eapply (EXT_Let _ _ (binop_precise_ty bop_le (vfvar x') (vfvar y')))
        with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} ∪ {[y']} : aset)).
      * unfold pos_under, q_pos. intro_wf.
      * eapply EXT_BinOp. unfold pos_under, q_pos. intro_wf.
      * intros c' Hc'. intro_norm_open.
        assert (Hxy : x' <> y') by intro_clear_neq.
        assert (Hxc : x' <> c') by intro_clear_neq.
        assert (Hyc : y' <> c') by intro_clear_neq.
        change (((Emp ,, (x' ∷ pos_under)) ∗ (y' ∷ pos_under)) ,,
                  (c' ∷ binop_precise_ty bop_le (vfvar x') (vfvar y')))
          with (nat_minus_ctx x' y' c').
        eapply (intro_ext_ctx_sub _ _
          (nat_minus_true_ctx x' y' c' ⊕ nat_minus_false_ctx x' y' c')
          ({[x']} ∪ {[y']} ∪ {[c']} : aset)).
        -- unfold nat_minus_ctx, pos_under, q_pos. intro_wf.
        -- eapply (EXT_Sub _ _ _ (const_precise_ty (cnat 0) ⊕ pos_under)).
           ++ unfold nat_minus_true_ctx, nat_minus_false_ctx, q_minus_false_y,
                q_ge2, pos_under, q_pos. intro_wf.
           ++ change (tmatch (vfvar c') (tret (vconst (cnat 0)))
                        (tbinop bop_minus (vfvar x') (vfvar y')))
                with (if (avar c') then ret (vnat 0) else (x' ⟨ - ⟩ y')).
              eapply EXT_MatchBoth.
              ** unfold nat_minus_true_ctx, nat_minus_false_ctx, q_minus_false_y,
                   q_ge2, pos_under, q_pos. intro_wf.
              ** eapply (intro_ext_ctx_sub _ _ (c' ∷ bool_precise_ty true) ({[c']} : aset)).
                 --- unfold nat_minus_true_ctx. intro_wf.
                 --- eapply EXT_Var. intro_wf.
                 --- intro_dom_sub.
                 --- apply nat_minus_program_obl_true_guard; assumption.
              ** eapply (intro_ext_ctx_sub _ _ (c' ∷ bool_precise_ty false) ({[c']} : aset)).
                 --- unfold nat_minus_false_ctx, q_minus_false_y, q_ge2. intro_wf.
                 --- eapply EXT_Var. intro_wf.
                 --- intro_dom_sub.
                 --- apply nat_minus_program_obl_false_guard; assumption.
              ** eapply (intro_ext_ctx_sub _ _ Emp (∅ : aset)).
                 --- unfold nat_minus_true_ctx. intro_wf.
                 --- eapply EXT_Const. intro_wf.
                 --- intro_dom_sub.
                 --- apply nat_minus_program_obl_true_const; assumption.
              ** eapply EXT_Sub.
                 --- unfold nat_minus_false_ctx, q_minus_false_y, q_ge2,
                       pos_under, q_pos. intro_wf.
                 --- eapply EXT_BinOp. unfold nat_minus_false_ctx,
                       q_minus_false_y, q_ge2. intro_wf.
                 --- apply nat_minus_program_obl_false_reach; assumption.
           ++ apply nat_minus_program_obl_sum_reach; assumption.
        -- unfold nat_minus_true_ctx, nat_minus_false_ctx. intro_dom_sub.
        -- apply nat_minus_program_obl_split; assumption.
Qed.

(** ** Paper-shaped division guard: λx.λy. if y ≤ 0 then x else x - y

    The paper's [div] (p.2 l.53) tests [y ≤ 0] and otherwise recurses
    ([fst (divmod x (y-1) 0 (y-1))]).  We keep the guard and replace the
    recursive call by truncated subtraction (the same stand-in as
    [nat_minus_program]).

    τa IS derivable: under the demonic [y:{ν>0}] the guard is always [false],
    so T-MatchFalseOnly applies (the unreachable [then] branch is not typed).

    Corrected τb (round 2).  Round 1 reported
    [∅; Emp ⊢ₓ div_guard_program ⋮ intro_tau_b_wand] (the paper's ✓ on p.3
    l.143 for [div]) as not derivable: under the angelic [y:[ν>0]] the value
    [y ↦ 0] may be absent (then-branch unreachable) or present (guard not
    constant).  With [T-CtxCase] both situations are typed separately; see
    [div_guard_program_tau_b_wand] below. *)
Definition div_guard_program : tm :=
  ret (ƛ x : ℕ =>
    ret (ƛ y : ℕ =>
      let c := y ⟨ ≤ ⟩ vnat 0 in
      if c then
        ret x
      else
        x ⟨ - ⟩ y)).

Lemma div_guard_program_basic_type :
  ∅ ⊢ₑ div_guard_program ⋮ nat_minus_basic_ty.
Proof. unfold div_guard_program, nat_minus_basic_ty. basic_check. Qed.

Definition div_guard_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_over)) ,, (b ∷ pos_over)) ,,
    (c0 ∷ binop_precise_ty bop_le (vfvar b) (vconst (cnat 0))).

(** Obligation (guard determined):  Γ1 ≤_{c} c:({ν = false} ⊓ [ν = false]).
    Informal argument: in every environment of a capability of [Γ1],
    [y > 0] (demonic binding: [O Atom(ν > 0)] means all [y]-values are
    positive) and [c = (y ≤ 0)] (precise binop type), hence [c = false]
    everywhere; capabilities are non-empty, so [r|{c} = {[c ↦ false]}],
    which satisfies both [O Atom(ν = false)] and [U Atom(ν = false)]. *)
Lemma div_guard_program_obl_guard_false (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ ({[c0]} : aset) (div_guard_ctx a b c0)
    (c0 ∷ bool_precise_ty false).
Proof.
Admitted.

(** Obligation (τa result in the false branch): as
    [nat_sub_program_obl_tau_a_result], in a context extended by an
    independent closed-qualifier-free binding of [c]: pointwise
    [x - y ≤ x]. *)
Lemma div_guard_program_obl_result (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅ (div_guard_ctx a b c0)
    (binop_precise_ty bop_minus (vfvar a) (vfvar b))
    ({: ℕ | q_nat2 ν (vfvar a) le }).
Proof.
Admitted.

Theorem div_guard_program_tau_a :
  ∅; Emp ⊢ₓ div_guard_program ⋮ intro_tau_a.
Proof.
  unfold div_guard_program, intro_tau_a, lam_named, let_named.
  intro_compute_close.
  eapply (EXT_Lam _ _ pos_over) with (L := ({[x]} ∪ {[y]} ∪ {[c]} : aset)).
  - unfold pos_over, q_pos. intro_wf.
  - intros x' Hx'. unfold pos_over, q_pos. intro_norm_open.
    eapply (EXT_Lam _ _ ({: ℕ | q_nat_pred (vbvar 0) (fun n => 0 < n) }))
      with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} : aset)).
    + intro_wf.
    + intros y' Hy'. intro_norm_open.
      eapply (EXT_Let _ _
        (binop_precise_ty bop_le (vfvar y') (vconst (cnat 0))))
        with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} ∪ {[y']} : aset)).
      * intro_wf.
      * eapply EXT_BinOp. intro_wf.
      * intros c' Hc'. intro_norm_open.
        assert (Hxy : x' <> y') by intro_clear_neq.
        assert (Hxc : x' <> c') by intro_clear_neq.
        assert (Hyc : y' <> c') by intro_clear_neq.
        change (tmatch (vfvar c') (tret (vfvar x'))
                  (tbinop bop_minus (vfvar x') (vfvar y')))
          with (if (avar c') then ret (avar x') else (x' ⟨ - ⟩ y')).
        eapply EXT_MatchFalseOnly.
        -- intro_wf.
        -- eapply (intro_ext_ctx_sub _ _ (c' ∷ bool_precise_ty false)
              ({[c']} : aset)).
           ++ intro_wf.
           ++ eapply EXT_Var. intro_wf.
           ++ intro_dom_sub.
           ++ apply div_guard_program_obl_guard_false; assumption.
        -- eapply EXT_Sub.
           ++ intro_wf.
           ++ eapply EXT_BinOp. intro_wf.
           ++ apply div_guard_program_obl_result; assumption.
Qed.

(** ** Round 2: [nat_minus_program] at τa via T-CtxCase

    Round 1 reported [∅; Emp ⊢ₓ nat_minus_program ⋮ intro_tau_a] as not
    derivable: in the demonic body context
      Γ1 = x:{ν>0}, y:{ν>0}, c:({ν = (x ≤ y)} ⊓ [ν = (x ≤ y)])
    the guard [c] is not determined, and models may make the [then] branch,
    the [else] branch, or both reachable.  The capability case split
    [T-CtxCase] covers the three situations separately:
    - every environment has [c = true]: [T-MatchTrueOnly] in [Γtrue];
    - otherwise [false] is reachable for [c] ([Γ¬true]), and then either
      every environment has [c = false] ([T-MatchFalseOnly] in [Γfalse]) or
      both values occur ([T-MatchBoth] in [Γtrue ⊕ Γfalse]).
    The branch contexts forget the correlation [c = (x ≤ y)]: neither branch
    needs it, since [0 ≤ x] and the truncated [x - y ≤ x] hold pointwise. *)

Definition nat_minus_le_ty (a : atom) : context_ty :=
  {: ℕ | q_nat2 ν (vfvar a) le }.

Definition nat_minus_over_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_over)) ,, (b ∷ pos_over)) ,,
    (c0 ∷ binop_precise_ty bop_le (vfvar a) (vfvar b)).

Definition nat_minus_over_true_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_over)) ,, (b ∷ pos_over)) ,, (c0 ∷ bool_precise_ty true).

Definition nat_minus_over_false_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_over)) ,, (b ∷ pos_over)) ,, (c0 ∷ bool_precise_ty false).

(** "[false] is reachable for [c]": [c:[ν = false]] (closed under type, so
    no fibering: some environment has [c = false]). *)
Definition nat_minus_over_nottrue_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_over)) ,, (b ∷ pos_over)) ,, (c0 ∷ under_ty TBool q_false).

(** Obligation (outer case split): [Γ1 ⊑_{x,y,c} Γtrue  or  Γ¬true].
    Informal argument: let [r ⊨ ⟦Γ1⟧] and [r' = r|{x,y,c}].  The [x]- and
    [y]-bindings are demonic ([O Atom(ν>0)]); they hold of [r'] in both
    target contexts because they are the same bindings.  By the precise
    binding of [c], every environment has [c = (x ≤ y)].  If every
    environment has [c = true], then ([r'] being non-empty)
    [r'|{c} = {c ↦ true}] satisfies the closed [{ν = true} ⊓ [ν = true]], so
    [r' ⊨ ⟦Γtrue⟧].  Otherwise some environment has [c = false], so the
    sub-capability [{c ↦ false}] of [r'|{c}] witnesses [U Atom(ν = false)]
    and [r' ⊨ ⟦Γ¬true⟧]. *)
Lemma nat_minus_program_tau_a_obl_case_true (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_case_under ∅ ({[a]} ∪ {[b]} ∪ {[c0]} : aset)
    (nat_minus_over_ctx a b c0)
    (nat_minus_over_true_ctx a b c0) (nat_minus_over_nottrue_ctx a b c0).
Proof.
Admitted.

(** Obligation (inner case split): [Γ¬true ⊑_{x,y,c} Γfalse  or
    Γtrue ⊕ Γfalse].
    Informal argument: let [r ⊨ ⟦Γ¬true⟧], [r' = r|{x,y,c}].  If every
    environment has [c = false], [r' ⊨ ⟦Γfalse⟧] as above.  Otherwise both
    [c = true] and (by [U Atom(ν = false)]) [c = false] occur; split [r'] into
    [T = {σ | σ(c) = true}] and [F = {σ | σ(c) = false}]: both non-empty, same
    domain, [T ∪ F = r'], hence [r' = T + F]; the demonic [x]/[y] bindings
    hold of every sub-capability, and [c] is exactly [true] on [T] and
    exactly [false] on [F], so [T ⊨ ⟦Γtrue⟧] and [F ⊨ ⟦Γfalse⟧]. *)
Lemma nat_minus_program_tau_a_obl_case_rest (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_case_under ∅ ({[a]} ∪ {[b]} ∪ {[c0]} : aset)
    (nat_minus_over_nottrue_ctx a b c0)
    (nat_minus_over_false_ctx a b c0)
    (nat_minus_over_true_ctx a b c0 ⊕ nat_minus_over_false_ctx a b c0).
Proof.
Admitted.

(** Obligation ([then] branch): [Γtrue ⊢ {ν = 0} ⊓ [ν = 0] <: {ν ≤ x}].
    Informal argument: in every environment the result is [0] (over part of
    the precise constant type) and [0 ≤ x] holds for every natural [x]; each
    [x]-fiber's results therefore satisfy [ν ≤ x], and the exact atom
    [Atom(ν ≤ x)] holds of the superset of each fiber obtained by adding the
    missing [ν ≤ x] valuations ([x ▷ O Atom(ν ≤ x)]). *)
Lemma nat_minus_program_tau_a_obl_zero (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅ (nat_minus_over_true_ctx a b c0)
    (const_precise_ty (cnat 0)) (nat_minus_le_ty a).
Proof.
Admitted.

(** Obligation ([else] branch): [Γfalse ⊢ {ν = x - y} ⊓ [ν = x - y] <: {ν ≤ x}].
    Same argument as [nat_sub_program_obl_tau_a_result]: pointwise
    [x - y ≤ x] (truncated subtraction); the [c]-binding is irrelevant. *)
Lemma nat_minus_program_tau_a_obl_false_result (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅ (nat_minus_over_false_ctx a b c0)
    (binop_precise_ty bop_minus (vfvar a) (vfvar b)) (nat_minus_le_ty a).
Proof.
Admitted.

(** Obligation (sum of demonic results):
      Γtrue ⊕ Γfalse ⊢ {ν ≤ x} ⊕ {ν ≤ x} <: {ν ≤ x}.
    Informal argument: a result capability of the sum is [m1 + m2] (same
    domain, union of environments) with [m1], [m2] both satisfying
    [x ▷ O Atom(ν ≤ x)]; each [x]-fiber of [m1 + m2] is the union of the
    corresponding fibers of [m1] and [m2] (one of which may be empty), all of
    whose results satisfy [ν ≤ x]; so the union also satisfies
    [x ▷ O Atom(ν ≤ x)]. *)
Lemma nat_minus_program_tau_a_obl_sum (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅
    (nat_minus_over_true_ctx a b c0 ⊕ nat_minus_over_false_ctx a b c0)
    (nat_minus_le_ty a ⊕ nat_minus_le_ty a) (nat_minus_le_ty a).
Proof.
Admitted.

(** Structural projections (Qed). *)
Lemma nat_minus_program_tau_a_obl_true_guard (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ {[c0]} (nat_minus_over_true_ctx a b c0)
    (c0 ∷ bool_precise_ty true).
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold nat_minus_over_true_ctx, pos_over, q_pos, wf_ctx_under.
    intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = c0) by set_solver. subst z.
    unfold nat_minus_over_true_ctx. intro_erase.
    etransitivity; [apply map_lookup_insert| symmetry; apply map_lookup_insert].
  - intros r Hr. unfold nat_minus_over_true_ctx in Hr.
    cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c0 (bool_precise_ty true)) = ∅)
      by (apply intro_closed_fv; intro_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

Lemma nat_minus_program_tau_a_obl_false_guard (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ {[c0]} (nat_minus_over_false_ctx a b c0)
    (c0 ∷ bool_precise_ty false).
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold nat_minus_over_false_ctx, pos_over, q_pos, wf_ctx_under.
    intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = c0) by set_solver. subst z.
    unfold nat_minus_over_false_ctx. intro_erase.
    etransitivity; [apply map_lookup_insert| symmetry; apply map_lookup_insert].
  - intros r Hr. unfold nat_minus_over_false_ctx in Hr.
    cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c0 (bool_precise_ty false)) = ∅)
      by (apply intro_closed_fv; intro_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

Lemma nat_minus_program_tau_a_obl_true_const (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ ∅ (nat_minus_over_true_ctx a b c0) Emp.
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold nat_minus_over_true_ctx, pos_over, q_pos, wf_ctx_under.
    intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. set_solver.
  - intros r _. cbn [ctx_denote_under].
    apply res_models_and_iff. split; [ |apply res_models_true].
    match goal with |- res_models _ (basic_world_formula ?E) =>
      replace E with (∅ : lty_env) by (vm_compute; reflexivity) end.
    apply basic_world_formula_empty.
Qed.

(** Branch derivations (structural, Qed modulo the obligations above). *)
Lemma nat_minus_program_tau_a_true_part (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ∅; nat_minus_over_true_ctx a b c0 ⊢ₓ
    (if (avar c0) then ret (vnat 0) else (a ⟨ - ⟩ b)) ⋮ nat_minus_le_ty a.
Proof.
  intros Hab Hac Hbc.
  eapply EXT_MatchTrueOnly.
  - unfold nat_minus_over_true_ctx, nat_minus_le_ty, pos_over, q_pos. intro_wf.
  - eapply (intro_ext_ctx_sub _ _ (c0 ∷ bool_precise_ty true) ({[c0]} : aset)).
    + unfold nat_minus_over_true_ctx, pos_over, q_pos. intro_wf.
    + eapply EXT_Var. intro_wf.
    + intro_dom_sub.
    + apply nat_minus_program_tau_a_obl_true_guard; assumption.
  - eapply (EXT_Sub _ _ _ (const_precise_ty (cnat 0))).
    + unfold nat_minus_over_true_ctx, nat_minus_le_ty, pos_over, q_pos. intro_wf.
    + eapply (intro_ext_ctx_sub _ _ Emp (∅ : aset)).
      * unfold nat_minus_over_true_ctx, pos_over, q_pos. intro_wf.
      * eapply EXT_Const. intro_wf.
      * intro_dom_sub.
      * apply nat_minus_program_tau_a_obl_true_const; assumption.
    + apply nat_minus_program_tau_a_obl_zero; assumption.
Qed.

Lemma nat_minus_program_tau_a_false_part (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ∅; nat_minus_over_false_ctx a b c0 ⊢ₓ
    (if (avar c0) then ret (vnat 0) else (a ⟨ - ⟩ b)) ⋮ nat_minus_le_ty a.
Proof.
  intros Hab Hac Hbc.
  eapply EXT_MatchFalseOnly.
  - unfold nat_minus_over_false_ctx, nat_minus_le_ty, pos_over, q_pos. intro_wf.
  - eapply (intro_ext_ctx_sub _ _ (c0 ∷ bool_precise_ty false) ({[c0]} : aset)).
    + unfold nat_minus_over_false_ctx, pos_over, q_pos. intro_wf.
    + eapply EXT_Var. intro_wf.
    + intro_dom_sub.
    + apply nat_minus_program_tau_a_obl_false_guard; assumption.
  - eapply EXT_Sub.
    + unfold nat_minus_over_false_ctx, nat_minus_le_ty, pos_over, q_pos. intro_wf.
    + eapply EXT_BinOp. unfold nat_minus_over_false_ctx, pos_over, q_pos. intro_wf.
    + apply nat_minus_program_tau_a_obl_false_result; assumption.
Qed.

Lemma nat_minus_program_tau_a_body (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ∅; nat_minus_over_ctx a b c0 ⊢ₓ
    (if (avar c0) then ret (vnat 0) else (a ⟨ - ⟩ b)) ⋮ nat_minus_le_ty a.
Proof.
  intros Hab Hac Hbc.
  eapply (intro_ext_ctx_case _ _ (nat_minus_over_true_ctx a b c0)
    (nat_minus_over_nottrue_ctx a b c0) ({[a]} ∪ {[b]} ∪ {[c0]} : aset)).
  - unfold nat_minus_over_ctx, nat_minus_le_ty, pos_over, q_pos. intro_wf.
  - apply nat_minus_program_tau_a_true_part; assumption.
  - eapply (intro_ext_ctx_case _ _ (nat_minus_over_false_ctx a b c0)
      (nat_minus_over_true_ctx a b c0 ⊕ nat_minus_over_false_ctx a b c0)
      ({[a]} ∪ {[b]} ∪ {[c0]} : aset)).
    + unfold nat_minus_over_nottrue_ctx, nat_minus_le_ty, pos_over, q_pos.
      intro_wf.
    + apply nat_minus_program_tau_a_false_part; assumption.
    + eapply (EXT_Sub _ _ _ (nat_minus_le_ty a ⊕ nat_minus_le_ty a)).
      * unfold nat_minus_over_true_ctx, nat_minus_over_false_ctx,
          nat_minus_le_ty, pos_over, q_pos. intro_wf.
      * eapply EXT_MatchBoth.
        -- unfold nat_minus_over_true_ctx, nat_minus_over_false_ctx,
             nat_minus_le_ty, pos_over, q_pos. intro_wf.
        -- eapply (intro_ext_ctx_sub _ _ (c0 ∷ bool_precise_ty true) ({[c0]} : aset)).
           ++ unfold nat_minus_over_true_ctx, pos_over, q_pos. intro_wf.
           ++ eapply EXT_Var. intro_wf.
           ++ intro_dom_sub.
           ++ apply nat_minus_program_tau_a_obl_true_guard; assumption.
        -- eapply (intro_ext_ctx_sub _ _ (c0 ∷ bool_precise_ty false) ({[c0]} : aset)).
           ++ unfold nat_minus_over_false_ctx, pos_over, q_pos. intro_wf.
           ++ eapply EXT_Var. intro_wf.
           ++ intro_dom_sub.
           ++ apply nat_minus_program_tau_a_obl_false_guard; assumption.
        -- eapply (EXT_Sub _ _ _ (const_precise_ty (cnat 0))).
           ++ unfold nat_minus_over_true_ctx, nat_minus_le_ty, pos_over, q_pos.
              intro_wf.
           ++ eapply (intro_ext_ctx_sub _ _ Emp (∅ : aset)).
              ** unfold nat_minus_over_true_ctx, pos_over, q_pos. intro_wf.
              ** eapply EXT_Const. intro_wf.
              ** intro_dom_sub.
              ** apply nat_minus_program_tau_a_obl_true_const; assumption.
           ++ apply nat_minus_program_tau_a_obl_zero; assumption.
        -- eapply EXT_Sub.
           ++ unfold nat_minus_over_false_ctx, nat_minus_le_ty, pos_over, q_pos.
              intro_wf.
           ++ eapply EXT_BinOp. unfold nat_minus_over_false_ctx, pos_over, q_pos.
              intro_wf.
           ++ apply nat_minus_program_tau_a_obl_false_result; assumption.
      * apply nat_minus_program_tau_a_obl_sum; assumption.
    + unfold nat_minus_over_false_ctx. intro_dom_sub.
    + apply nat_minus_program_tau_a_obl_case_rest; assumption.
  - unfold nat_minus_over_true_ctx. intro_dom_sub.
  - apply nat_minus_program_tau_a_obl_case_true; assumption.
Qed.

Theorem nat_minus_program_tau_a :
  ∅; Emp ⊢ₓ nat_minus_program ⋮ intro_tau_a.
Proof.
  unfold nat_minus_program, intro_tau_a, lam_named, let_named.
  intro_compute_close.
  eapply (EXT_Lam _ _ pos_over) with (L := ({[x]} ∪ {[y]} ∪ {[c]} : aset)).
  - unfold pos_over, q_pos. intro_wf.
  - intros x' Hx'. unfold pos_over, q_pos. intro_norm_open.
    eapply (EXT_Lam _ _ ({: ℕ | q_nat_pred (vbvar 0) (fun n => 0 < n) }))
      with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} : aset)).
    + intro_wf.
    + intros y' Hy'. intro_norm_open.
      eapply (EXT_Let _ _ (binop_precise_ty bop_le (vfvar x') (vfvar y')))
        with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} ∪ {[y']} : aset)).
      * intro_wf.
      * eapply EXT_BinOp. intro_wf.
      * intros c' Hc'. intro_norm_open.
        assert (Hxy : x' <> y') by intro_clear_neq.
        assert (Hxc : x' <> c') by intro_clear_neq.
        assert (Hyc : y' <> c') by intro_clear_neq.
        change (tmatch (vfvar c') (tret (vconst (cnat 0)))
                  (tbinop bop_minus (vfvar x') (vfvar y')))
          with (if (avar c') then ret (vnat 0) else (x' ⟨ - ⟩ y')).
        change (((Emp ,, (x' ∷ {: ℕ | q_nat_pred (vbvar 0) (fun n => 0 < n) })) ,,
                   (y' ∷ {: ℕ | q_nat_pred (vbvar 0) (fun n => 0 < n) })) ,,
                  (c' ∷ binop_precise_ty bop_le (vfvar x') (vfvar y')))
          with (nat_minus_over_ctx x' y' c').
        change ({: ℕ | q_nat2 (vbvar 0) (vfvar x') le }) with (nat_minus_le_ty x').
        apply nat_minus_program_tau_a_body; assumption.
Qed.

(** ** Round 2: [div_guard_program] at the corrected τb via T-CtxCase

    Round 1 reported [∅; Emp ⊢ₓ div_guard_program ⋮ intro_tau_b_wand] (the
    paper's ✓ on p.3 l.143 for [div]) as not derivable: in the body context
      Γ1 = (x:[ν>0] ∗ y:[ν>0]), c:({ν = (y ≤ 0)} ⊓ [ν = (y ≤ 0)])
    the angelic [y] may or may not reach [0].  With [T-CtxCase]:
    - if no environment has [y = 0], [c] is constantly [false]:
      [T-MatchFalseOnly] in [Γfalse] (which keeps the independent
      [x:[ν>0] ∗ y:[ν>0]], needed for the reachability of [x - y]);
    - otherwise both branches are reachable: the [y = 0] environments form
      a model of [Γtrue = x:[ν>0], y:O[ℕ], c:true] (the [x]-projection of a
      product is unchanged by fixing [y = 0]) and the [y > 0] environments a
      model of [Γfalse]; [T-MatchBoth], then [[ν>0] ⊕ [ν>0] <: [ν>0]]. *)

Definition div_wand_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_under)) ∗ (b ∷ pos_under)) ,,
    (c0 ∷ binop_precise_ty bop_le (vfvar b) (vconst (cnat 0))).

Definition div_wand_false_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_under)) ∗ (b ∷ pos_under)) ,, (c0 ∷ bool_precise_ty false).

Definition div_wand_true_ctx (a b c0 : atom) : ctx :=
  ((Emp ,, (a ∷ pos_under)) ,, (b ∷ ONat)) ,, (c0 ∷ bool_precise_ty true).

(** Obligation (case split): [Γ1 ⊑_{x,y,c} Γfalse  or  Γtrue ⊕ Γfalse].
    Informal argument: let [r ⊨ ⟦Γ1⟧], [r' = r|{x,y,c}].  [r'|{x,y}] is a
    product [r_x × r_y] with [r_x, r_y ⊇ {n | n > 0}] (as sub-capabilities
    with exactly the positive values), and every environment has
    [c = (y ≤ 0)], i.e. [c = (y = 0)].
    - If [0 ∉ r_y], then [c = false] everywhere and [r' ⊨ ⟦Γfalse⟧]
      ([r'] is non-empty, [r'|{c} = {c ↦ false}]).
    - If [0 ∈ r_y], let [T = {σ ∈ r' | σ(y) = 0}] and
      [F = {σ ∈ r' | σ(y) > 0}].  Both are non-empty, have domain
      [{x,y,c}] and [T ∪ F = r'], so [r' = T + F].  [T|{x,y} = r_x × {0}]:
      its [x]-projection is [r_x ⊇ positives] ([U Atom(ν>0)]), [y] is
      unconstrained ([O[ℕ]]), [c = true] on [T]: [T ⊨ ⟦Γtrue⟧].
      [F|{x,y} = r_x × (r_y ∖ {0})], again a product of capabilities whose
      projections contain all positive values, and [c = false] on [F]:
      [F ⊨ ⟦Γfalse⟧]. *)
Lemma div_guard_program_wand_obl_case (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_case_under ∅ ({[a]} ∪ {[b]} ∪ {[c0]} : aset)
    (div_wand_ctx a b c0)
    (div_wand_false_ctx a b c0)
    (div_wand_true_ctx a b c0 ⊕ div_wand_false_ctx a b c0).
Proof.
Admitted.

(** Obligation ([else] branch reachability):
      x:[ν>0] ∗ y:[ν>0], c:false ⊢ {ν = x - y} ⊓ [ν = x - y] <: [ν > 0].
    Same argument as [nat_sub_program_obl_tau_b_result]: the product
    contains [x ↦ n+1, y ↦ 1] for every [n > 0], with result exactly [n];
    the closed [c]-binding is irrelevant. *)
Lemma div_guard_program_wand_obl_false_reach (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅ (div_wand_false_ctx a b c0)
    (binop_precise_ty bop_minus (vfvar a) (vfvar b)) pos_under.
Proof.
Admitted.

(** Obligation (sum of angelic results):
      Γtrue ⊕ Γfalse ⊢ [ν>0] ⊕ [ν>0] <: [ν>0].
    Informal argument: a result capability of the sum is [m1 + m2] with both
    summands non-empty and [m1 ⊨ U Atom(ν > 0)]; the sub-capability of [m1]
    whose results are exactly the positive numbers is a sub-capability of
    [m1 + m2]. *)
Lemma div_guard_program_wand_obl_sum (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  sub_type_under ∅ (div_wand_true_ctx a b c0 ⊕ div_wand_false_ctx a b c0)
    (pos_under ⊕ pos_under) pos_under.
Proof.
Admitted.

(** Structural projections (Qed). *)
Lemma div_guard_program_wand_obl_false_guard (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ {[c0]} (div_wand_false_ctx a b c0)
    (c0 ∷ bool_precise_ty false).
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold div_wand_false_ctx, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = c0) by set_solver. subst z.
    unfold div_wand_false_ctx. intro_erase.
    etransitivity; [apply map_lookup_insert| symmetry; apply map_lookup_insert].
  - intros r Hr. unfold div_wand_false_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c0 (bool_precise_ty false)) = ∅)
      by (apply intro_closed_fv; intro_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

Lemma div_guard_program_wand_obl_true_guard (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ {[c0]} (div_wand_true_ctx a b c0)
    (c0 ∷ bool_precise_ty true).
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold div_wand_true_ctx, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - unfold wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = c0) by set_solver. subst z.
    unfold div_wand_true_ctx. intro_erase.
    etransitivity; [apply map_lookup_insert| symmetry; apply map_lookup_insert].
  - intros r Hr. unfold div_wand_true_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c0 (bool_precise_ty true)) = ∅)
      by (apply intro_closed_fv; intro_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

Lemma div_guard_program_wand_obl_proj_x (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ctx_sub_under ∅ {[a]} (div_wand_true_ctx a b c0) (a ∷ pos_under).
Proof.
  intros Hab Hac Hbc.
  apply intro_ctx_sub_by_entails.
  - unfold div_wand_true_ctx, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - unfold pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = a) by set_solver. subst z.
    unfold div_wand_true_ctx. intro_erase.
    etransitivity; [apply map_lookup_insert_ne; congruence| ].
    etransitivity; [apply map_lookup_insert_ne; congruence| ].
    reflexivity.
  - intros r Hr. unfold div_wand_true_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _].
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _].
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    setoid_rewrite storeA_restrict_empty in Hr.
    setoid_rewrite storeA_restrict_empty.
    exact Hr.
Qed.

Lemma div_guard_program_wand_false_part (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ∅; div_wand_false_ctx a b c0 ⊢ₓ
    (if (avar c0) then ret (avar a) else (a ⟨ - ⟩ b)) ⋮ pos_under.
Proof.
  intros Hab Hac Hbc.
  eapply EXT_MatchFalseOnly.
  - unfold div_wand_false_ctx, pos_under, q_pos. intro_wf.
  - eapply (intro_ext_ctx_sub _ _ (c0 ∷ bool_precise_ty false) ({[c0]} : aset)).
    + unfold div_wand_false_ctx, pos_under, q_pos. intro_wf.
    + eapply EXT_Var. intro_wf.
    + intro_dom_sub.
    + apply div_guard_program_wand_obl_false_guard; assumption.
  - eapply EXT_Sub.
    + unfold div_wand_false_ctx, pos_under, q_pos. intro_wf.
    + eapply EXT_BinOp. unfold div_wand_false_ctx, pos_under, q_pos. intro_wf.
    + apply div_guard_program_wand_obl_false_reach; assumption.
Qed.

Lemma div_guard_program_wand_body (a b c0 : atom) :
  a <> b -> a <> c0 -> b <> c0 ->
  ∅; div_wand_ctx a b c0 ⊢ₓ
    (if (avar c0) then ret (avar a) else (a ⟨ - ⟩ b)) ⋮ pos_under.
Proof.
  intros Hab Hac Hbc.
  eapply (intro_ext_ctx_case _ _ (div_wand_false_ctx a b c0)
    (div_wand_true_ctx a b c0 ⊕ div_wand_false_ctx a b c0)
    ({[a]} ∪ {[b]} ∪ {[c0]} : aset)).
  - unfold div_wand_ctx, pos_under, q_pos. intro_wf.
  - apply div_guard_program_wand_false_part; assumption.
  - eapply (EXT_Sub _ _ _ (pos_under ⊕ pos_under)).
    + unfold div_wand_true_ctx, div_wand_false_ctx, pos_under, q_pos. intro_wf.
    + eapply EXT_MatchBoth.
      * unfold div_wand_true_ctx, div_wand_false_ctx, pos_under, q_pos. intro_wf.
      * eapply (intro_ext_ctx_sub _ _ (c0 ∷ bool_precise_ty true) ({[c0]} : aset)).
        -- unfold div_wand_true_ctx, pos_under, q_pos. intro_wf.
        -- eapply EXT_Var. intro_wf.
        -- intro_dom_sub.
        -- apply div_guard_program_wand_obl_true_guard; assumption.
      * eapply (intro_ext_ctx_sub _ _ (c0 ∷ bool_precise_ty false) ({[c0]} : aset)).
        -- unfold div_wand_false_ctx, pos_under, q_pos. intro_wf.
        -- eapply EXT_Var. intro_wf.
        -- intro_dom_sub.
        -- apply div_guard_program_wand_obl_false_guard; assumption.
      * eapply (intro_ext_ctx_sub _ _ (a ∷ pos_under) ({[a]} : aset)).
        -- unfold div_wand_true_ctx, pos_under, q_pos. intro_wf.
        -- eapply EXT_Var. unfold pos_under, q_pos. intro_wf.
        -- intro_dom_sub.
        -- apply div_guard_program_wand_obl_proj_x; assumption.
      * eapply EXT_Sub.
        -- unfold div_wand_false_ctx, pos_under, q_pos. intro_wf.
        -- eapply EXT_BinOp. unfold div_wand_false_ctx, pos_under, q_pos. intro_wf.
        -- apply div_guard_program_wand_obl_false_reach; assumption.
    + apply div_guard_program_wand_obl_sum; assumption.
  - unfold div_wand_false_ctx. intro_dom_sub.
  - apply div_guard_program_wand_obl_case; assumption.
Qed.

Theorem div_guard_program_tau_b_wand :
  ∅; Emp ⊢ₓ div_guard_program ⋮ intro_tau_b_wand.
Proof.
  unfold div_guard_program, intro_tau_b_wand, lam_named, let_named.
  intro_compute_close.
  eapply (EXT_Lam _ _ pos_under) with (L := ({[x]} ∪ {[y]} ∪ {[c]} : aset)).
  - unfold pos_under, q_pos. intro_wf.
  - intros x' Hx'. cbn [cty_open open_one open_cty_atom_inst].
    rewrite !intro_pos_under_closed_open.
    intro_norm_open.
    eapply (EXT_LamD _ _ pos_under)
      with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} : aset)).
    + unfold pos_under, q_pos. intro_wf.
    + intros y' Hy'. rewrite intro_pos_under_closed_open. intro_norm_open.
      eapply (EXT_Let _ _ (binop_precise_ty bop_le (vfvar y') (vconst (cnat 0))))
        with (L := ({[x]} ∪ {[y]} ∪ {[c]} ∪ {[x']} ∪ {[y']} : aset)).
      * unfold pos_under, q_pos. intro_wf.
      * eapply EXT_BinOp. unfold pos_under, q_pos. intro_wf.
      * intros c' Hc'. intro_norm_open.
        assert (Hxy : x' <> y') by intro_clear_neq.
        assert (Hxc : x' <> c') by intro_clear_neq.
        assert (Hyc : y' <> c') by intro_clear_neq.
        change (((Emp ,, (x' ∷ pos_under)) ∗ (y' ∷ pos_under)) ,,
                  (c' ∷ binop_precise_ty bop_le (vfvar y') (vconst (cnat 0))))
          with (div_wand_ctx x' y' c').
        change (tmatch (vfvar c') (tret (vfvar x'))
                  (tbinop bop_minus (vfvar x') (vfvar y')))
          with (if (avar c') then ret (avar x') else (x' ⟨ - ⟩ y')).
        apply div_guard_program_wand_body; assumption.
Qed.

(** ** The captured closure [λy. x - y] (paper p.2 l.88)

    Under [x:[ν>0]] the closure has the independent type
    [y:[ν>0] -∗ [ν>0]] (this is [(−) x] for the paper's
    [(−) : x:[ν>0] → y:[ν>0] -∗ [ν>0]], p.7 l.329).

    It does NOT have the entangled type [y:[ν>0] → [ν>0]]: the arrow
    quantifies over all extensions of the context capability with a [y]
    satisfying [[ν>0]], including the entangled one
    [{[x↦n, y↦n] | n > 0}], on which [x - y] is constantly [0] (paper p.6,
    [C_en]). *)

Definition captured_minus_ctx : ctx := x ∷ pos_under.

(** Obligation:  x:[ν>0] ∗ y:[ν>0] ⊢ {ν = x - y} ⊓ [ν = x - y] <: [ν>0].
    Same argument as [nat_sub_program_obl_tau_b_result]: the product contains
    [x ↦ n+1, y ↦ 1] for every [n > 0]. *)
Lemma captured_minus_fun_obl_reach :
  sub_type_under ∅ ((x ∷ pos_under) ∗ (y ∷ pos_under))
    (binop_precise_ty bop_minus (vfvar x) (vfvar y)) pos_under.
Proof.
Admitted.

Theorem captured_minus_fun_wand_type :
  ∅; captured_minus_ctx ⊢ₓ captured_minus_fun ⋮ (pos_under -∗ pos_under).
Proof.
  unfold captured_minus_fun, captured_minus_ctx.
  eapply EXT_LamDNamedErased.
  - reflexivity.
  - unfold pos_under, q_pos. intro_wf.
  - eapply EXT_Sub.
    + unfold pos_under, q_pos. intro_wf.
    + eapply EXT_BinOp. unfold pos_under, q_pos. intro_wf.
    + exact captured_minus_fun_obl_reach.
Qed.

(** ** Higher-order application [λf. f x] (paper p.2 l.82-99, p.8)

    ✗ (paper p.2 l.82):  x:[ν>0] ⊢ λf. f x : f:(y:[ν>0] → [ν>0]) → [ν>0].
    Not typed (paper ✗).  The paper's counterexample instantiates [f] with the
    captured closure [λy. x - y], for which [f x = 0]
    ([static_alias_counterexample]).

    FINDING (the informal fix on p.2 l.95-99 is insufficient).  Making only
    [f]'s parameter independent,
      x:[ν>0] ⊢ λf. f x : f:(y:[ν>0] -∗ [ν>0]) → [ν>0],
    is still invalid: [λy. x - y] HAS type [y:[ν>0] -∗ [ν>0]] under
    [x:[ν>0]] ([captured_minus_fun_wand_type]), and [f x = 0].  What is
    needed is that [f] be independent of the closure context, i.e. the OUTER
    arrow must be [-∗] (the p.8 fix).  Both versions of the p.8 fix are
    derivable below. *)

Definition ho_entangled_f_ty : context_ty := pos_under → pos_under.
Definition ho_wand_f_ty : context_ty := pos_under -∗ pos_under.

(** x:[ν>0] ⊢ λf. f x : f:(y:[ν>0] → [ν>0]) -∗ [ν>0]   (p.8 style) *)
Definition higher_order_apply_x_fixed_ty : context_ty :=
  ho_entangled_f_ty -∗ pos_under.

(** x:[ν>0] ⊢ λf. f x : f:(y:[ν>0] -∗ [ν>0]) -∗ [ν>0] *)
Definition higher_order_apply_x_fixed_wand_ty : context_ty :=
  ho_wand_f_ty -∗ pos_under.

(** Obligations (projections of an independent context).  Informal
    argument: [⟦Γ1 ∗ Γ2⟧] holds at [r] iff [r] restricted to
    [dom Γ1 ∪ dom Γ2] is a product [r1 × r2] with [r1 ⊨ ⟦Γ1⟧],
    [r2 ⊨ ⟦Γ2⟧]; projecting a product on [dom Γi] yields [ri] (worlds are
    non-empty), so [r|dom Γi = ri ⊨ ⟦Γi⟧]. *)
Lemma higher_order_apply_x_obl_proj_f :
  ctx_sub_under ∅ ({[f]} : aset) ((x ∷ pos_under) ∗ (f ∷ ho_entangled_f_ty))
    (f ∷ ho_entangled_f_ty).
Proof.
  apply intro_ctx_sub_by_entails.
  - unfold ho_entangled_f_ty, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - unfold ho_entangled_f_ty, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = f) by set_solver. subst z. vm_compute. reflexivity.
  - intros r Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_star_iff in Hr as [m1 [m2 [Hc [Hle [Hm1 Hm2]]]]].
    assert (Hr' : res_models r (ctx_denote_under (store_restrict ∅ (ctx_fv ((x ∷ pos_under) ∗ (f ∷ ho_entangled_f_ty)))) (f ∷ ho_entangled_f_ty))).
    { eapply res_models_kripke; [ |exact Hm2].
      etransitivity; [apply res_product_le_r|exact Hle]. }
    cbn [ctx_denote_under] in Hr'.
    intro_close_by_env_compute Hr'.
Qed.

Lemma higher_order_apply_x_obl_proj_x :
  ctx_sub_under ∅ ({[x]} : aset) ((x ∷ pos_under) ∗ (f ∷ ho_entangled_f_ty))
    (x ∷ pos_under).
Proof.
  apply intro_ctx_sub_by_entails.
  - unfold ho_entangled_f_ty, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - unfold ho_entangled_f_ty, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - intros z Hz. assert (z = x) by set_solver. subst z. vm_compute. reflexivity.
  - intros r Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_star_iff in Hr as [m1 [m2 [Hc [Hle [Hm1 Hm2]]]]].
    assert (Hr' : res_models r (ctx_denote_under (store_restrict ∅ (ctx_fv ((x ∷ pos_under) ∗ (f ∷ ho_entangled_f_ty)))) (x ∷ pos_under))).
    { eapply res_models_kripke; [ |exact Hm1].
      etransitivity; [apply res_product_le_l|exact Hle]. }
    cbn [ctx_denote_under] in Hr'.
    intro_close_by_env_compute Hr'.
Qed.

(** Obligation (exchange, paper Example 3.2 T-Exchange): [∗] is
    commutative because the capability product is. *)
Lemma higher_order_apply_x_obl_exchange :
  ctx_sub_under ∅ ({[f]} ∪ {[x]} : aset) ((x ∷ pos_under) ∗ (f ∷ ho_wand_f_ty))
    ((f ∷ ho_wand_f_ty) ∗ (x ∷ pos_under)).
Proof.
  apply intro_ctx_sub_by_entails.
  - unfold ho_wand_f_ty, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - unfold ho_wand_f_ty, pos_under, q_pos, wf_ctx_under. intro_wf_goals.
  - intros z Hz. vm_compute. set_unfold in Hz. destruct Hz as [-> | ->]; reflexivity.
  - intros r Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [Hbasic Hr].
    apply res_models_and_iff. split.
    + match type of Hbasic with res_models _ (basic_world_formula ?E1) =>
      match goal with |- res_models _ (basic_world_formula ?E2) =>
        replace E1 with E2 in Hbasic by (vm_compute; reflexivity) end end.
      exact Hbasic.
    + apply res_models_star_iff in Hr as [m1 [m2 [Hc [Hle [Hm1 Hm2]]]]].
      destruct (res_product_comm_eq m1 m2 Hc) as [Hc' Heq].
      eapply (res_models_star_intro r m2 m1); [rewrite <- Heq; exact Hle| | ].
      * cbn [ctx_denote_under] in Hm2. intro_close_by_env_compute Hm2.
      * cbn [ctx_denote_under] in Hm1. intro_close_by_env_compute Hm1.
Qed.

Theorem higher_order_apply_x_fixed :
  ∅; captured_minus_ctx ⊢ₓ higher_order_apply_x ⋮ higher_order_apply_x_fixed_ty.
Proof.
  unfold higher_order_apply_x, higher_order_apply_x_fixed_ty, captured_minus_ctx.
  eapply EXT_LamDNamedErased.
  - reflexivity.
  - unfold ho_entangled_f_ty, pos_under, q_pos. intro_wf.
  - enough (H : ∅; (x ∷ pos_under) ∗ (f ∷ ho_entangled_f_ty) ⊢ₓ
                 f @ x ⋮ cty_open 0 x pos_under)
      by (rewrite intro_pos_under_closed_open in H; exact H).
    eapply (EXT_AppFun _ _ pos_under pos_under (vfvar f) x).
    + rewrite intro_pos_under_closed_open.
      unfold ho_entangled_f_ty, pos_under, q_pos. intro_wf.
    + rewrite intro_pos_under_fv. unfold x, f. cbn. clear. set_solver.
    + eapply (intro_ext_ctx_sub _ _ (f ∷ ho_entangled_f_ty) ({[f]} : aset)).
      * unfold ho_entangled_f_ty, pos_under, q_pos. intro_wf.
      * eapply EXT_Var. unfold ho_entangled_f_ty, pos_under, q_pos. intro_wf.
      * intro_dom_sub.
      * exact higher_order_apply_x_obl_proj_f.
    + eapply (intro_ext_ctx_sub _ _ (x ∷ pos_under) ({[x]} : aset)).
      * unfold ho_entangled_f_ty, pos_under, q_pos. intro_wf.
      * eapply EXT_Var. unfold pos_under, q_pos. intro_wf.
      * intro_dom_sub.
      * exact higher_order_apply_x_obl_proj_x.
Qed.

Theorem higher_order_apply_x_fixed_wand :
  ∅; captured_minus_ctx ⊢ₓ higher_order_apply_x ⋮ higher_order_apply_x_fixed_wand_ty.
Proof.
  unfold higher_order_apply_x, higher_order_apply_x_fixed_wand_ty, captured_minus_ctx.
  eapply EXT_LamDNamedErased.
  - reflexivity.
  - unfold ho_wand_f_ty, pos_under, q_pos. intro_wf.
  - enough (H : ∅; (x ∷ pos_under) ∗ (f ∷ ho_wand_f_ty) ⊢ₓ
                 f @ x ⋮ cty_open 0 x pos_under)
      by (rewrite intro_pos_under_closed_open in H; exact H).
    eapply (intro_ext_ctx_sub _ _ ((f ∷ ho_wand_f_ty) ∗ (x ∷ pos_under))
      ({[f]} ∪ {[x]} : aset)).
    + rewrite intro_pos_under_closed_open.
      unfold ho_wand_f_ty, pos_under, q_pos. intro_wf.
    + eapply (EXT_AppFunD _ _ _ pos_under pos_under (vfvar f) x).
      * rewrite intro_pos_under_closed_open.
        unfold ho_wand_f_ty, pos_under, q_pos. intro_wf.
      * rewrite intro_pos_under_fv. unfold x, f. cbn. clear. set_solver.
      * eapply EXT_Var. unfold ho_wand_f_ty, pos_under, q_pos. intro_wf.
      * eapply EXT_Var. unfold pos_under, q_pos. intro_wf.
    + intro_dom_sub.
    + exact higher_order_apply_x_obl_exchange.
Qed.

(** ** Counterexample programs (✗ in the paper; documented, not typed)

    [static_alias_counterexample] = [let x = gen in (λf. f x) (λy. x - y)]
    (p.2 l.90).  It always evaluates to [0], so it does not have the paper's
    intended reachability type [[ν > 0]].  Independently of semantics, it is
    not in the A-normal form accepted by T-AppFun (the argument of the
    application is a lambda, not a variable).  The derivable fix is
    [higher_order_apply_x_fixed]: with the outer [-∗], [λy. x - y] can no
    longer be passed for [f] in a context where [x] is the argument, because
    the closure of [f] would have to be independent of [x].

    [dynamic_dependency_counterexample] =
    [let x = gen in let y = gen in (λf. f (f y)) f2] with
    [f2 = λy. if y = 1 then x else 2] (p.3 l.106-118, judgment
    [y:[ν>0] ⊢ λf. f (f y) : f:(y:[ν>0] → [ν>0]) → [ν>0]] ✗).  The program
    reaches only [{1, 2}] together with the value of [x] chosen for the
    unique environment where [y = 1] is used, so it cannot reach every
    positive number.  Not typed (paper ✗).  We did not formalize the
    semantic refutation of the ✗ judgments themselves (that would need
    soundness of the extended judgment, which is not available); note that
    under the Rocq denotation the entangled arrow quantifies over argument
    extensions that may be correlated with the context, so the precise
    counter-model for the [→]-typed judgments is more delicate than the
    paper's informal explanation.  The p.8 fix of this example
    ([x ∗ y ⊢ λf. x - f (f y) : f:(y:[ν>0] → [ν>0]) -∗ [ν>0]]) is
    [Section2Typing.nested_apply_program] (not in this file's assignment). *)


End Section1IntroExamples.
