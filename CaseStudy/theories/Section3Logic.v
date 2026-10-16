(** * Small program witnesses for Section 3 (logic and denotation) *)

(** Generic subsumption lemmas ([subtype_over_closed_by_qualifier],
    [subtype_under_closed_by_qualifier_corrected],
    [extended_semantic_subtype_trans], [extended_semantic_subtype_inter_right])
    are taken from the shared, fully proved [ProofAutomation.ExtendedSubsumption].
    (Round 1 kept local verbatim copies; they are no longer needed.) *)


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

    - [logic_qual_open_lq_nat2] / [logic_qual_open_q_nat_pred]: opening a
      value-based qualifier replaces the opened de Bruijn value by the atom.
      Needed whenever a dependent arrow result (e.g. [ν ≤ x]) is opened by
      [EXT_Lam].
    - [logic_ctx_sub_under_mono], [logic_ext_ctx_sub]: [T-CtxSub] stated
      with the variable set [dom ⌊Γ2⌋] (any obligation proved for a superset of
      [fv e ∪ fv τ] suffices).
    - tactics [logic_wf] / [logic_basic]: well-formedness and basic typing for
      opened (locally nameless) terms whose free atoms are abstract cofinite
      atoms; the shared [extended_wf] only handles concrete atoms. *)

Definition logic_atomic_value (v : value) : Prop :=
  match v with vbvar _ | vfvar _ | vconst _ => True | _ => False end.

Lemma logic_atomic_open_keys k a v :
  logic_atomic_value v -> a ∉ fv_value v ->
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

Lemma logic_atomic_open_denote k a (s : LStore (V := value)) v :
  logic_atomic_value v -> a ∉ fv_value v ->
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
Definition lq_nat2 (v1 v2 : value) (R : nat -> nat -> Prop) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ => exists n m,
       denote_lvar_value (lso_store σ) v1 = Some (vconst (cnat n)) /\
       denote_lvar_value (lso_store σ) v2 = Some (vconst (cnat m)) /\ R n m).

Lemma logic_qual_open_lq_nat2 k a v1 v2 R :
  logic_atomic_value v1 -> logic_atomic_value v2 ->
  a ∉ fv_value v1 -> a ∉ fv_value v2 ->
  qual_open_atom k a (lq_nat2 v1 v2 R) =
  lq_nat2 (open_value k (vfvar a) v1) (open_value k (vfvar a) v2) R.
Proof.
  intros H1 H2 Ha1 Ha2.
  unfold lq_nat2. apply qual_ext; cbn [qual_open_atom qual_lvars qual_prop].
  - unfold set_swap. rewrite set_map_union_L.
    rewrite <- !logic_atomic_open_keys by assumption. reflexivity.
  - intros s1 s2 Hs. cbn.
    rewrite !logic_atomic_open_denote by assumption. rewrite Hs. reflexivity.
Qed.

Lemma logic_qual_open_q_nat_pred k a v P :
  logic_atomic_value v -> a ∉ fv_value v ->
  qual_open_atom k a (q_nat_pred v P) = q_nat_pred (open_value k (vfvar a) v) P.
Proof.
  intros H1 Ha1.
  unfold q_nat_pred, q_const_pred.
  apply qual_ext; cbn [qual_open_atom qual_lvars qual_prop].
  - rewrite <- !logic_atomic_open_keys by assumption. reflexivity.
  - intros s1 s2 Hs. cbn.
    rewrite !logic_atomic_open_denote by assumption. rewrite Hs. reflexivity.
Qed.

Lemma logic_cty_open_over k a b q :
  cty_open k a (over_ty b q) = over_ty b (qual_open_atom (S k) a q).
Proof. reflexivity. Qed.

Lemma logic_cty_open_under k a b q :
  cty_open k a (under_ty b q) = under_ty b (qual_open_atom (S k) a q).
Proof. reflexivity. Qed.

Lemma logic_dom_erase_ctx_comma Γ1 Γ2 :
  dom (erase_ctx (CtxComma Γ1 Γ2)) = dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2).
Proof. cbn [erase_ctx]. apply dom_union_L. Qed.

Lemma logic_dom_erase_ctx_star Γ1 Γ2 :
  dom (erase_ctx (CtxStar Γ1 Γ2)) = dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2).
Proof. cbn [erase_ctx]. apply dom_union_L. Qed.

Lemma logic_dom_erase_ctx_sum Γ1 Γ2 :
  dom (erase_ctx (CtxSum Γ1 Γ2)) = dom (erase_ctx Γ1).
Proof. reflexivity. Qed.

Lemma logic_dom_erase_ctx_empty : dom (erase_ctx CtxEmpty) = (∅ : aset).
Proof. cbn [erase_ctx]. apply dom_empty_L. Qed.

(** [T-CtxSub] only needs the refinement on [fv e ∪ fv τ]; a refinement on a
    larger variable set is stronger. *)
Lemma logic_ctx_sub_under_mono Σ (X Y : aset) Γ1 Γ2 :
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

Lemma logic_ext_ctx_sub Σ Γ1 Γ2 (X : aset) e τ :
  Σ; Γ1 ⊢wf e ⋮ τ ->
  Σ; Γ2 ⊢ₓ e ⋮ τ ->
  dom (erase_ctx Γ2) ⊆ X ->
  ctx_sub_under Σ X Γ1 Γ2 ->
  Σ; Γ1 ⊢ₓ e ⋮ τ.
Proof.
  intros Hwf Hty HX Hsub.
  eapply EXT_CtxSub; [exact Hwf|exact Hty| ].
  eapply logic_ctx_sub_under_mono; [ |exact Hsub].
  pose proof (extended_typing_wf_under Σ Γ2 e τ Hty) as Hwf2.
  pose proof (context_typing_wf_fv_tm_subset Σ Γ2 e τ Hwf2).
  pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γ2 e τ Hwf2).
  set_solver.
Qed.

(** [T-CtxCase] with a larger variable set (same pattern as
    [logic_ext_ctx_sub]). *)
Lemma logic_ctx_case_under_mono Σ (X Y : aset) Γ Γa Γb :
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

Lemma logic_ext_ctx_case Σ Γ Γa Γb (X : aset) e τ :
  Σ; Γ ⊢wf e ⋮ τ ->
  Σ; Γa ⊢ₓ e ⋮ τ ->
  Σ; Γb ⊢ₓ e ⋮ τ ->
  dom (erase_ctx Γa) ⊆ X ->
  ctx_case_under Σ X Γ Γa Γb ->
  Σ; Γ ⊢ₓ e ⋮ τ.
Proof.
  intros Hwf Ha Hb HX Hcase.
  eapply EXT_CtxCase; [exact Hwf|exact Ha|exact Hb| ].
  eapply logic_ctx_case_under_mono; [ |exact Hcase].
  pose proof (extended_typing_wf_under Σ Γa e τ Ha) as Hwfa.
  pose proof (context_typing_wf_fv_tm_subset Σ Γa e τ Hwfa).
  pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γa e τ Hwfa).
  set_solver.
Qed.

Ltac logic_compute_close :=
  repeat match goal with |- context[close_tm ?a ?k ?e] =>
    let r := eval vm_compute in (close_tm a k e) in
    change (close_tm a k e) with r end.

Ltac logic_norm_dec :=
  repeat (first [rewrite decide_True by reflexivity | rewrite decide_False by lia]).

Ltac logic_norm_open :=
  cbn [open_one open_tm_atom_inst open_cty_atom_inst open_tm open_value
       cty_open Ret];
  repeat rewrite logic_cty_open_over; repeat rewrite logic_cty_open_under;
  repeat rewrite logic_qual_open_lq_nat2
    by (unfold avar; cbn; first [exact I | set_solver]);
  repeat rewrite logic_qual_open_q_nat_pred
    by (unfold avar; cbn; first [exact I | set_solver]);
  unfold vnu;
  cbn [open_value];
  logic_norm_dec.

Ltac logic_set :=
  cbn [ctx_dom erase_ctx] in *;
  rewrite ?dom_empty_L, ?dom_union_L, ?dom_singleton_L;
  set_solver.

Ltac logic_norm_erase_dom :=
  repeat first [ rewrite logic_dom_erase_ctx_comma | rewrite logic_dom_erase_ctx_star
               | rewrite logic_dom_erase_ctx_sum | rewrite logic_dom_erase_ctx_empty
               | rewrite erase_ctx_bind_dom ].

Ltac logic_lvars_wf :=
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

Ltac logic_wf_type :=
  logic_norm_erase_dom;
  cbn [ctx_dom];
  unfold lq_nat2, q_nat_pred, q_const_pred, vnu, avar, vnat, vbool in *;
  unfold basic_context_ty, ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
    precise_const, const_precise_ty, precise_ty, over_ty, under_ty,
    q_true, q_false, bool_qual, bool_precise_ty, mk_q_eq, qual_top,
    binop_precise_ty, binop_result_qual, binop_top_ty in *;
  cbn [wf_context_ty_at erase_ty qual_vars qual_lvars lvar_value_keys
       bin_op_type base_ty_of_const] in *;
  repeat split; try reflexivity; logic_lvars_wf.

Ltac logic_wf_ctx :=
  unfold wf_ctx_under;
  repeat
    match goal with
    | |- basic_ctx _ CtxEmpty => apply basic_ctx_empty
    | |- basic_ctx _ (CtxBind _ _) =>
        apply basic_ctx_bind; [logic_set | logic_wf_type]
    | |- basic_ctx _ (CtxComma _ _) =>
        cbn [basic_ctx ctx_dom]; repeat split;
        try logic_wf_ctx; try logic_wf_type; try logic_set
    | |- basic_ctx _ (CtxStar _ _) =>
        apply basic_ctx_star; [logic_wf_ctx|logic_wf_ctx|logic_set]
    | |- basic_ctx _ (CtxSum _ _) =>
        apply basic_ctx_sum; [logic_wf_ctx|logic_wf_ctx|reflexivity|reflexivity]
    end.

Lemma logic_erase_ctx_sum Γ1 Γ2 : erase_ctx (CtxSum Γ1 Γ2) = erase_ctx Γ1.
Proof. reflexivity. Qed.

Lemma logic_erase_ctx_bind a τ :
  erase_ctx (CtxBind a τ) = <[a := erase_ty τ]> (∅ : gmap atom ty).
Proof. reflexivity. Qed.

Ltac logic_erase :=
  repeat first
    [ rewrite logic_erase_ctx_sum
    | rewrite erase_ctx_comma_bind_fresh by (logic_norm_erase_dom; logic_set)
    | rewrite erase_ctx_star_bind_fresh by (logic_norm_erase_dom; logic_set)
    | rewrite logic_erase_ctx_bind ];
  cbn [erase_ctx erase_ty over_ty under_ty] in *.

Ltac logic_clear_neq :=
  let Heq := fresh "Heq" in
  intros Heq;
  first [ solve [vm_compute in Heq; congruence] | subst ];
  repeat match goal with
         | H : ?a ∉ _ |- False => apply H; clear H; set_solver
         | H : ?a ∉ _ |- _ => rewrite ?dom_insert_L, ?dom_empty_L in H
         end.

Ltac logic_lookup :=
  first
    [ apply map_lookup_insert
    | match goal with
      | |- <[?y := ?Ty]> ?Γ !! ?x = Some ?T =>
          transitivity (Γ !! x);
          [ apply map_lookup_insert_ne; logic_clear_neq
          | logic_lookup ]
      end ].

Ltac logic_keys_of m :=
  lazymatch m with
  | <[?k := _]> ?m' => let s := logic_keys_of m' in constr:(({[k]} : aset) ∪ s)
  | _ => constr:(∅ : aset)
  end.

Ltac logic_basic :=
  unfold Ret, avar, vnat, vbool, if_named, case_app in *;
  lazymatch goal with
  | |- _ ⊢ₑ tret _ ⋮ _ => apply TT_Ret; logic_basic
  | |- _ ⊢ₑ tbinop _ _ _ ⋮ _ =>
      eapply TT_BinOp; [basic_solve_binop_type | logic_basic | logic_basic]
  | |- _ ⊢ₑ tprim _ _ ⋮ _ => eapply TT_Op; [reflexivity | logic_basic]
  | |- _ ⊢ₑ tapp _ _ ⋮ _ => eapply TT_App; [logic_basic | logic_basic]
  | |- _ ⊢ₑ tmatch _ _ _ ⋮ _ =>
      eapply TT_Match; [logic_basic | logic_basic | logic_basic]
  | |- ?Γ ⊢ₑ tlete _ _ ⋮ _ =>
      let L := logic_keys_of Γ in
      eapply (TT_Let _ _ _ _ _ L);
      [ logic_basic
      | let z := fresh "z" in let Hz := fresh "Hz" in
        intros z Hz;
        cbn [open_one open_tm_atom_inst open_value_atom_inst open_tm open_value]; logic_norm_dec; logic_basic ]
  | |- _ ⊢ᵥ vconst _ ⋮ _ => constructor
  | |- _ ⊢ᵥ vfvar _ ⋮ _ => apply VT_FVar; logic_lookup
  | |- ?Γ ⊢ᵥ vlam _ _ ⋮ _ =>
      let L := logic_keys_of Γ in
      eapply (VT_Lam _ _ _ _ L);
      let z := fresh "z" in let Hz := fresh "Hz" in
      intros z Hz;
      cbn [open_one open_tm_atom_inst open_value_atom_inst open_tm open_value]; logic_norm_dec; logic_basic
  end.

Ltac logic_basic_top :=
  unfold ONat, UNat, OBool, UBool, OTree, UTree, OList, UList, qual_top in *;
  logic_erase;
  unfold binop_precise_ty, binop_top_ty, primop_precise_ty, const_precise_ty,
    precise_ty, bool_precise_ty, over_ty, under_ty in *;
  cbn [erase_ty bin_op_type base_ty_of_const] in *;
  unfold lam_named, let_named in *; logic_compute_close;
  logic_basic.

Ltac logic_wf :=
  unfold context_typing_wf;
  repeat split;
  lazymatch goal with
  | |- wf_ctx_under _ _ => logic_wf_ctx
  | |- basic_ctx _ _ => logic_wf_ctx
  | |- wf_context_ty_at _ _ _ => logic_wf_type
  | |- basic_context_ty _ _ => logic_wf_type
  | |- _ ∉ _ => logic_set
  | |- _ ## _ => logic_set
  | |- _ ⊆ _ => logic_set
  | |- _ ∈ _ => logic_set
  | |- _ ⊢ₑ _ ⋮ _ =>
      first [ logic_basic_top
            | unfold ONat, UNat, qual_top in *; logic_erase;
              unfold over_ty, under_ty in *; cbn [erase_ty] in *; basic_check
            | extended_basic_check ]
  | |- _ = _ => reflexivity
  end.

(** [ctx_sub] target-domain side goal of [logic_ext_ctx_sub]. *)
Ltac logic_dom_sub := logic_norm_erase_dom; clear; set_solver.

(** ** Helpers for structural [T-CtxSub] obligations

    A context refinement whose target denotation is entailed by the source
    denotation holds with the identity capability ([r' = r]). *)
Local Notation ctx_denote_under := Denotation.Context.ctx_denote_under.
Local Notation ty_denote := Denotation.TypeDenote.ty_denote.

Lemma logic_ctx_sub_by_entails Σ (X : aset) Γ1 Γ2 :
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

Lemma logic_closed_fv τ : wf_context_ty_at 0 ∅ τ -> fv_cty τ = ∅.
Proof.
  intros Hwf. pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hwf). set_solver.
Qed.

Ltac logic_wf_goals :=
  repeat split;
  lazymatch goal with
  | |- wf_ctx_under _ _ => logic_wf_ctx
  | |- basic_ctx _ _ => logic_wf_ctx
  | |- wf_context_ty_at _ _ _ => logic_wf_type
  | |- basic_context_ty _ _ => logic_wf_type
  | |- _ ∉ _ => logic_set
  | |- _ ## _ => logic_set
  | |- _ ⊆ _ => logic_set
  | |- _ ∈ _ => logic_set
  | |- _ = _ => reflexivity
  end.

(** Close [H : r ⊨ ⟦x:τ⟧_{Σ1}] against the goal [r ⊨ ⟦x:τ⟧_{Σ2}] when the
    two (concrete) environments compute to the same map. *)
Ltac logic_close_by_env_compute H :=
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


Section Section3LogicExamples.

Definition x : atom := 301%positive.
Definition y : atom := 302%positive.
Definition p : atom := 303%positive.
Definition q : atom := 304%positive.
Definition c : atom := 305%positive.

Definition logic_project_x : tm :=
  ret x.

Definition logic_correlated_xy : tm :=
  let y := x ⟨ + ⟩ vnat 1 in
  x ⟨ + ⟩ y.

Definition logic_branch_atom_example : tm :=
  let c := x ⟨ ≤ ⟩ vnat 2 in
  if c then
    ret x
  else
    y ⟨ + ⟩ vnat 1.

Definition logic_product_style_example : tm :=
  x ⟨ + ⟩ y.

Definition logic_implication_witness : tm :=
  ret (ƛ x : ℕ => x ⟨ + ⟩ vnat 1).

Definition nat_increment_ty : ty := (ℕ : ty) →ᵦ ℕ.

Lemma logic_project_x_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ logic_project_x ⋮ ℕ.
Proof. unfold logic_project_x. basic_check. Qed.

Lemma logic_project_x_extended_type :
  ∅; x ∷ ONat ⊢ₓ logic_project_x ⋮ ONat.
Proof.
  unfold logic_project_x.
  eapply EXT_Var.
  extended_wf.
Qed.

Lemma logic_correlated_xy_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ logic_correlated_xy ⋮ ℕ.
Proof. unfold logic_correlated_xy. basic_check. Qed.

Lemma logic_branch_atom_example_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ logic_branch_atom_example ⋮ ℕ.
Proof. unfold logic_branch_atom_example. basic_check. Qed.

Lemma logic_product_style_example_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ logic_product_style_example ⋮ ℕ.
Proof. unfold logic_product_style_example. basic_check. Qed.

Lemma logic_product_style_example_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    logic_product_style_example ⋮ binop_precise_ty bop_plus (avar x) (avar y).
Proof.
  unfold logic_product_style_example.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma logic_implication_witness_basic_type :
  ∅ ⊢ₑ logic_implication_witness ⋮ nat_increment_ty.
Proof. unfold logic_implication_witness, nat_increment_ty. basic_check. Qed.

(** * Context-type derivations for the Section 4 (logic) examples

    The paper's Section 4 examples are stated about capabilities; we type the
    small witness programs above against the corresponding context types:

    - Example 4.5: [r_x = {[x↦1], [x↦2]}] satisfies [O Atom(0 ≤ x ≤ 4)] and
      [U Atom(x = 1)], but not [O Atom(x = 1)] nor [U Atom(0 ≤ x ≤ 4)].
      Typing counterparts: [x:{1≤ν≤2} ⊢ x : {0≤ν≤4}] ✓,
      [x:[1≤ν≤2] ⊢ x : [ν=1]] ✓, [x:{1≤ν≤2} ⊢ x : {ν=1}] ✗,
      [x:[1≤ν≤2] ⊢ x : [0≤ν≤4]] ✗.
    - Product vs entangled (p.16): [r_x × r_y ⊨ U(1≤x≤2) ∗ U(3≤y≤4)] but
      [r_xy = {[x↦1,y↦3],[x↦2,y↦4]}] only satisfies the [∧] version.
      Typing counterparts: [x:[1≤ν≤2] ∗ y:[3≤ν≤4] ⊢ x + y : [4≤ν≤6]] ✓ and
      [x:[1≤ν≤2], y:[3≤ν≤4] ⊢ x + y : [4≤ν≤6]] ✗ ([r_xy] only reaches 4, 6).
    - Example 4.6: [x:[1≤ν≤2], y:[0≤ν<x]], denoted
      [U(1≤x≤2) ∧ x▷U(0≤y<x)]; every capability contains [(1,0)], [(2,0)],
      [(2,1)].  Typing counterparts: [⊢ x + y : [1≤ν≤3]] ✓ and the
      projection [⊢ x : [1≤ν≤2]] ✓.

    Qualifier translation: integer ranges become [ℕ] ranges
    ([q_nat_pred ν (fun n => lo <= n <= hi)]); [0 ≤ ν < x] is the binary
    qualifier [lq_nat2 ν x (fun v n => v < n)]. *)

Definition q_range (lo hi : nat) : type_qualifier :=
  q_nat_pred ν (fun n => lo <= n <= hi).

Definition q_eq_nat (k : nat) : type_qualifier :=
  q_nat_pred ν (fun n => n = k).

Definition x12_over : context_ty := {: ℕ | q_range 1 2 }.
Definition x12_under : context_ty := [: ℕ | q_range 1 2 ].
Definition x12_precise : context_ty := x12_over ⊓ x12_under.

(** [y:[0 ≤ ν < x]] (Example 4.6). *)
Definition y_below_x : context_ty := [: ℕ | lq_nat2 ν (vfvar x) (fun v n => v < n) ].
(** [y:[3 ≤ ν ≤ 4]] (product example, p.16). *)
Definition y34_under : context_ty := [: ℕ | q_range 3 4 ].

(** Example 4.6 entangled context and the independent (product) context. *)
Definition ex46_ctx : ctx := (x ∷ x12_under) ,, (y ∷ y_below_x).
Definition product_ctx : ctx := (x ∷ x12_under) ∗ (y ∷ y34_under).

(** ** Small proved facts used to discharge closed-qualifier obligations *)

Lemma logic_qual_dom_nu_pred P : qual_dom (q_nat_pred ν P) = ∅.
Proof.
  unfold qual_dom, q_nat_pred, q_const_pred, vnu. cbn [qual_lvars lvar_value_keys].
  apply set_eq. intros a. split; [ |set_solver]. intros Ha.
  apply lvars_fv_elem in Ha. set_solver.
Qed.

Lemma logic_nu_pred_entails P Q :
  (forall n, P n -> Q n) ->
  qualifier_entails (q_nat_pred ν P) (q_nat_pred ν Q).
Proof.
  intros HPQ [st Hst] [c0 [Hc HP]].
  exists c0. split; [exact Hc| ].
  destruct c0; try contradiction. apply HPQ. exact HP.
Qed.

(** Premises of [subtype_under_closed_by_qualifier_corrected]
    for [ν]-only natural-number predicates. *)
Lemma logic_nu_pred_vars_sub P Q :
  qual_vars (q_nat_pred ν P) ⊆ qual_vars (q_nat_pred ν Q).
Proof. reflexivity. Qed.

Lemma logic_nu_pred_sat P (k : nat) :
  P k -> exists s, qual_prop (q_nat_pred ν P) s.
Proof.
  intros Hk.
  unshelve eexists.
  - refine {| storeAO_store :=
      ({[LVBound 0 := vconst (cnat k)]} : gmap logic_var value) |}.
    unfold q_nat_pred, q_const_pred, vnu. cbn [qual_lvars lvar_value_keys].
    apply dom_singleton_L.
  - exists (cnat k). split; [ |exact Hk].
    unfold denote_lvar_value, vnu, lso_store, storeAO_store. cbn. rewrite lookup_singleton. case_decide; congruence.
Qed.

Ltac logic_subtype_wf :=
  unfold subtype_wf; repeat split;
  lazymatch goal with
  | |- wf_ctx_under _ _ => logic_wf_ctx
  | |- basic_ctx _ _ => logic_wf_ctx
  | |- wf_context_ty_at _ _ _ => logic_wf_type
  | |- basic_context_ty _ _ => logic_wf_type
  | |- _ ∉ _ => logic_set
  | |- _ ## _ => logic_set
  | |- _ = _ => reflexivity
  end.

(** ** [logic_project_x = x] *)

(** Example 4.5, demonic: [r_x ⊨ O Atom(0 ≤ x ≤ 4)].  Proved from the
    generic closed-qualifier lemma [subtype_over_closed_by_qualifier] (shared, proved). *)
Lemma logic_project_x_obl_over_weaken :
  sub_type_under ∅ (x ∷ x12_over) x12_over ({: ℕ | q_range 0 4 }).
Proof.
  unfold x12_over.
  apply subtype_over_closed_by_qualifier.
  - unfold q_range. logic_subtype_wf.
  - unfold q_range. rewrite logic_qual_dom_nu_pred. set_solver.
  - unfold q_range. rewrite logic_qual_dom_nu_pred. set_solver.
  - apply logic_nu_pred_entails. lia.
Qed.

Theorem logic_project_x_example45_over :
  ∅; x ∷ x12_over ⊢ₓ logic_project_x ⋮ ({: ℕ | q_range 0 4 }).
Proof.
  unfold logic_project_x.
  eapply EXT_Sub.
  - unfold x12_over, q_range. logic_wf.
  - eapply EXT_Var. unfold x12_over, q_range. logic_wf.
  - exact logic_project_x_obl_over_weaken.
Qed.

(** Example 4.5, angelic: [r_x ⊨ U Atom(x = 1)] (angelic refinements are
    contravariant: [ν = 1] entails [1 ≤ ν ≤ 2]).  Proved from the CORRECTED
    under lemma [subtype_under_closed_by_qualifier_corrected]
    (extra premises: [ν = 1] mentions no variable besides [ν], and is
    satisfiable).  The shared [subtype_under_closed_by_qualifier] is false in
    general and is no longer used. *)
Lemma logic_project_x_obl_under_weaken :
  sub_type_under ∅ (x ∷ x12_under) x12_under ([: ℕ | q_eq_nat 1 ]).
Proof.
  unfold x12_under.
  apply subtype_under_closed_by_qualifier_corrected.
  - unfold q_range, q_eq_nat. logic_subtype_wf.
  - unfold q_range. rewrite logic_qual_dom_nu_pred. set_solver.
  - unfold q_eq_nat. rewrite logic_qual_dom_nu_pred. set_solver.
  - apply logic_nu_pred_entails. lia.
  - apply logic_nu_pred_vars_sub.
  - apply (logic_nu_pred_sat _ 1). reflexivity.
Qed.

Theorem logic_project_x_example45_under :
  ∅; x ∷ x12_under ⊢ₓ logic_project_x ⋮ ([: ℕ | q_eq_nat 1 ]).
Proof.
  unfold logic_project_x.
  eapply EXT_Sub.
  - unfold x12_under, q_range, q_eq_nat. logic_wf.
  - eapply EXT_Var. unfold x12_under, q_range. logic_wf.
  - exact logic_project_x_obl_under_weaken.
Qed.

(** ✗ (Example 4.5): [x:{1≤ν≤2} ⊢ x : {ν = 1}] -- [r_x] itself is a model
    of the context in which [x ↦ 2] occurs; and [x:[1≤ν≤2] ⊢ x : [0≤ν≤4]] --
    [r_x] is a model which does not reach [0, 3, 4].  Not typed. *)

(** Example 4.6, projection of the entangled context.  Obligation:
    [x:[1≤ν≤2], y:[0≤ν<x] ≤_{x} x:[1≤ν≤2]].  Informal argument:
    [⟦Γ1, Γ2⟧ = ⟦Γ1⟧ ∧ ⟦Γ2⟧], so [r ⊨ ⟦x:[1≤ν≤2]⟧]; this formula only
    mentions [x], hence it holds of [r|{x}] (restriction to a superset of the
    free variables preserves satisfaction). *)
Lemma logic_project_x_obl_entangled_proj :
  ctx_sub_under ∅ ({[x]} : aset) ex46_ctx (x ∷ x12_under).
Proof.
  apply logic_ctx_sub_by_entails.
  - unfold ex46_ctx, y_below_x, x12_under, q_range, wf_ctx_under. logic_wf_goals.
  - unfold x12_under, q_range, wf_ctx_under. logic_wf_goals.
  - intros z Hz. assert (z = x) by set_solver. subst z. vm_compute. reflexivity.
  - intros r Hr. unfold ex46_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _].
    cbn [ctx_denote_under] in Hr.
    logic_close_by_env_compute Hr.
Qed.

Theorem logic_project_x_example46 :
  ∅; ex46_ctx ⊢ₓ logic_project_x ⋮ x12_under.
Proof.
  unfold logic_project_x.
  eapply (logic_ext_ctx_sub _ _ (x ∷ x12_under) ({[x]} : aset)).
  - unfold ex46_ctx, y_below_x, x12_under, q_range. logic_wf.
  - eapply EXT_Var. unfold x12_under, q_range. logic_wf.
  - logic_dom_sub.
  - exact logic_project_x_obl_entangled_proj.
Qed.

(** ** [logic_product_style_example = x + y] *)

(** Obligation (product, p.16):
      x:[1≤ν≤2] ∗ y:[3≤ν≤4] ⊢ {ν = x + y} ⊓ [ν = x + y] <: [4 ≤ ν ≤ 6].
    Informal argument: a model projects on [{x,y}] to a product
    [r_x × r_y] with [{1,2} ⊆ r_x] and [{3,4} ⊆ r_y]; the environments
    [(1,3), (1,4), (2,4)] are all present, and by the precise source type the
    result in them is [4, 5, 6]; restricting the result capability to those
    environments gives exactly [Atom(4 ≤ ν ≤ 6)], i.e. [U Atom(4≤ν≤6)]. *)
Lemma logic_product_style_example_obl_product :
  sub_type_under ∅ product_ctx
    (binop_precise_ty bop_plus (vfvar x) (vfvar y)) ([: ℕ | q_range 4 6 ]).
Proof.
Admitted.

Theorem logic_product_style_example_product :
  ∅; product_ctx ⊢ₓ logic_product_style_example ⋮ ([: ℕ | q_range 4 6 ]).
Proof.
  unfold logic_product_style_example.
  eapply EXT_Sub.
  - unfold product_ctx, x12_under, y34_under, q_range. logic_wf.
  - eapply EXT_BinOp. unfold product_ctx, x12_under, y34_under, q_range. logic_wf.
  - exact logic_product_style_example_obl_product.
Qed.

(** ✗ (p.16, entangled version of the product example):
      x:[1≤ν≤2], y:[3≤ν≤4] ⊢ x + y : [4≤ν≤6].
    Counterexample capability [r_xy = {[x↦1,y↦3],[x↦2,y↦4]}]: it satisfies
    the entangled context (both projections are covered; [y]'s qualifier
    does not mention [x]) but [x + y] only reaches [{4, 6}].  Not typed. *)

(** Obligation (Example 4.6):
      x:[1≤ν≤2], y:[0≤ν<x] ⊢ {ν = x + y} ⊓ [ν = x + y] <: [1 ≤ ν ≤ 3].
    Informal argument: by [U(1≤x≤2)] both [x ↦ 1] and [x ↦ 2] occur; by
    [x ▷ U(0 ≤ y < x)] the [x ↦ 1] fiber contains [y ↦ 0] and the [x ↦ 2]
    fiber contains [y ↦ 0] and [y ↦ 1]; the precise sum gives results
    [1, 2, 3] in these environments, hence [U Atom(1 ≤ ν ≤ 3)]. *)
Lemma logic_product_style_example_obl_entangled :
  sub_type_under ∅ ex46_ctx
    (binop_precise_ty bop_plus (vfvar x) (vfvar y)) ([: ℕ | q_range 1 3 ]).
Proof.
Admitted.

Theorem logic_product_style_example_example46 :
  ∅; ex46_ctx ⊢ₓ logic_product_style_example ⋮ ([: ℕ | q_range 1 3 ]).
Proof.
  unfold logic_product_style_example.
  eapply EXT_Sub.
  - unfold ex46_ctx, y_below_x, x12_under, q_range. logic_wf.
  - eapply EXT_BinOp. unfold ex46_ctx, y_below_x, x12_under, q_range. logic_wf.
  - exact logic_product_style_example_obl_entangled.
Qed.

(** ** [logic_correlated_xy = let y = x + 1 in x + y]

    [y] is entangled with [x] (as in the paper's [C_en], p.6): the result is
    [2x + 1], so under [x:[1≤ν≤2]] exactly [3] and [5] are reachable.
    ✓ [x:[1≤ν≤2] ⊢ e : [ν = 3 ∨ ν = 5]];
    ✗ [x:[1≤ν≤2] ⊢ e : [3 ≤ ν ≤ 5]] (4 is unreachable: [r_x] is a model).
    Over-approximate counterpart: [x:{1≤ν≤2} ⊢ e : {3 ≤ ν ≤ 5}] ✓. *)

Definition q_3_or_5 : type_qualifier := q_nat_pred ν (fun n => n = 3%nat \/ n = 5%nat).

Definition correlated_ctx (τx : context_ty) : ctx :=
  (x ∷ τx) ,, (y ∷ binop_precise_ty bop_plus (vfvar x) (vconst (cnat 1))).

(** Obligation: [x:[1≤ν≤2], y:{ν=x+1}⊓[ν=x+1] ⊢ {ν=x+y}⊓[ν=x+y] <: [ν=3 ∨ ν=5]].
    Informal argument: [x ↦ 1] and [x ↦ 2] occur; by the precise binding of
    [y] (fibered over [x] by [▷]), every environment has [y = x + 1], and each
    [x]-fiber is non-empty; the precise sum yields [1+2 = 3] and [2+3 = 5],
    so the result capability contains a sub-capability with exactly
    [{3, 5}]. *)
Lemma logic_correlated_xy_obl_under :
  sub_type_under ∅ (correlated_ctx x12_under)
    (binop_precise_ty bop_plus (vfvar x) (vfvar y)) ([: ℕ | q_3_or_5 ]).
Proof.
Admitted.

Theorem logic_correlated_xy_under :
  ∅; x ∷ x12_under ⊢ₓ logic_correlated_xy ⋮ ([: ℕ | q_3_or_5 ]).
Proof.
  unfold logic_correlated_xy.
  eapply (EXT_LetNamed _ _ _
    (binop_precise_ty bop_plus (vfvar x) (vconst (cnat 1)))).
  - unfold x12_under, q_range, q_3_or_5. logic_wf.
  - eapply EXT_BinOp. unfold x12_under, q_range. logic_wf.
  - eapply EXT_Sub.
    + unfold x12_under, q_range, q_3_or_5. logic_wf.
    + eapply EXT_BinOp. unfold x12_under, q_range. logic_wf.
    + exact logic_correlated_xy_obl_under.
Qed.

(** Obligation: [x:{1≤ν≤2}, y:{ν=x+1}⊓[ν=x+1] ⊢ {ν=x+y}⊓[ν=x+y] <: {3≤ν≤5}].
    Informal argument: every environment has [x ∈ {1,2}] and [y = x + 1],
    so the result [2x+1 ∈ {3,5} ⊆ [3,5]]; the over-approximate atom is
    satisfied by adding the missing valuation [ν = 4]. *)
Lemma logic_correlated_xy_obl_over :
  sub_type_under ∅ (correlated_ctx x12_over)
    (binop_precise_ty bop_plus (vfvar x) (vfvar y)) ({: ℕ | q_range 3 5 }).
Proof.
Admitted.

Theorem logic_correlated_xy_over :
  ∅; x ∷ x12_over ⊢ₓ logic_correlated_xy ⋮ ({: ℕ | q_range 3 5 }).
Proof.
  unfold logic_correlated_xy.
  eapply (EXT_LetNamed _ _ _
    (binop_precise_ty bop_plus (vfvar x) (vconst (cnat 1)))).
  - unfold x12_over, q_range. logic_wf.
  - eapply EXT_BinOp. unfold x12_over, q_range. logic_wf.
  - eapply EXT_Sub.
    + unfold x12_over, q_range. logic_wf.
    + eapply EXT_BinOp. unfold x12_over, q_range. logic_wf.
    + exact logic_correlated_xy_obl_over.
Qed.

(** ** [logic_branch_atom_example = let c = x ≤ 2 in if c then x else y + 1]

    With [x:{1≤ν≤2}] the guard is always [true], so only the [then] branch is
    reachable and the [else] branch is never typed (T-MatchTrueOnly, paper
    Example 3.4 last part).  This is Example 4.5's [r_x ⊨ O Atom(0≤x≤4)]
    lifted through an unreachable branch.  With the precise
    [x:{1≤ν≤2} ⊓ [1≤ν≤2]] we additionally get [r_x ⊨ U Atom(x = 1)].

    Angelic-only context (round 2).  With [x:[1≤ν≤2]] alone the guard is not
    determined (models may contain [x ↦ 3]) and the [else] branch need not be
    reachable (the model [r_x]); round 1 reported the judgment at [[ν = 1]]
    as not derivable.  It IS derivable with the capability case split
    [T-CtxCase]: see [logic_branch_atom_example_under] below. *)

Definition branch_ctx (τx : context_ty) : ctx :=
  ((x ∷ τx) ,, (y ∷ ONat)) ,,
    (c ∷ binop_precise_ty bop_le (vfvar x) (vconst (cnat 2))).

(** Obligation (guard determined, demonic part): every environment has
    [x ≤ 2] and [c = (x ≤ 2)], so [c = true] everywhere; capabilities are
    non-empty, hence [r|{c} = {[c ↦ true]}] satisfies
    [{ν = true} ⊓ [ν = true]]. *)
Lemma logic_branch_atom_example_obl_guard (τx : context_ty) :
  τx = x12_over \/ τx = x12_precise ->
  ctx_sub_under ∅ ({[c]} : aset) (branch_ctx τx) (c ∷ bool_precise_ty true).
Proof.
Admitted.

(** Obligation (projection of the first [,]-binding, closed type):
    [⟦(x:τx, y:⊤), c:τc⟧ ⊨ ⟦x:τx⟧], and [⟦x:τx⟧] only mentions [x]. *)
Lemma logic_branch_atom_example_obl_proj_x (τx : context_ty) :
  τx = x12_over \/ τx = x12_precise ->
  ctx_sub_under ∅ ({[x]} : aset) (branch_ctx τx) (x ∷ τx).
Proof.
  intros Hτ.
  apply logic_ctx_sub_by_entails.
  - destruct Hτ as [-> | ->];
      unfold branch_ctx, x12_precise, x12_over, x12_under, q_range, wf_ctx_under;
      logic_wf_goals.
  - destruct Hτ as [-> | ->];
      unfold x12_precise, x12_over, x12_under, q_range, wf_ctx_under;
      logic_wf_goals.
  - intros z Hz. assert (z = x) by set_solver. subst z.
    destruct Hτ as [-> | ->]; vm_compute; reflexivity.
  - intros r Hr. unfold branch_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _].
    cbn [ctx_denote_under] in Hr.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _].
    cbn [ctx_denote_under] in Hr.
    destruct Hτ as [-> | ->]; logic_close_by_env_compute Hr.
Qed.

Theorem logic_branch_atom_example_over :
  ∅; (x ∷ x12_over) ,, (y ∷ ONat) ⊢ₓ logic_branch_atom_example ⋮
    ({: ℕ | q_range 0 4 }).
Proof.
  unfold logic_branch_atom_example.
  eapply (EXT_LetNamed _ _ _
    (binop_precise_ty bop_le (vfvar x) (vconst (cnat 2)))).
  - unfold x12_over, q_range. logic_wf.
  - eapply EXT_BinOp. unfold x12_over, q_range. logic_wf.
  - change (((x ∷ x12_over) ,, (y ∷ ONat)) ,,
              (c ∷ binop_precise_ty bop_le (vfvar x) (vconst (cnat 2))))
      with (branch_ctx x12_over).
    eapply EXT_MatchTrueOnly.
    + unfold branch_ctx, x12_over, q_range. logic_wf.
    + eapply (logic_ext_ctx_sub _ _ (c ∷ bool_precise_ty true) ({[c]} : aset)).
      * unfold branch_ctx, x12_over, q_range. logic_wf.
      * eapply EXT_Var. logic_wf.
      * logic_dom_sub.
      * apply logic_branch_atom_example_obl_guard. left. reflexivity.
    + eapply (logic_ext_ctx_sub _ _ (x ∷ x12_over) ({[x]} : aset)).
      * unfold branch_ctx, x12_over, q_range. logic_wf.
      * eapply EXT_Sub.
        -- unfold x12_over, q_range. logic_wf.
        -- eapply EXT_Var. unfold x12_over, q_range. logic_wf.
        -- exact logic_project_x_obl_over_weaken.
      * logic_dom_sub.
      * apply logic_branch_atom_example_obl_proj_x. left. reflexivity.
Qed.

(** [x:{1≤ν≤2}⊓[1≤ν≤2] ⊢ x : [ν = 1]], proved from the shared generic lemmas (trans, inter_right and the CORRECTED under lemma; the original [subtype_under_closed_by_qualifier] was false and has been removed). *)
Lemma logic_branch_atom_example_obl_precise_under :
  sub_type_under ∅ (x ∷ x12_precise) x12_precise ([: ℕ | q_eq_nat 1 ]).
Proof.
  unfold x12_precise.
  eapply (extended_semantic_subtype_trans _ _ _ x12_under).
  - apply extended_semantic_subtype_inter_right.
    unfold x12_over, x12_under, q_range. logic_subtype_wf.
  - unfold x12_under.
    apply subtype_under_closed_by_qualifier_corrected.
    + unfold x12_precise, x12_over, x12_under, q_range, q_eq_nat. logic_subtype_wf.
    + unfold q_range. rewrite logic_qual_dom_nu_pred. set_solver.
    + unfold q_eq_nat. rewrite logic_qual_dom_nu_pred. set_solver.
    + apply logic_nu_pred_entails. lia.
    + apply logic_nu_pred_vars_sub.
    + apply (logic_nu_pred_sat _ 1). reflexivity.
Qed.

Theorem logic_branch_atom_example_precise :
  ∅; (x ∷ x12_precise) ,, (y ∷ ONat) ⊢ₓ logic_branch_atom_example ⋮
    ([: ℕ | q_eq_nat 1 ]).
Proof.
  unfold logic_branch_atom_example.
  eapply (EXT_LetNamed _ _ _
    (binop_precise_ty bop_le (vfvar x) (vconst (cnat 2)))).
  - unfold x12_precise, x12_over, x12_under, q_range, q_eq_nat. logic_wf.
  - eapply EXT_BinOp. unfold x12_precise, x12_over, x12_under, q_range. logic_wf.
  - change (((x ∷ x12_precise) ,, (y ∷ ONat)) ,,
              (c ∷ binop_precise_ty bop_le (vfvar x) (vconst (cnat 2))))
      with (branch_ctx x12_precise).
    eapply EXT_MatchTrueOnly.
    + unfold branch_ctx, x12_precise, x12_over, x12_under, q_range, q_eq_nat.
      logic_wf.
    + eapply (logic_ext_ctx_sub _ _ (c ∷ bool_precise_ty true) ({[c]} : aset)).
      * unfold branch_ctx, x12_precise, x12_over, x12_under, q_range. logic_wf.
      * eapply EXT_Var. logic_wf.
      * logic_dom_sub.
      * apply logic_branch_atom_example_obl_guard. right. reflexivity.
    + eapply (logic_ext_ctx_sub _ _ (x ∷ x12_precise) ({[x]} : aset)).
      * unfold branch_ctx, x12_precise, x12_over, x12_under, q_range, q_eq_nat.
        logic_wf.
      * eapply EXT_Sub.
        -- unfold x12_precise, x12_over, x12_under, q_range, q_eq_nat. logic_wf.
        -- eapply EXT_Var. unfold x12_precise, x12_over, x12_under, q_range. logic_wf.
        -- exact logic_branch_atom_example_obl_precise_under.
      * logic_dom_sub.
      * apply logic_branch_atom_example_obl_proj_x. right. reflexivity.
Qed.

(** ** [logic_branch_atom_example] under the angelic-only [x:[1≤ν≤2]]

    Round 1 reported this judgment as not derivable.  With [T-CtxCase] it is:
    a model of [branch_ctx x12_under] either has [x ≤ 2] in every environment
    (then [c] is constantly [true]: [T-MatchTrueOnly] in
    [branch_true_ctx]), or it contains some [x > 2] (then both branches are
    reachable: its restriction splits into the [x ≤ 2] part, a model of
    [branch_true_ctx], and the [x > 2] part, a model of [branch_false_ctx];
    [T-MatchBoth]).  The [else] branch is given the demonic top type
    [O[ℕ]] by [T-BinOpTop]; the sum [[ν = 1] ⊕ O[ℕ]] is then weakened to
    [[ν = 1]]: the [then] summand already reaches [1]. *)

Definition branch_true_ctx : ctx :=
  ((x ∷ x12_under) ,, (y ∷ ONat)) ,, (c ∷ bool_precise_ty true).

Definition branch_false_ctx : ctx :=
  ((x ∷ ONat) ,, (y ∷ ONat)) ,, (c ∷ bool_precise_ty false).

(** Obligation (capability case split, T-CtxCase):
      Γ = x:[1≤ν≤2], y:O[ℕ], c:({ν = (x ≤ 2)} ⊓ [ν = (x ≤ 2)])
      ⊑_{x,y,c}  Γtrue  or  Γtrue ⊕ Γfalse.
    Informal argument: let [r ⊨ ⟦Γ⟧] and [r' = r|{x,y,c}] (so [r|X ⊑ r']).
    By the precise binding of [c] (fibered over [x]), every environment of
    [r'] has [c = (x ≤ 2)].
    - If every environment has [x ≤ 2], then [c = true] everywhere; [r'] is
      non-empty, so [r'|{c} = {c ↦ true}] satisfies the closed
      [{ν = true} ⊓ [ν = true]]; the [x]- and [y]-bindings of [Γtrue] are
      those of [Γ] (the [y]-binding [O[ℕ]] is trivial), hence [r' ⊨ ⟦Γtrue⟧].
    - Otherwise let [T = {σ ∈ r' | σ(x) ≤ 2}], [F = {σ ∈ r' | σ(x) > 2}].
      [F] is non-empty by assumption, [T] is non-empty since [x ↦ 1] occurs
      ([U(1≤x≤2)]); both have domain [{x,y,c}] and [T ∪ F = r'], so
      [r' = T + F] (FPlus).  [T ⊨ ⟦Γtrue⟧]: [T] contains every environment of
      [r'] with [x ∈ {1,2}], so its [x]-projection still covers [{1,2}]
      ([U Atom(1≤ν≤2)]), [y] is unconstrained and [c = true] on all of [T].
      [F ⊨ ⟦Γfalse⟧]: [x], [y] are unconstrained ([O[ℕ]]) and [c = false]
      on all of [F]. *)
Lemma logic_branch_atom_example_obl_case :
  ctx_case_under ∅ ({[c]} ∪ {[x]} ∪ {[y]} : aset) (branch_ctx x12_under)
    branch_true_ctx (branch_true_ctx ⊕ branch_false_ctx).
Proof.
Admitted.

(** Obligation (affine sum weakening):
      Γtrue ⊕ Γfalse ⊢ [ν = 1] ⊕ O[ℕ] <: [ν = 1].
    Informal argument: a result capability [m ⊨ ⟦[ν=1] ⊕ O[ℕ]⟧] is a sum
    [m1 + m2] of two non-empty capabilities with the same domain and
    [m1 ⊨ ⟦[ν=1]⟧]; [m1] contains a sub-capability whose results are exactly
    [{1}]; it is also a sub-capability of [m = m1 ∪ m2], hence
    [m ⊨ U Atom(ν = 1)]; the basic (totality/typing) guard is shared since the
    erasures agree. *)
Lemma logic_branch_atom_example_obl_sum :
  sub_type_under ∅ (branch_true_ctx ⊕ branch_false_ctx)
    (([: ℕ | q_eq_nat 1 ]) ⊕ binop_top_ty bop_plus) ([: ℕ | q_eq_nat 1 ]).
Proof.
Admitted.

(** Structural projections out of the branch contexts (Qed). *)
Lemma logic_branch_true_obl_guard :
  ctx_sub_under ∅ ({[c]} : aset) branch_true_ctx (c ∷ bool_precise_ty true).
Proof.
  apply logic_ctx_sub_by_entails.
  - unfold branch_true_ctx, x12_under, q_range, wf_ctx_under. logic_wf_goals.
  - unfold wf_ctx_under. logic_wf_goals.
  - intros z Hz. assert (z = c) by set_solver. subst z. vm_compute. reflexivity.
  - intros r Hr. unfold branch_true_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c (bool_precise_ty true)) = ∅)
      by (apply logic_closed_fv; logic_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

Lemma logic_branch_false_obl_guard :
  ctx_sub_under ∅ ({[c]} : aset) branch_false_ctx (c ∷ bool_precise_ty false).
Proof.
  apply logic_ctx_sub_by_entails.
  - unfold branch_false_ctx, wf_ctx_under. logic_wf_goals.
  - unfold wf_ctx_under. logic_wf_goals.
  - intros z Hz. assert (z = c) by set_solver. subst z. vm_compute. reflexivity.
  - intros r Hr. unfold branch_false_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    assert (Hfv : ctx_fv (CtxBind c (bool_precise_ty false)) = ∅)
      by (apply logic_closed_fv; logic_wf_type).
    rewrite Hfv in Hr |- *. rewrite !storeA_restrict_empty_set in Hr |- *.
    exact Hr.
Qed.

Lemma logic_branch_true_obl_proj_x :
  ctx_sub_under ∅ ({[x]} : aset) branch_true_ctx (x ∷ x12_under).
Proof.
  apply logic_ctx_sub_by_entails.
  - unfold branch_true_ctx, x12_under, q_range, wf_ctx_under. logic_wf_goals.
  - unfold x12_under, q_range, wf_ctx_under. logic_wf_goals.
  - intros z Hz. assert (z = x) by set_solver. subst z. vm_compute. reflexivity.
  - intros r Hr. unfold branch_true_ctx in Hr. cbn [ctx_denote_under] in Hr |- *.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _].
    cbn [ctx_denote_under] in Hr.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _].
    cbn [ctx_denote_under] in Hr.
    logic_close_by_env_compute Hr.
Qed.

(** [Γtrue ⊢ if c then x else y + 1 : [ν = 1]] (T-MatchTrueOnly). *)
Lemma logic_branch_atom_example_true_part :
  ∅; branch_true_ctx ⊢ₓ
    (if (avar c) then ret (avar x) else (y ⟨ + ⟩ vnat 1)) ⋮ ([: ℕ | q_eq_nat 1 ]).
Proof.
  eapply EXT_MatchTrueOnly.
  - unfold branch_true_ctx, x12_under, q_range, q_eq_nat. logic_wf.
  - eapply (logic_ext_ctx_sub _ _ (c ∷ bool_precise_ty true) ({[c]} : aset)).
    + unfold branch_true_ctx, x12_under, q_range. logic_wf.
    + eapply EXT_Var. logic_wf.
    + logic_dom_sub.
    + exact logic_branch_true_obl_guard.
  - eapply (logic_ext_ctx_sub _ _ (x ∷ x12_under) ({[x]} : aset)).
    + unfold branch_true_ctx, x12_under, q_range, q_eq_nat. logic_wf.
    + eapply EXT_Sub.
      * unfold x12_under, q_range, q_eq_nat. logic_wf.
      * eapply EXT_Var. unfold x12_under, q_range. logic_wf.
      * exact logic_project_x_obl_under_weaken.
    + logic_dom_sub.
    + exact logic_branch_true_obl_proj_x.
Qed.

Theorem logic_branch_atom_example_under :
  ∅; (x ∷ x12_under) ,, (y ∷ ONat) ⊢ₓ logic_branch_atom_example ⋮
    ([: ℕ | q_eq_nat 1 ]).
Proof.
  unfold logic_branch_atom_example.
  eapply (EXT_LetNamed _ _ _
    (binop_precise_ty bop_le (vfvar x) (vconst (cnat 2)))).
  - unfold x12_under, q_range, q_eq_nat. logic_wf.
  - eapply EXT_BinOp. unfold x12_under, q_range. logic_wf.
  - change (((x ∷ x12_under) ,, (y ∷ ONat)) ,,
              (c ∷ binop_precise_ty bop_le (vfvar x) (vconst (cnat 2))))
      with (branch_ctx x12_under).
    eapply (logic_ext_ctx_case _ _ branch_true_ctx
      (branch_true_ctx ⊕ branch_false_ctx) ({[c]} ∪ {[x]} ∪ {[y]} : aset)).
    + unfold branch_ctx, x12_under, q_range, q_eq_nat. logic_wf.
    + exact logic_branch_atom_example_true_part.
    + eapply (EXT_Sub _ _ _ (([: ℕ | q_eq_nat 1 ]) ⊕ binop_top_ty bop_plus)).
      * unfold branch_true_ctx, branch_false_ctx, x12_under, q_range, q_eq_nat.
        logic_wf.
      * eapply EXT_MatchBoth.
        -- unfold branch_true_ctx, branch_false_ctx, x12_under, q_range, q_eq_nat.
           logic_wf.
        -- eapply (logic_ext_ctx_sub _ _ (c ∷ bool_precise_ty true) ({[c]} : aset)).
           ++ unfold branch_true_ctx, x12_under, q_range. logic_wf.
           ++ eapply EXT_Var. logic_wf.
           ++ logic_dom_sub.
           ++ exact logic_branch_true_obl_guard.
        -- eapply (logic_ext_ctx_sub _ _ (c ∷ bool_precise_ty false) ({[c]} : aset)).
           ++ unfold branch_false_ctx. logic_wf.
           ++ eapply EXT_Var. logic_wf.
           ++ logic_dom_sub.
           ++ exact logic_branch_false_obl_guard.
        -- eapply (logic_ext_ctx_sub _ _ (x ∷ x12_under) ({[x]} : aset)).
           ++ unfold branch_true_ctx, x12_under, q_range, q_eq_nat. logic_wf.
           ++ eapply EXT_Sub.
              ** unfold x12_under, q_range, q_eq_nat. logic_wf.
              ** eapply EXT_Var. unfold x12_under, q_range. logic_wf.
              ** exact logic_project_x_obl_under_weaken.
           ++ logic_dom_sub.
           ++ exact logic_branch_true_obl_proj_x.
        -- eapply EXT_BinOpTop. unfold branch_false_ctx. logic_wf.
      * exact logic_branch_atom_example_obl_sum.
    + unfold branch_true_ctx. logic_dom_sub.
    + exact logic_branch_atom_example_obl_case.
Qed.

(** ** [logic_implication_witness = λx. x + 1]

    The entangled arrow is the additive implication of the logic:
    [⟦x:τx → τ⟧ f = ⟦τx⟧ x ⇒ ⟦τ⟧ (f x)].
    ✓ [⊢ λx. x+1 : x:[1≤ν≤2] → [2≤ν≤3]] and
    ✓ [⊢ λx. x+1 : x:{1≤ν≤2} → {2≤ν≤3}]. *)

(** Obligation: [x:[1≤ν≤2] ⊢ {ν=x+1}⊓[ν=x+1] <: [2≤ν≤3]]: [x ↦ 1, 2] occur
    and give results [2, 3]. *)
Lemma logic_implication_witness_obl_under :
  sub_type_under ∅ (Emp ,, (x ∷ x12_under))
    (binop_precise_ty bop_plus (vfvar x) (vconst (cnat 1))) ([: ℕ | q_range 2 3 ]).
Proof.
Admitted.

Theorem logic_implication_witness_under :
  ∅; Emp ⊢ₓ logic_implication_witness ⋮ (x12_under → [: ℕ | q_range 2 3 ]).
Proof.
  unfold logic_implication_witness.
  eapply EXT_LamNamedErased.
  - reflexivity.
  - unfold x12_under, q_range. logic_wf.
  - eapply EXT_Sub.
    + unfold x12_under, q_range. logic_wf.
    + eapply EXT_BinOp. unfold x12_under, q_range. logic_wf.
    + exact logic_implication_witness_obl_under.
Qed.

(** Obligation: [x:{1≤ν≤2} ⊢ {ν=x+1}⊓[ν=x+1] <: {2≤ν≤3}]: pointwise
    [1 ≤ x ≤ 2 ⇒ 2 ≤ x+1 ≤ 3] in every environment. *)
Lemma logic_implication_witness_obl_over :
  sub_type_under ∅ (Emp ,, (x ∷ x12_over))
    (binop_precise_ty bop_plus (vfvar x) (vconst (cnat 1))) ({: ℕ | q_range 2 3 }).
Proof.
Admitted.

Theorem logic_implication_witness_over :
  ∅; Emp ⊢ₓ logic_implication_witness ⋮ (x12_over → {: ℕ | q_range 2 3 }).
Proof.
  unfold logic_implication_witness.
  eapply EXT_LamNamedErased.
  - reflexivity.
  - unfold x12_over, q_range. logic_wf.
  - eapply EXT_Sub.
    + unfold x12_over, q_range. logic_wf.
    + eapply EXT_BinOp. unfold x12_over, q_range. logic_wf.
    + exact logic_implication_witness_obl_over.
Qed.


End Section3LogicExamples.
