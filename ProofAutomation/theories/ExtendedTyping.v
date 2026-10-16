(** * ProofAutomation.ExtendedTyping

    A proof-automation facing extension layer for context typing.

    The rules intentionally mirror [ContextTyping.Typing.has_context_type],
    but recursive premises mention [has_extended_context_type].  This keeps the
    current core rules available while giving case studies a separate judgment
    where extra proof-only rules can be added later.  No fundamental theorem is
    proved for this extension layer. *)

From stdpp Require Import gmap.
From Stdlib Require Import List.
From CoreLang Require Import SmallStep SyntaxNotation Sugar.
From ContextLogic Require Import FormulaConnectivesHigher.
From ContextTypeLanguage Require Import Syntax.
From Denotation Require Import Context.
From ProofAutomation Require Import CaseTypes.
From ContextTyping Require Import PrimOpContext PrimOpConcreteContext Typing.

Import ListNotations.
Open Scope core_scope.
Open Scope cty_scope.
Open Scope ctx_scope.
Open Scope case_scope.

(** ** Proof-automation-only precise operation helpers *)

Definition binop_result_qual (op : bin_op) (v1 v2 : value) : type_qualifier :=
  tqual
    (lvar_value_keys (vbvar 0) ∪ lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ =>
       exists c1 c2 c',
         denote_lvar_value (lso_store σ) v1 = Some (vconst c1) /\
         denote_lvar_value (lso_store σ) v2 = Some (vconst c2) /\
         denote_lvar_value (lso_store σ) (vbvar 0) = Some (vconst c') /\
         bin_step op c1 c2 c').

Definition binop_precise_ty (op : bin_op) (v1 v2 : value) : context_ty :=
  match bin_op_type op with
  | (_, _, ret_b) =>
      (fun q => {: ret_b | q} ⊓ [: ret_b | q])
      (binop_result_qual op v1 v2)
  end.

Definition binop_top_ty (op : bin_op) : context_ty :=
  match bin_op_type op with
  | (_, _, ret_b) => O[ ret_b ]
  end.

Definition primop_result_qual (op : prim_op) (v : value) : type_qualifier :=
  tqual
    (lvar_value_keys (vbvar 0) ∪ lvar_value_keys v)
    (fun σ =>
       exists c c',
         denote_lvar_value (lso_store σ) v = Some (vconst c) /\
         denote_lvar_value (lso_store σ) (vbvar 0) = Some (vconst c') /\
         prim_step op c c').

Definition primop_precise_ty (op : prim_op) (v : value) : context_ty :=
  match prim_op_type op with
  | (_, ret_b) =>
      (fun q => {: ret_b | q} ⊓ [: ret_b | q])
        (primop_result_qual op v)
  end.

Definition tree_node_result_qual
    (root left right : value) : type_qualifier :=
  tqual
    (lvar_value_keys (vbvar 0) ∪ lvar_value_keys root ∪
       lvar_value_keys left ∪ lvar_value_keys right)
    (fun σ =>
       exists n l r,
         denote_lvar_value (lso_store σ) root = Some (vconst (cnat n)) /\
         denote_lvar_value (lso_store σ) left = Some (vconst (ctree l)) /\
         denote_lvar_value (lso_store σ) right = Some (vconst (ctree r)) /\
         denote_lvar_value (lso_store σ) (vbvar 0) =
           Some (vconst (ctree (tr_node n l r)))).

Definition tree_node_precise_ty
    (root left right : value) : context_ty :=
  (fun q => {: Tree | q} ⊓ [: Tree | q])
    (tree_node_result_qual root left right).

Definition list_cons_result_qual (hd tl : value) : type_qualifier :=
  tqual
    (lvar_value_keys (vbvar 0) ∪ lvar_value_keys hd ∪ lvar_value_keys tl)
    (fun σ =>
       exists n xs,
         denote_lvar_value (lso_store σ) hd = Some (vconst (cnat n)) /\
         denote_lvar_value (lso_store σ) tl = Some (vconst (clist xs)) /\
         denote_lvar_value (lso_store σ) (vbvar 0) =
           Some (vconst (clist (n :: xs)))).

Definition list_cons_precise_ty (hd tl : value) : context_ty :=
  (fun q => {: List | q} ⊓ [: List | q])
    (list_cons_result_qual hd tl).

Definition tree_node_pattern_ctx
    (root left right : atom) : ctx :=
  ((root ∷ ONat) ,, (left ∷ OTree)) ,, (right ∷ OTree).

Definition list_cons_pattern_ctx (hd tl : atom) : ctx :=
  (hd ∷ ONat) ,, (tl ∷ OList).

Definition tree_match_eq_ty (v : value) : context_ty :=
  (fun q => {: Tree | q} ⊓ [: Tree | q])
    (mk_q_eq (vbvar 0) v).

Definition list_match_eq_ty (v : value) : context_ty :=
  (fun q => {: List | q} ⊓ [: List | q])
    (mk_q_eq (vbvar 0) v).

(** Target shapes for which fixpoint unrolling is proved sound. *)
Fixpoint fix_unroll_shape (τ : context_ty) : Prop :=
  match τ with
  | CTArrow _ _ | CTOver _ _ | CTUnder _ _ => True
  | CTInter τ1 τ2 | CTUnion τ1 τ2 =>
      fix_unroll_shape τ1 /\ fix_unroll_shape τ2
  | _ => False
  end.

(** Capability case split: every model of [Γ] agrees on [X] with a model of
    [Γa] or of [Γb] (a disjunctive [ctx_sub_under]). *)
Definition ctx_case_under
    (Σ : gmap atom ty) (X : aset) (Γ Γa Γb : ctx) : Prop :=
  wf_ctx_under Σ Γ ∧
  wf_ctx_under Σ Γa ∧
  wf_ctx_under Σ Γb ∧
  ty_env_agree_on X (erase_ctx Γ) (erase_ctx Γa) ∧
  ty_env_agree_on X (erase_ctx Γ) (erase_ctx Γb) ∧
  ∀ r, r ⊨ ctx_denote_under Σ Γ →
       exists r',
         res_restrict r X ⊑ r' /\
         (r' ⊨ ctx_denote_under Σ Γa \/ r' ⊨ ctx_denote_under Σ Γb).

Notation "Σ ';' Γ '⊢wf' e '⋮' τ" :=
  (context_typing_wf Σ Γ e τ)
  (at level 20, Γ constr, e constr, τ constr,
   format "Σ ;  Γ  ⊢wf  e  ⋮  τ").

Reserved Notation "Σ ';' Γ '⊢ₓ' e '⋮' τ"
  (at level 20, Γ constr, e constr, τ constr).

Inductive has_extended_context_type
    (Σ : gmap atom ty) : ctx -> tm -> context_ty -> Prop :=

  (** T-Var *)
  | EXT_Var x τ :
      Σ; x ∷ τ ⊢wf ret (avar x) ⋮ τ ->
      Σ; x ∷ τ ⊢ₓ ret (avar x) ⋮ τ

  (** T-Const. *)
  | EXT_Const c :
      Σ; Emp ⊢wf ret (vconst c) ⋮ (const_precise_ty c) ->
      Σ; Emp ⊢ₓ ret (vconst c) ⋮ (const_precise_ty c)

  (** Named-builder rules for case studies.  These are proof-automation
      conveniences over the locally nameless core syntax. *)
  | EXT_LamNamed Γ x τx τ e :
      Σ; Γ ⊢wf ret (lam_named x (erase_ty τx) e) ⋮ (τx → τ) ->
      Σ; (Γ ,, (x ∷ τx)) ⊢ₓ e ⋮ τ ->
      Σ; Γ ⊢ₓ ret (lam_named x (erase_ty τx) e) ⋮ (τx → τ)

  | EXT_LamNamedErased Γ x Tx τx τ e :
      Tx = erase_ty τx ->
      Σ; Γ ⊢wf ret (lam_named x Tx e) ⋮ (τx → τ) ->
      Σ; (Γ ,, (x ∷ τx)) ⊢ₓ e ⋮ τ ->
      Σ; Γ ⊢ₓ ret (lam_named x Tx e) ⋮ (τx → τ)

  | EXT_LetNamed Γ x τ1 τ2 e1 e2 :
      Σ; Γ ⊢wf let x := e1 in e2 ⋮ τ2 ->
      Σ; Γ ⊢ₓ e1 ⋮ τ1 ->
      Σ; (Γ ,, (x ∷ τ1)) ⊢ₓ e2 ⋮ τ2 ->
      Σ; Γ ⊢ₓ let x := e1 in e2 ⋮ τ2

  (** Named separating variants (T-LamD / T-LetD with a concrete binder). *)
  | EXT_LamDNamedErased Γ x Tx τx τ e :
      Tx = erase_ty τx ->
      Σ; Γ ⊢wf ret (lam_named x Tx e) ⋮ (τx -∗ τ) ->
      Σ; (Γ ∗ (x ∷ τx)) ⊢ₓ e ⋮ τ ->
      Σ; Γ ⊢ₓ ret (lam_named x Tx e) ⋮ (τx -∗ τ)

  | EXT_LetDNamed Γ1 Γ2 x τ1 τ2 e1 e2 :
      Σ; Γ1 ∗ Γ2 ⊢wf let x := e1 in e2 ⋮ τ2 ->
      Σ; Γ1 ⊢ₓ e1 ⋮ τ1 ->
      Σ; (Γ2 ∗ (x ∷ τ1)) ⊢ₓ e2 ⋮ τ2 ->
      Σ; Γ1 ∗ Γ2 ⊢ₓ let x := e1 in e2 ⋮ τ2

  (** Named T-Fix: [fixfun_named self arg] with a concrete argument binder.
      Mirrors [EXT_Fix] after opening the argument binder with [arg]. *)
  | EXT_FixNamed Γ φx τ (self arg : atom) (b : base_ty) (t : ty) body :
      erase_ty τ = t ->
      Σ; Γ ⊢wf ret (fixfun_named self arg (TBase b) t body) ⋮ ({: b | φx} → τ) ->
      Σ; (Γ ,, (arg ∷ {: b | φx})) ⊢ₓ
        ret (lam_named self (TBase b →ₜ t) body) ⋮
        (fix_rec_call_ty b arg {: b | φx} τ → ({0 ~> arg} τ)) ->
      Σ; Γ ⊢ₓ ret (fixfun_named self arg (TBase b) t body) ⋮ ({: b | φx} → τ)

  (** Named T-ListMatch / T-TreeMatch in the paper's form (Fig. 4, T-Match):
      the context of a reachable branch BINDS the pattern variables itself,
      with user-chosen types (they are introduced by T-CtxSub, whose
      extension condition is exactly what makes this sound), and the precise
      pattern equation [d(ȳ) : {ν = x} ⊓ [ν = x]] is checked in that same
      context.  A previous version checked the premises under [Γ ,, Γpat] and
      concluded at [Γ]; that was UNSOUND (an unmodelable [Γpat] makes every
      premise vacuous): see [ExtendedRuleSoundness.ext_list_match_cons_only_named_unsound].
      These shapes are proved sound in [ExtendedRuleSoundness]
      ([ext_*_paper_rule_sound], [ext_list_match_nil_sound], ...). *)
  | EXT_ListMatchBothNamed Γn Γc (x : atom) τn τc enil hd tl econs :
      Σ; Γn ⊕ Γc ⊢wf
        match_list_named (avar x) enil hd tl econs ⋮ (τn ⊕ τc) ->
      Σ; Γn ⊢ₓ ret Nil ⋮ (list_match_eq_ty (avar x)) ->
      Σ; Γc ⊢ₓ (avar hd ::ᵗ avar tl) ⋮ (list_match_eq_ty (avar x)) ->
      Σ; Γn ⊢ₓ enil ⋮ τn ->
      Σ; Γc ⊢ₓ econs ⋮ τc ->
      Σ; Γn ⊕ Γc ⊢ₓ match_list_named (avar x) enil hd tl econs ⋮ (τn ⊕ τc)

  | EXT_ListMatchConsOnlyNamed Γ (x : atom) τ enil hd tl econs :
      Σ; Γ ⊢wf match_list_named (avar x) enil hd tl econs ⋮ τ ->
      Σ; Γ ⊢ₓ (avar hd ::ᵗ avar tl) ⋮ (list_match_eq_ty (avar x)) ->
      Σ; Γ ⊢ₓ econs ⋮ τ ->
      Σ; Γ ⊢ₓ match_list_named (avar x) enil hd tl econs ⋮ τ

  | EXT_TreeMatchBothNamed Γl Γn (x : atom) τl τn eleaf root left right enode :
      left <> right ->
      Σ; Γl ⊕ Γn ⊢wf
        match_tree_named (avar x) eleaf root left right enode ⋮ (τl ⊕ τn) ->
      Σ; Γl ⊢ₓ ret Leaf ⋮ (tree_match_eq_ty (avar x)) ->
      Σ; Γn ⊢ₓ [| avar root, avar left, avar right |] ⋮ (tree_match_eq_ty (avar x)) ->
      Σ; Γl ⊢ₓ eleaf ⋮ τl ->
      Σ; Γn ⊢ₓ enode ⋮ τn ->
      Σ; Γl ⊕ Γn ⊢ₓ
        match_tree_named (avar x) eleaf root left right enode ⋮ (τl ⊕ τn)

  | EXT_TreeMatchNodeOnlyNamed Γ (x : atom) τ eleaf root left right enode :
      left <> right ->
      Σ; Γ ⊢wf match_tree_named (avar x) eleaf root left right enode ⋮ τ ->
      Σ; Γ ⊢ₓ [| avar root, avar left, avar right |] ⋮ (tree_match_eq_ty (avar x)) ->
      Σ; Γ ⊢ₓ enode ⋮ τ ->
      Σ; Γ ⊢ₓ match_tree_named (avar x) eleaf root left right enode ⋮ τ

  (** T-VarComma.  The paper's T-Var [x:τ ⊢ x : τ] is checked under the basic
      context [Σ,⌊Γ⌋] when [τ] depends on [Γ] (WfComma).  The Rocq judgment
      keeps [Σ] fixed and checks [τ] against [⌊Γ⌋], so the dependency
      bindings stay in the context; T-CtxSub does all other structural work.
      Proved sound against the core denotation in [ExtendedRuleSoundness]. *)
  | EXT_VarComma Γ x τ :
      Σ; Γ ,, (x ∷ τ) ⊢wf ret (avar x) ⋮ τ ->
      Σ; Γ ,, (x ∷ τ) ⊢ₓ ret (avar x) ⋮ τ

  (** T-CtxCase (capability case split).  Every capability of [Γ] is, up to
      T-CtxSub's projection on the free variables, a capability of [Γa] or of
      [Γb].  Used to type a match whose branch reachability is not determined
      by the context: split into "both reachable" ([Γt ⊕ Γf]), "true only" and
      "false only".  Proved sound in [ExtendedRuleSoundness]. *)
  | EXT_CtxCase Γ Γa Γb e τ :
      Σ; Γ ⊢wf e ⋮ τ ->
      Σ; Γa ⊢ₓ e ⋮ τ ->
      Σ; Γb ⊢ₓ e ⋮ τ ->
      ctx_case_under Σ (fv_tm e ∪ fv_cty τ) Γ Γa Γb ->
      Σ; Γ ⊢ₓ e ⋮ τ

  (** T-FixUnroll.  A recursive function may be typed by its one-step
      unfolding [λarg. body[self := fix]] (the standard unrolling used in
      incorrectness reasoning): [fix v] and [unfold v] step to the same term.
      Proved sound for EVERY target type in
      [ExtendedRuleSoundness.ext_fix_unroll_named_sound_ext]
      ([fix_unroll_shape_ext_all]).  [lc_tm body] is needed: a dangling bound
      variable would be captured by different binders in the fix value and in
      its unfolding. *)
  | EXT_FixUnrollNamed Γ (self arg : atom) (sx t : ty) body τ :
      lc_tm body ->
      Σ; Γ ⊢wf ret (fixfun_named self arg sx t body) ⋮ τ ->
      Σ; Γ ⊢ₓ
        ret (lam_named arg sx
          (tm_subst self (fixfun_named self arg sx t body) body)) ⋮ τ ->
      Σ; Γ ⊢ₓ ret (fixfun_named self arg sx t body) ⋮ τ

  (** T-Sub *)
  | EXT_Sub Γ e τ1 τ2 :
      Σ; Γ ⊢wf e ⋮ τ2 ->
      Σ; Γ ⊢ₓ e ⋮ τ1 ->
      sub_type_under Σ Γ τ1 τ2 ->
      Σ; Γ ⊢ₓ e ⋮ τ2

  (** T-CtxSub *)
  | EXT_CtxSub Γ1 Γ2 e τ :
      Σ; Γ1 ⊢wf e ⋮ τ ->
      Σ; Γ2 ⊢ₓ e ⋮ τ ->
      ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 ->
      Σ; Γ1 ⊢ₓ e ⋮ τ

  (** T-PersistIntro *)
  | EXT_PersistIntro Γ v τ :
      Σ; Γ ⊢wf ret v ⋮ (□ τ) ->
      persistent_formula (ctx_denote_under Σ Γ) ->
      Σ; Γ ⊢ₓ ret v ⋮ τ ->
      Σ; Γ ⊢ₓ ret v ⋮ (□ τ)

  (** T-Let *)
  | EXT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      Σ; Γ ⊢wf let: e1 in e2 ⋮ τ2 ->
      Σ; Γ ⊢ₓ e1 ⋮ τ1 ->
      (forall x, x ∉ L ->
        Σ; (Γ ,, (x ∷ τ1)) ⊢ₓ (e2 ^^ x) ⋮ τ2) ->
      Σ; Γ ⊢ₓ let: e1 in e2 ⋮ τ2

  (** T-LetD *)
  | EXT_LetD Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      Σ; Γ1 ∗ Γ2 ⊢wf let: e1 in e2 ⋮ τ2 ->
      Σ; Γ1 ⊢ₓ e1 ⋮ τ1 ->
      (forall x, x ∉ L ->
        Σ; (Γ2 ∗ (x ∷ τ1)) ⊢ₓ (e2 ^^ x) ⋮ τ2) ->
      Σ; Γ1 ∗ Γ2 ⊢ₓ let: e1 in e2 ⋮ τ2

  (** T-Lam *)
  | EXT_Lam Γ τx τ e (L : aset) :
      Σ; Γ ⊢wf ret (λ: erase_ty τx, e) ⋮ (τx → τ) ->
      (forall y, y ∉ L ->
        Σ; (Γ ,, (y ∷ τx)) ⊢ₓ (e ^^ y) ⋮ ({0 ~> y} τ)) ->
      Σ; Γ ⊢ₓ ret (λ: erase_ty τx, e) ⋮ (τx → τ)

  (** T-LamD *)
  | EXT_LamD Γ τx τ e (L : aset) :
      Σ; Γ ⊢wf ret (λ: erase_ty τx, e) ⋮ (τx -∗ τ) ->
      (forall y, y ∉ L ->
        Σ; (Γ ∗ (y ∷ τx)) ⊢ₓ (e ^^ y) ⋮ ({0 ~> y} τ)) ->
      Σ; Γ ⊢ₓ ret (λ: erase_ty τx, e) ⋮ (τx -∗ τ)

  (** T-AppFun *)
  | EXT_AppFun Γ τx τ v1 (x : atom) :
      Σ; Γ ⊢wf v1 @ x ⋮ ({0 ~> x} τ) ->
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
      Σ; Γ ⊢ₓ ret v1 ⋮ (τx → τ) ->
      Σ; Γ ⊢ₓ ret (avar x) ⋮ τx ->
      Σ; Γ ⊢ₓ v1 @ x ⋮ ({0 ~> x} τ)

  (** T-AppFunD *)
  | EXT_AppFunD Γ1 Γ2 τx τ v1 (x : atom) :
      Σ; Γ1 ∗ Γ2 ⊢wf v1 @ x ⋮ ({0 ~> x} τ) ->
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
      Σ; Γ1 ⊢ₓ ret v1 ⋮ (τx -∗ τ) ->
      Σ; Γ2 ⊢ₓ ret (avar x) ⋮ τx ->
      Σ; Γ1 ∗ Γ2 ⊢ₓ v1 @ x ⋮ ({0 ~> x} τ)

  (** T-Fix *)
  | EXT_Fix Γ φx τ vf (b : base_ty) (t : ty) (L : aset) :
      erase_ty τ = t ->
      Σ; Γ ⊢wf ret (fix: (b →ᵦ t), vf) ⋮ ({: b | φx} → τ) ->
      (forall y, y ∉ L ->
        Σ; (Γ ,, (y ∷ {: b | φx})) ⊢ₓ
          ret ({0 ~> avar y} vf) ⋮
          (fix_rec_call_ty b y {: b | φx} τ → ({0 ~> y} τ))) ->
      Σ; Γ ⊢ₓ ret (fix: (b →ᵦ t), vf) ⋮ ({: b | φx} → τ)

  (** T-AppOp *)
  | EXT_AppOp Γ op (x : atom) :
      Σ; Γ ⊢wf op ·₁ x ⋮
        ({0 ~> x} (primop_result_ty (concrete_Φ op))) ->
      Σ; Γ ⊢ₓ ret (avar x) ⋮ (primop_arg_ty (concrete_Φ op)) ->
      Σ; Γ ⊢ₓ op ·₁ x ⋮
        ({0 ~> x} (primop_result_ty (concrete_Φ op)))

  (** T-AppOpValue.  Case-study precise primitive application for a general
      value argument, used for generator examples with dummy constants. *)
  | EXT_AppOpValue Γ op v :
      Σ; Γ ⊢wf op ·₁ v ⋮ (primop_precise_ty op v) ->
      Σ; Γ ⊢ₓ op ·₁ v ⋮ (primop_precise_ty op v)

  (** T-BinOp.  This rule is proof-automation-only: binary operators are not
      part of the core [primop_ctx], so the result precision is described by a
      local graph qualifier over [bin_step]. *)
  | EXT_BinOp Γ op v1 v2 :
      Σ; Γ ⊢wf v1 ⟨ op ⟩ v2 ⋮ (binop_precise_ty op v1 v2) ->
      Σ; Γ ⊢ₓ v1 ⟨ op ⟩ v2 ⋮ (binop_precise_ty op v1 v2)

  | EXT_BinOpTop Γ op v1 v2 :
      Σ; Γ ⊢wf v1 ⟨ op ⟩ v2 ⋮ (binop_top_ty op) ->
      Σ; Γ ⊢ₓ v1 ⟨ op ⟩ v2 ⋮ (binop_top_ty op)

  (** T-TreeNode *)
  | EXT_TreeNode Γ root left right :
      Σ; Γ ⊢wf [| root, left, right |] ⋮
        (tree_node_precise_ty root left right) ->
      Σ; Γ ⊢ₓ ret root ⋮ ONat ->
      Σ; Γ ⊢ₓ ret left ⋮ OTree ->
      Σ; Γ ⊢ₓ ret right ⋮ OTree ->
      Σ; Γ ⊢ₓ [| root, left, right |] ⋮
        (tree_node_precise_ty root left right)

  (** T-ListCons *)
  | EXT_ListCons Γ hd tl :
      Σ; Γ ⊢wf (hd ::ᵗ tl) ⋮ (list_cons_precise_ty hd tl) ->
      Σ; Γ ⊢ₓ ret hd ⋮ ONat ->
      Σ; Γ ⊢ₓ ret tl ⋮ OList ->
      Σ; Γ ⊢ₓ (hd ::ᵗ tl) ⋮ (list_cons_precise_ty hd tl)

  (** T-MatchBoth *)
  | EXT_MatchBoth Γt Γf x τt τf et ef :
      Σ; Γt ⊕ Γf ⊢wf if avar x then et else ef ⋮ (τt ⊕ τf) ->
      Σ; Γt ⊢ₓ ret (avar x) ⋮ (bool_precise_ty true) ->
      Σ; Γf ⊢ₓ ret (avar x) ⋮ (bool_precise_ty false) ->
      Σ; Γt ⊢ₓ et ⋮ τt ->
      Σ; Γf ⊢ₓ ef ⋮ τf ->
      Σ; Γt ⊕ Γf ⊢ₓ if avar x then et else ef ⋮ (τt ⊕ τf)

  (** T-MatchTrueOnly *)
  | EXT_MatchTrueOnly Γ x τ et ef :
      Σ; Γ ⊢wf if avar x then et else ef ⋮ τ ->
      Σ; Γ ⊢ₓ ret (avar x) ⋮ (bool_precise_ty true) ->
      Σ; Γ ⊢ₓ et ⋮ τ ->
      Σ; Γ ⊢ₓ if avar x then et else ef ⋮ τ

  (** T-MatchFalseOnly *)
  | EXT_MatchFalseOnly Γ x τ et ef :
      Σ; Γ ⊢wf if avar x then et else ef ⋮ τ ->
      Σ; Γ ⊢ₓ ret (avar x) ⋮ (bool_precise_ty false) ->
      Σ; Γ ⊢ₓ ef ⋮ τ ->
      Σ; Γ ⊢ₓ if avar x then et else ef ⋮ τ

  (** T-TreeMatch.  These rules mirror the paper's constructor-pattern match
      rule, specialized to the current two-constructor tree language. *)
  | EXT_TreeMatchBoth Γleaf Γnode v τleaf τnode eleaf enode (L : aset) :
      Σ; Γleaf ⊕ Γnode ⊢wf
        matchTree v with Leaf => eleaf | Node => enode ⋮ (τleaf ⊕ τnode) ->
      Σ; Γleaf ⊢ₓ ret Leaf ⋮
        (tree_match_eq_ty v) ->
      (forall root left right,
        root ∉ L -> left ∉ L ∪ {[root]} ->
        right ∉ L ∪ {[root]} ∪ {[left]} ->
        Σ; (Γnode ,, tree_node_pattern_ctx root left right) ⊢ₓ
          [| avar root, avar left, avar right |] ⋮
          (tree_match_eq_ty v)) ->
      Σ; Γleaf ⊢ₓ eleaf ⋮ τleaf ->
      (forall root left right,
        root ∉ L -> left ∉ L ∪ {[root]} ->
        right ∉ L ∪ {[root]} ∪ {[left]} ->
        Σ; (Γnode ,, tree_node_pattern_ctx root left right) ⊢ₓ
          (open_tree_node_branch root left right enode) ⋮ τnode) ->
      Σ; Γleaf ⊕ Γnode ⊢ₓ
        matchTree v with Leaf => eleaf | Node => enode ⋮ (τleaf ⊕ τnode)

  | EXT_TreeMatchLeafOnly Γ v τ eleaf enode :
      Σ; Γ ⊢wf matchTree v with Leaf => eleaf | Node => enode ⋮ τ ->
      Σ; Γ ⊢ₓ ret Leaf ⋮
        (tree_match_eq_ty v) ->
      Σ; Γ ⊢ₓ eleaf ⋮ τ ->
      Σ; Γ ⊢ₓ matchTree v with Leaf => eleaf | Node => enode ⋮ τ

  | EXT_TreeMatchNodeOnly Γ v τ eleaf enode (L : aset) :
      Σ; Γ ⊢wf matchTree v with Leaf => eleaf | Node => enode ⋮ τ ->
      (forall root left right,
        root ∉ L -> left ∉ L ∪ {[root]} ->
        right ∉ L ∪ {[root]} ∪ {[left]} ->
        Σ; (Γ ,, tree_node_pattern_ctx root left right) ⊢ₓ
          [| avar root, avar left, avar right |] ⋮
          (tree_match_eq_ty v)) ->
      (forall root left right,
        root ∉ L -> left ∉ L ∪ {[root]} ->
        right ∉ L ∪ {[root]} ∪ {[left]} ->
        Σ; (Γ ,, tree_node_pattern_ctx root left right) ⊢ₓ
          (open_tree_node_branch root left right enode) ⋮ τ) ->
      Σ; Γ ⊢ₓ matchTree v with Leaf => eleaf | Node => enode ⋮ τ

  (** T-ListMatch.  The cons branch binds [hd] then [tl]. *)
  | EXT_ListMatchBoth Γnil Γcons v τnil τcons enil econs (L : aset) :
      Σ; Γnil ⊕ Γcons ⊢wf
        matchList v with Nil => enil | Cons => econs ⋮ (τnil ⊕ τcons) ->
      Σ; Γnil ⊢ₓ ret Nil ⋮
        (list_match_eq_ty v) ->
      (forall hd tl,
        hd ∉ L -> tl ∉ L ∪ {[hd]} ->
        Σ; (Γcons ,, list_cons_pattern_ctx hd tl) ⊢ₓ
          (avar hd ::ᵗ avar tl) ⋮ (list_match_eq_ty v)) ->
      Σ; Γnil ⊢ₓ enil ⋮ τnil ->
      (forall hd tl,
        hd ∉ L -> tl ∉ L ∪ {[hd]} ->
        Σ; (Γcons ,, list_cons_pattern_ctx hd tl) ⊢ₓ
          (open_list_cons_branch hd tl econs) ⋮ τcons) ->
      Σ; Γnil ⊕ Γcons ⊢ₓ
        matchList v with Nil => enil | Cons => econs ⋮ (τnil ⊕ τcons)

  | EXT_ListMatchNilOnly Γ v τ enil econs :
      Σ; Γ ⊢wf matchList v with Nil => enil | Cons => econs ⋮ τ ->
      Σ; Γ ⊢ₓ ret Nil ⋮
        (list_match_eq_ty v) ->
      Σ; Γ ⊢ₓ enil ⋮ τ ->
      Σ; Γ ⊢ₓ matchList v with Nil => enil | Cons => econs ⋮ τ

  | EXT_ListMatchConsOnly Γ v τ enil econs (L : aset) :
      Σ; Γ ⊢wf matchList v with Nil => enil | Cons => econs ⋮ τ ->
      (forall hd tl,
        hd ∉ L -> tl ∉ L ∪ {[hd]} ->
        Σ; (Γ ,, list_cons_pattern_ctx hd tl) ⊢ₓ
          (avar hd ::ᵗ avar tl) ⋮ (list_match_eq_ty v)) ->
      (forall hd tl,
        hd ∉ L -> tl ∉ L ∪ {[hd]} ->
        Σ; (Γ ,, list_cons_pattern_ctx hd tl) ⊢ₓ
          (open_list_cons_branch hd tl econs) ⋮ τ) ->
      Σ; Γ ⊢ₓ matchList v with Nil => enil | Cons => econs ⋮ τ

where "Σ ';' Γ '⊢ₓ' e '⋮' τ" :=
  (has_extended_context_type Σ Γ e τ).

#[global] Hint Constructors has_extended_context_type : core.

Lemma extended_typing_wf_under Σ Γ e τ :
  Σ; Γ ⊢ₓ e ⋮ τ ->
  context_typing_wf Σ Γ e τ.
Proof. induction 1; assumption. Qed.

Lemma extended_typing_wf Γ e τ :
  ∅; Γ ⊢ₓ e ⋮ τ ->
  context_typing_wf ∅ Γ e τ.
Proof.
  intros Hty.
  exact (extended_typing_wf_under ∅ Γ e τ Hty).
Qed.

Lemma typing_to_extended_typing Σ Γ e τ :
  has_context_type concrete_Φ Σ Γ e τ ->
  Σ; Γ ⊢ₓ e ⋮ τ.
Proof.
  induction 1; eauto using has_extended_context_type.
Qed.

Lemma extended_typing_erase Σ Γ e τ :
  Σ; Γ ⊢ₓ e ⋮ τ ->
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hty.
  exact (context_typing_wf_basic_typing Σ Γ e τ
    (extended_typing_wf_under Σ Γ e τ Hty)).
Qed.
