import «section 5».OriginalSortedPredicates
import «section 5».NativeGammaRelationSyntax
import «section 5».OriginalPredicateSyntax

/-! Full quotient-domain validity is a genuine original-base predicate.
Both sortedness and invariance of every nonzero value-code row are checked. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n : ℕ} {sp : Fin p → SortTag}

 theorem OriginalSortedPredicate.parameter_free (hc : CanonicalStructure.IsCanonical (M := M))
    {s : Fin n → SortTag} (φ : LRV.Formula (Fin n)) :
    OriginalSortedPredicate B s (fun x => φ.Realize x) :=
  parameter_free_formula_original_definable hc B s φ

theorem original_domain_nonzero_validity_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : GammaDomainFormula B p n sp) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ x : Fin n → M, Fin.append z x ∈ D.val → Proper x} := by
  let U := (nativeGammaRelationSyntax hc).proper
  let φ : LRV.Formula (Fin (p+n)) := tupleProperFormula U (Fin.natAdd p)
  have hφ : OriginalSortedPredicate B (Fin.append sp (fun _ : Fin n => .rv))
      (fun w => ∀ i : Fin n, NonzeroRV (w (Fin.natAdd p i))) := by
    apply (OriginalSortedPredicate.parameter_free hc φ).congr
    intro w hw
    rw [tupleProperFormula_realize]
    exact forall_congr' (fun i => (nativeGammaRelationSyntax hc).proper_realize _)
  have h := ((OriginalSortedPredicate.of_definable D.property).impl hφ).all
  unfold OriginalSortedPredicate at h
  convert h using 1
  ext z
  change (_ ∧ ∀ x, Fin.append z x ∈ D.val → Proper x) ↔
    (_ ∧ ∀ x, x ∈ sortedUniverse (fun _ : Fin n => .rv) →
      Fin.append z x ∈ D.val → ∀ i, NonzeroRV ((Fin.append z x) (Fin.natAdd p i)))
  simp only [Fin.append_right]
  constructor
  · exact fun hz => ⟨hz.1, fun x _ hx => hz.2 x hx⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun x hx => h x
      (fun i => by simpa only [Fin.append_right] using D.property.proper _ hx (Fin.natAdd p i)) hx⟩

theorem original_domain_value_invariance_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : GammaDomainFormula B p n sp) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ x y : Fin n → M, Proper x → Proper y →
        (codeValue ∘ x = codeValue ∘ y) →
          (Fin.append z x ∈ D.val ↔ Fin.append z y ∈ D.val)} := by
  let rv : Fin n → SortTag := fun _ => .rv
  let s : Fin (p+(n+n)) → SortTag := Fin.append sp (Fin.append rv rv)
  let left : Fin (p+n) → Fin (p+(n+n)) :=
    Fin.append (Fin.castAdd (n+n)) (fun i => Fin.natAdd p (Fin.castAdd n i))
  let right : Fin (p+n) → Fin (p+(n+n)) :=
    Fin.append (Fin.castAdd (n+n)) (fun i => Fin.natAdd p (Fin.natAdd n i))
  have hleft : ∀ i, Fin.append sp rv i = s (left i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [s, left, Fin.append_left, Fin.append_right, rv]
  have hright : ∀ i, Fin.append sp rv i = s (right i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [s, right, Fin.append_left, Fin.append_right, rv]
  let U := (nativeGammaRelationSyntax hc).proper
  let E := (nativeGammaRelationSyntax hc).equal
  let φ : LRV.Formula (Fin (p+(n+n))) :=
    tupleProperFormula U (fun i : Fin n => Fin.natAdd p (Fin.castAdd n i)) ⊓
    tupleProperFormula U (fun i : Fin n => Fin.natAdd p (Fin.natAdd n i)) ⊓
    tupleQuotientEqualityFormula E
      (fun i : Fin n => Fin.natAdd p (Fin.castAdd n i))
      (fun i : Fin n => Fin.natAdd p (Fin.natAdd n i))
  have h0 : OriginalSortedPredicate B s (fun w => φ.Realize w) :=
    OriginalSortedPredicate.parameter_free hc φ
  have h := (h0.impl (((OriginalSortedPredicate.of_definable D.property).pullback left hleft).iff
    ((OriginalSortedPredicate.of_definable D.property).pullback right hright))).all
  unfold OriginalSortedPredicate at h
  convert h using 1
  ext z
  change (_ ∧ ∀ x y, Proper x → Proper y → _ → _) ↔
    (_ ∧ ∀ v, v ∈ sortedUniverse (Fin.append rv rv) →
      φ.Realize (Fin.append z v) →
        ((Fin.append z v ∘ left) ∈ D.val ↔ (Fin.append z v ∘ right) ∈ D.val))
  have hdecode (v : Fin (n+n) → M) :
      φ.Realize (Fin.append z v) ↔
      Proper (v ∘ Fin.castAdd n) ∧ Proper (v ∘ Fin.natAdd n) ∧
        codeValue ∘ (v ∘ Fin.castAdd n) = codeValue ∘ (v ∘ Fin.natAdd n) := by
    simp only [φ, Formula.realize_inf, tupleProperFormula_realize,
      tupleQuotientEqualityFormula_realize, Fin.append_right]
    simp_rw [U, (nativeGammaRelationSyntax hc).proper_realize]
    dsimp only [E]
    constructor
    · rintro ⟨⟨hx, hy⟩, he⟩
      change (∀ i, NonzeroRV ((v ∘ Fin.castAdd n) i)) at hx
      change (∀ i, NonzeroRV ((v ∘ Fin.natAdd n) i)) at hy
      exact ⟨hx, hy, funext (fun i =>
        ((nativeGammaRelationSyntax hc).equal_realize _ _ (hx i) (hy i)).mp (he i))⟩
    · rintro ⟨hx, hy, he⟩
      exact ⟨⟨hx, hy⟩, fun i =>
        ((nativeGammaRelationSyntax hc).equal_realize _ _ (hx i) (hy i)).mpr (congrFun he i)⟩
  have hl (v : Fin (n+n) → M) :
      Fin.append z v ∘ left = Fin.append z (v ∘ Fin.castAdd n) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Function.comp_apply, left, Fin.append_left, Fin.append_right]
  have hr (v : Fin (n+n) → M) :
      Fin.append z v ∘ right = Fin.append z (v ∘ Fin.natAdd n) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Function.comp_apply, right, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨hz, hinv⟩
    refine ⟨hz, fun v _ hv => ?_⟩
    obtain ⟨hx, hy, he⟩ := (hdecode v).mp hv
    rw [hl, hr]
    exact hinv _ _ hx hy he
  · rintro ⟨hz, hinv⟩
    refine ⟨hz, fun x y hx hy he => ?_⟩
    have hs : Fin.append x y ∈ sortedUniverse (Fin.append rv rv) := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left, rv, sortEval, iRV] using (hx j).1
      · simpa only [Fin.append_right, rv, sortEval, iRV] using (hy j).1
    have hv : φ.Realize (Fin.append z (Fin.append x y)) := by
      apply (hdecode _).mpr
      simpa only [Function.comp_def, Fin.append_left, Fin.append_right] using And.intro hx (And.intro hy he)
    have hh := hinv (Fin.append x y) hs hv
    rw [hl, hr] at hh
    simpa only [Function.comp_def, Fin.append_left, Fin.append_right] using hh

theorem original_quotient_domain_validity_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : GammaDomainFormula B p n sp) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      (quotientDomainValidityFormula (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (gammaDomainSyntax hc B D)).Realize
          (predicateParameterValues B z)} := by
  have he (z : Fin p → M) :
      (quotientDomainValidityFormula (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (gammaDomainSyntax hc B D)).Realize
          (predicateParameterValues B z) ↔
      (∀ x : Fin n → M, Fin.append z x ∈ D.val → Proper x) ∧
      ∀ x y : Fin n → M, Proper x → Proper y → codeValue ∘ x = codeValue ∘ y →
        (Fin.append z x ∈ D.val ↔ Fin.append z y ∈ D.val) := by
    rw [quotientDomainValidityFormula_realize]
    simp_rw [gammaDomainSyntax_realize, (nativeGammaRelationSyntax hc).proper_realize]
    apply and_congr_right
    intro _
    constructor
    · intro h x y hx hy hq
      apply h x y hx hy
      intro i
      exact ((nativeGammaRelationSyntax hc).equal_realize _ _ (hx i) (hy i)).mpr (congrFun hq i)
    · intro h x y hx hy hq
      apply h x y hx hy
      exact funext (fun i =>
        ((nativeGammaRelationSyntax hc).equal_realize _ _ (hx i) (hy i)).mp (hq i))
  have h := (original_domain_nonzero_validity_definable hc D).inter
    (original_domain_value_invariance_definable hc D)
  convert h using 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, he]
  tauto

end DiamondIntegral.Section5
