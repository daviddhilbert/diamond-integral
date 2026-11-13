import «section 3».ValueCharacterTwistTerms
import Section3.QuantifierFree
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

/-- Quantifier-free sorted formulas are preserved by the actual
character twist on RV and identity on the old VF definable closure. -/
theorem rvCharacterPair_qf {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (v w : α → M) (xs ys : Fin n → M)
    (hv : ∀ a, RVCharacterPair B χ (sα a) (v a) (w a))
    (hx : ∀ i, RVCharacterPair B χ (sn i) (xs i) (ys i))
    (φ : LRV.BoundedFormula α n) (hφ : φ.IsQF) (hw : WellSorted sα sn φ) :
    φ.Realize v xs ↔ φ.Realize w ys := by
  induction hφ with
  | falsum => rfl
  | of_isAtomic ha =>
    cases ha with
    | equal t u =>
      cases hw with
      | @equal _ _ _ _ σ ht hu =>
        exact rvCharacterPair_equal B χ
          (rvCharacterPair_term B χ sα sn v w xs ys hv hx t σ ht)
          (rvCharacterPair_term B χ sα sn v w xs ys hv hx u σ hu)
    | rel R ts =>
      cases hw with
      | rel _ _ _ hts =>
        exact rvCharacterPair_relation B χ R _ _
          (fun i => rvCharacterPair_term B χ sα sn v w xs ys hv hx (ts i) _ (hts i))
  | imp _ _ ihφ ihψ =>
    cases hw with
    | imp _ hwφ hwψ =>
      exact imp_congr (ihφ hwφ) (ihψ hwψ)

/-- The same preservation holds for all well-sorted formulas by the
released ACVF quantifier-elimination theorem. -/
theorem rvCharacterPair_formula {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (v w : α → M) (xs ys : Fin n → M)
    (hv : ∀ a, RVCharacterPair B χ (sα a) (v a) (w a))
    (hx : ∀ i, RVCharacterPair B χ (sn i) (xs i) (ys i))
    (φ : LRV.BoundedFormula α n) (hw : WellSorted sα sn φ) :
    φ.Realize v xs ↔ φ.Realize w ys := by
  have hsort {σ : SortTag} {u v : M} (h : RVCharacterPair B χ σ u v) :
      sortEval σ u ∧ sortEval σ v := by
    cases σ with
    | vf => obtain ⟨a,rfl,rfl⟩ := h; exact ⟨a.val.property,a.val.property⟩
    | rv => obtain ⟨a,rfl,rfl⟩ := h; exact ⟨a.property,(rvOriginalGroundCharacterTwistZero B χ a).property⟩
  obtain ⟨ψ,hq,hwψ,he⟩ := theorem_2_3_quantifier_elimination α sα n sn φ hw
  exact (he M inferInstance v xs (fun i => (hsort (hv i)).1) (fun i => (hsort (hx i)).1)).trans
    ((rvCharacterPair_qf B χ sα sn v w xs ys hv hx ψ hq hwψ).trans
      (he M inferInstance w ys (fun i => (hsort (hv i)).2) (fun i => (hsort (hx i)).2)).symm)

end DiamondIntegral.Section3
