import «section 3».RVGenericFamilyCoefficients
import «section 3».RVGenericResidueFold
import «section 3».ResidueGenericExistence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- A single actual residue generic tests a finite family and every
intermediate selector simultaneously. No extra names enter the output. -/
theorem exists_rvGeneric_family_test_point {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) {n : ℕ} {ι : Type} [Finite ι]
    (A : ι → Set (Fin n → M)) (hA : ∀ j, DefinableOverBase B (fun _ => .rv) (A j))
    (a : ι → Fin n → (CanonicalRV.RVSort M)ˣ) (L : List (Fin n)) :
    ∃ E : Subfield (ModelResidue M), ∃ x : Fin n → ModelResidue M,
      Cardinal.mk E ≤ Cardinal.aleph0 ∧ IsAlgClosed E ∧ AlgebraicIndependent E x ∧
      (∀ i, x i ≠ 0) ∧ ∀ j,
        (rvNormalizedTuple (a j) x ∈ L.foldl rvGenericCoordinate (A j) ↔
          rvNormalizedTuple (a j) x ∈ A j) := by
  obtain ⟨E,hE,hclosed,hER⟩ := rvGeneric_family_countable_coefficients hc hκ.le hs h00 B hsmall A hA a L
  obtain ⟨x,hx⟩ := exists_residue_generic_over_countable hc hκ hs h00 E hE n
  letI : CharZero (ModelResidue M) := rvResidueField_charZero h00
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  refine ⟨E,x,hE,hclosed,hx,algebraicallyIndependent_coordinate_ne_zero E x hx,?_⟩
  intro j
  exact rvGenericCoordinate_fold_at_residue_generic hc hs h00 B hsmall
    (A j) (hA j) (a j) E L (hER j) x hx

end DiamondIntegral.Section3
