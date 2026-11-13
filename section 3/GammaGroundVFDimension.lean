import «section 3».GammaGroundRealization
import «section 3».VFDimensionComparison

/-! The intrinsic VF dimension can be checked using the original real
coefficient field even when the set uses additional Gamma names. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaGroundVFDimension_le_iff_point_rank {n r : ℕ}
    {A : Set (rawMixedSpace (M := M) n r).Carrier}
    (hA : GammaGroundDefinable hc ground (rawMixedSpace n r) A)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (k : ℕ) :
    Section2.vfDimension A ≤ (k : WithBot ℕ) ↔
      ∀ a ∈ A, vfTupleTrdeg ground.real a.1 ≤ (k : Cardinal) := by
  obtain ⟨T, hT, hsmall, hfield, hdef⟩ := hA.realize hκ hS
  let D : DefSet (rawMixedSpace (M := M) n r) T := ⟨A, hdef⟩
  have h := (vfDimension_le_iff_companion hc hs hsmall hv D k).trans
    (vfDim_le_iff_point_trdeg hc hs hsmall (rawRVSpace 1) (rawRVSpace_rvCoded 1) D k)
  change Section2.vfDimension A ≤ (k : WithBot ℕ) ↔ _ at h
  rw [show (∀ a : D, vfTupleTrdeg T a.val.1 ≤ (k : Cardinal)) ↔
      ∀ a ∈ A, vfTupleTrdeg ground.real a.1 ≤ (k : Cardinal) from ?_] at h
  · exact h
  · simp only [vfTupleTrdeg, hfield]
    exact Subtype.forall

end DiamondIntegral.Section3
