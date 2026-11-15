import «section 5».RVRectangleDecompositionExistence
import IntegrationSection6.GammaWitnessUniformity

/-! Saturation selects finitely many complete rectangle packages over
the original real/Gamma ground, before any VF preparation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}

theorem rv_rectangle_finite_catalog
    (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (D : GammaDomainFormula B p a sp) :
    ∃ J : Finset (RVRectangleDecompositionSchema D), ∀ z ∈ A, ∃ W ∈ J, W.Valid hc z := by
  exact gamma_finite_witnesses hκ hs hr hγ sp A hA
    (fun W : RVRectangleDecompositionSchema D => {z | W.Valid hc z})
    (fun W => W.valid_definable hc) (fun z hz =>
      rv_rectangle_decomposition_schema_at_parameter hc h00 hκ hs hr hγ hΓ D z (hA.proper z hz))

end DiamondIntegral.Section5
