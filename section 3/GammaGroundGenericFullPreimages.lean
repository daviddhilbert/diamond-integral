import «section 3».GammaGroundGenericFibreTests
import «section 3».GammaGroundRVUnitProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {κ : Cardinal} {hc : CanonicalStructure.IsCanonical (M := M)}
variable (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
variable (hsmall : Cardinal.mk B.real < κ) {n : ℕ}

/-- Generic value selection is the identity on full Gamma preimages. -/
theorem gammaGroundRVGenericValueImage_full_preimage (hκ : Cardinal.aleph0 < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n))) :
    (gammaGroundRVGenericValueImage hs h00 B hsmall (gammaGroundRVUnitGammaPreimage G)).carrier = G.carrier := by
  ext γ
  obtain ⟨u,hu,hF⟩ := gammaGroundGeneric_finite_fibre_test hs h00 B hsmall hκ
    (fun _ : Unit => gammaGroundRVUnitGammaPreimage G) γ
  apply (hF ()).trans
  change rvUnitTupleValues u ∈ G.carrier ↔ γ ∈ G.carrier
  rw [hu]

end DiamondIntegral.Section3
