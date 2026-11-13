import «section 3».GammaGroundAngularCoefficientPoints
import «section 3».GammaGroundPointUniformization
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- A definable singleton RV tuple has each actual scalar coordinate in
the definable closure of precisely the original mixed ground. -/
theorem gammaGroundRVUnitTuple_point_definable_iff
    (c : Fin n → (CanonicalRV.RVSort M)ˣ) :
    GammaGroundDefinable hc B (rawRVUnitSpace n) {c} ↔
      ∀ i, DefinableClosureAtBase B .rv (rvUnitValues c i) := by
  constructor
  · intro hcdef
    let Q : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := ⟨{c},hcdef⟩
    letI : Subsingleton Q := ⟨by
      intro a b
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp a.property).trans (Set.mem_singleton_iff.mp b.property).symm⟩
    exact gammaGroundRVUnitMap_subsingleton_image_point_definable Q
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n))
      (GammaGroundMap.id Q).toUniv ⟨c,Set.mem_singleton c⟩
  · exact gammaGroundRVUnitTuple_point_definable c

end DiamondIntegral.Section3
