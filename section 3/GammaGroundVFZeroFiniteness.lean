import «section 3».GammaGroundVFCategories
import «section 3».GammaGroundRealization
import «section 3».VFDimensionComparison
import Section4.VFFiniteMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

/-- Every degree-zero VF object has a genuinely finite mixed domain.
Temporary Gamma-code realization is used only for this intrinsic finite
cardinality fact, not to descend a map over the enlarged real base. -/
theorem GammaGroundVFObject.degree_zero_finite
    (U : GammaGroundVFObject hc B 0)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    U.domain.carrier.Finite := by
  obtain ⟨T,_,hT,_,hdef⟩ := U.domain.definable.realize hκ hsmall
  let A : DefSet (rawMixedSpace (M := M) U.vfArity U.rvArity) T := ⟨U.domain.carrier,hdef⟩
  have hd : vfDim (rawRVSpace 1) A ≤ 0 :=
    (vfDimension_le_iff_companion hc hs hT hv A 0).mp U.dimension
  obtain ⟨f,hf⟩ := finite_map_to_vf_of_dimension_and_finite_rv_fibres hc hκ hs hT
    (rawRVSpace 1) (rawRVSpace_rvCoded 1) A hd U.finite
  apply f.finite_source_of_finite_image hf
  exact Set.Subsingleton.finite (fun a _ b _ => funext (fun i => i.elim0))
end DiamondIntegral.Section3
