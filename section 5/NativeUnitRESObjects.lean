import «section 5».NativeRVSetValues

/-! A finite-value nonzero RV domain has an actual native RES object
on the same raw domain, with the canonical finite nonzero labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem unitRVPresentation_finite_values
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (hR : (rvUnitTupleValues '' R.carrier).Finite) :
    GammaRVFiniteValues hc B (gammaGroundRVUnitToRVMap R).image := by
  apply (hR.image (fun γ => fun i => (γ i).val)).subset
  rintro γ ⟨u,hu,rfl⟩
  obtain ⟨r,hr⟩ := hu
  refine ⟨rvUnitTupleValues r.val,⟨r.val,r.property,rfl⟩,?_⟩
  rw [← hr]
  rfl

def nativeRESObjectOfUnitSet
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (hR : (rvUnitTupleValues '' R.carrier).Finite) :
    GammaGroundRESObject hc B n :=
  nativeRESObjectOfGammaSet hc B (gammaGroundRVUnitToRVMap R).image (unitRVPresentation_finite_values R hR)

def nativeRESUnitSetBijection
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (hR : (rvUnitTupleValues '' R.carrier).Finite) :
    GammaGroundBijection R (nativeRESObjectOfUnitSet R hR).obj.domain :=
  gammaGroundRVUnitPresentationBijection R

end DiamondIntegral.Section5
