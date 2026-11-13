import «section 3».GammaGroundFiniteMixedCoding
import «section 3».GammaGroundVFZeroFiniteness
import «section 3».GammaGroundZeroRVLift
import «section 3».GammaGroundRVFamilyObjects
import Mathlib.CategoryTheory.Equivalence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

/-- A finite RV domain with its unique empty label is an RV[0] object. -/
def gammaGroundFiniteRVZeroObject {m : ℕ}
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (hD : D.carrier.Finite) :
    GammaGroundRVObject hc B 0 where
  arity := m
  domain := D
  volume := gammaGroundRVSelectCoordinates Fin.elim0 D
  finite _ := by
    let : Finite D := Set.finite_coe_iff.mpr hD
    exact Set.toFinite _
  nonzero _ i := i.elim0

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

/-- The objectwise zero-degree comparison uses a complete same-ground
bijection, not merely equality after groupification. -/
theorem gammaGroundVFZeroRVRepresentative (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundVFObject hc B 0) :
    ∃ V : GammaGroundRVObject hc B 0, Nonempty (GammaGroundBijection U.domain V.domain) := by
  have hfin := U.degree_zero_finite hκ hs hsmall hv
  obtain ⟨m,f,hf⟩ := gammaGroundFiniteMixedCodeMap h00 U.domain hfin
  let : Finite U.domain := Set.finite_coe_iff.mpr hfin
  let V := gammaGroundFiniteRVZeroObject f.image (Set.finite_range (fun a => (f a).val))
  exact ⟨V,⟨f.toImage,f.toImage_bijective hf⟩⟩

/-- The manuscript's actual equivalence VF[0] ≃ RV[0], over the complete
original Gamma ground and with the Section 2 interior dimension. -/
def gammaGroundZeroRVVFEquivalence (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    GammaGroundRVObject hc B 0 ≌ GammaGroundVFObject hc B 0 := by
  let F := gammaGroundZeroRVToVF (hc := hc) (B := B)
  letI : F.EssSurj := ⟨fun U => by
    obtain ⟨V,⟨e⟩⟩ := gammaGroundVFZeroRVRepresentative h00 hκ hs hsmall hv U
    exact ⟨V,⟨asIso (show F.obj V ⟶ U from e.symm.comp (gammaGroundZeroRVLiftBijection V))⟩⟩⟩
  letI : F.IsEquivalence := {}
  exact F.asEquivalence
end DiamondIntegral.Section3
