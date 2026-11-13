import «section 3».GammaGroundZeroMeasuredLift
import «section 3».GammaGroundZeroCategoryEquivalence
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

/-- Empty VF coordinates can be deleted by an actual same-ground
bijection. The volume form is transported in full, with no normalization. -/
theorem gammaGroundZeroMeasuredRVRepresentative (U : GammaGroundZeroMeasuredVF hc B) :
    ∃ V : GammaGroundMeasuredRVObject hc B 0, Nonempty (gammaGroundMeasuredObjectLift V ≅ U) := by
  let p : GammaGroundMap U.domain (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) U.arity)) :=
    GammaGroundMap.ofGlobal U.domain _
      (universalProductSnd (rawVFSpace 0) (rawRVSpace U.arity) B.real) (fun _ => Set.mem_univ _)
  have hp : Function.Injective p := by
    intro a b he
    apply Subtype.ext
    exact Prod.ext (funext (fun i => i.elim0)) (congrArg Subtype.val he)
  have hfin : p.image.carrier.Finite := (U.finite Fin.elim0).subset (by
    rintro t ⟨a,ha⟩
    change (Fin.elim0,t) ∈ U.domain.carrier
    have he : Fin.elim0 = a.val.1 := funext (fun i => i.elim0)
    change a.val.2 = t at ha
    rw [he,← ha]
    exact a.property)
  let e : GammaGroundBijection U.domain p.image := ⟨p.toImage,p.toImage_bijective hp⟩
  let V : GammaGroundMeasuredRVObject hc B 0 :=
    ⟨gammaGroundFiniteRVZeroObject p.image hfin,U.form.comp e.symm.map⟩
  let f : gammaGroundMeasuredObjectLift V ⟶ U :=
    ⟨e.symm.comp (gammaGroundZeroRVLiftBijection V.underlying),fun _ => rfl⟩
  exact ⟨V,⟨asIso f⟩⟩

/-- The degree-zero measured category equivalence retains arbitrary
pointwise Gamma forms and uses only genuine preserving bijections. -/
def gammaGroundZeroMeasuredRVVFEquivalence :
    GammaGroundMeasuredRVObject hc B 0 ≌ GammaGroundZeroMeasuredVF hc B := by
  let F := gammaGroundZeroMeasuredRVToVF (hc := hc) (B := B)
  letI : F.EssSurj := ⟨fun U => gammaGroundZeroMeasuredRVRepresentative U⟩
  letI : F.IsEquivalence := {}
  exact F.asEquivalence
end DiamondIntegral.Section3
