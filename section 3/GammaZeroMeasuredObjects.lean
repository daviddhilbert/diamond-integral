import «section 3».GammaGroundZeroMeasuredEquivalence
import «section 3».GammaGroundMeasuredVFScissors
import «section 3».GammaGroundMeasuredRVIsomorphismClasses
import «section 3».GammaGroundMapPreimages

/-! Literal degree-zero descent. The inverse presentation uses the actual
RV projection and its empty-VF-tuple inverse, and retains the entire form.
No geometric kernel input is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : GammaParameters.Base (M := M)}

def gammaZeroLabelProjection (U : GammaGroundZeroMeasuredVF hc B) :
    GammaGroundMap U.domain (GammaGroundDefSet.univ hc B (rawRVSpace U.arity)) :=
  GammaGroundMap.ofGlobal U.domain _
    (universalProductSnd (rawVFSpace 0) (rawRVSpace U.arity) B.real)
    (fun _ => Set.mem_univ _)

theorem gammaZeroLabelProjection_injective (U : GammaGroundZeroMeasuredVF hc B) :
    Function.Injective (gammaZeroLabelProjection U) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (funext (fun i => i.elim0)) (congrArg Subtype.val h)

def gammaZeroLabelBijection (U : GammaGroundZeroMeasuredVF hc B) :
    GammaGroundBijection U.domain (gammaZeroLabelProjection U).image :=
  ⟨(gammaZeroLabelProjection U).toImage,
    (gammaZeroLabelProjection U).toImage_bijective (gammaZeroLabelProjection_injective U)⟩

theorem gammaZeroLabelProjection_finite (U : GammaGroundZeroMeasuredVF hc B) :
    (gammaZeroLabelProjection U).image.carrier.Finite := by
  apply (U.finite Fin.elim0).subset
  rintro t ⟨u,hu⟩
  change (Fin.elim0,t) ∈ U.domain.carrier
  have he : Fin.elim0 = u.val.1 := funext (fun i => i.elim0)
  change u.val.2 = t at hu
  rw [he,←hu]
  exact u.property

def gammaZeroRVOfVF (U : GammaGroundZeroMeasuredVF hc B) :
    GammaGroundMeasuredRVObject hc B 0 :=
  ⟨gammaGroundFiniteRVZeroObject (gammaZeroLabelProjection U).image
      (gammaZeroLabelProjection_finite U),
    U.form.comp (gammaZeroLabelBijection U).symm.map⟩

@[simp] theorem gammaZeroRVOfVF_weight (U : GammaGroundZeroMeasuredVF hc B)
    (t : (gammaZeroRVOfVF U).underlying.domain) :
    (gammaZeroRVOfVF U).combinedWeight t =
      gammaGroundFormValue U.form ((gammaZeroLabelBijection U).symm.map t) := by
  rw [GammaGroundMeasuredRVObject.zero_combinedWeight]
  rfl

def gammaZeroRVHomOfVFHom {U V : GammaGroundZeroMeasuredVF hc B}
    (f : GammaGroundZeroMeasuredVFHom U V) :
    gammaZeroRVOfVF U ⟶ gammaZeroRVOfVF V where
  bijection := (gammaZeroLabelBijection V).comp
    (f.bijection.comp (gammaZeroLabelBijection U).symm)
  preserves t := by
    simp only [gammaZeroRVOfVF_weight]
    have h := f.preserves ((gammaZeroLabelBijection U).symm.map t)
    simpa only [GammaGroundBijection.comp, GammaGroundBijection.symm,
      GammaGroundMap.comp, GammaGroundMap.inverse_apply] using h

def gammaZeroVFRepresentationIso (U : GammaGroundZeroMeasuredVF hc B) :
    gammaGroundMeasuredObjectLift (gammaZeroRVOfVF U) ≅ U := by
  let f : gammaGroundMeasuredObjectLift (gammaZeroRVOfVF U) ⟶ U := {
    bijection := (gammaZeroLabelBijection U).symm.comp
      (gammaGroundZeroRVLiftBijection (gammaZeroRVOfVF U).underlying)
    preserves := fun _ => rfl }
  exact asIso f

def gammaZeroRVRepresentationIso (U : GammaGroundMeasuredRVObject hc B 0) :
    gammaZeroRVOfVF (gammaGroundMeasuredObjectLift U) ≅ U := by
  let f : gammaGroundMeasuredObjectLift
      (gammaZeroRVOfVF (gammaGroundMeasuredObjectLift U)) ⟶ gammaGroundMeasuredObjectLift U :=
    (gammaZeroVFRepresentationIso (gammaGroundMeasuredObjectLift U)).hom
  exact asIso (gammaGroundZeroMeasuredRVPreimage f)

end DiamondIntegral.Section3
