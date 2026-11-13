import «section 3».GammaGroundZeroRVLift
import «section 3».GammaGroundMeasuredVFZero
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

@[simp] theorem GammaGroundMeasuredRVObject.zero_combinedWeight
    (U : GammaGroundMeasuredRVObject hc B 0) (a : U.underlying.domain) :
    U.combinedWeight a = gammaGroundFormValue U.form a := by
  simp [GammaGroundMeasuredRVObject.combinedWeight]

/-- In degree zero the actual measured lift transports the entire form
along the empty-VF-tuple bijection. -/
def gammaGroundZeroMeasuredRVLiftHom {U V : GammaGroundMeasuredRVObject hc B 0}
    (f : U ⟶ V) : gammaGroundMeasuredObjectLift U ⟶ gammaGroundMeasuredObjectLift V where
  bijection := (gammaGroundZeroRVLiftBijection V.underlying).symm.comp
    (f.bijection.comp (gammaGroundZeroRVLiftBijection U.underlying))
  preserves a := by
    have h := f.preserves ((gammaGroundZeroRVLiftBijection U.underlying).map a)
    simp only [GammaGroundMeasuredRVObject.zero_combinedWeight] at h
    change gammaGroundFormValue U.form ((gammaGroundZeroRVLiftBijection U.underlying).map a) =
      gammaGroundFormValue V.form
        ((gammaGroundZeroRVLiftBijection V.underlying).map
          ((gammaGroundZeroRVLiftBijection V.underlying).map.inverse _
            (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map a))))
    simpa only [GammaGroundMap.apply_inverse] using h

def gammaGroundZeroMeasuredRVToVF :
    GammaGroundMeasuredRVObject hc B 0 ⥤ GammaGroundZeroMeasuredVF hc B where
  obj := gammaGroundMeasuredObjectLift
  map := gammaGroundZeroMeasuredRVLiftHom
  map_id U := by
    apply GammaGroundZeroMeasuredVFHom.ext
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro a
    exact (gammaGroundZeroRVLiftBijection U.underlying).map.inverse_apply _ a
  map_comp {U V W} f g := by
    apply GammaGroundZeroMeasuredVFHom.ext
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro a
    change (gammaGroundZeroRVLiftBijection W.underlying).map.inverse _
      (g.bijection.map (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map a))) =
      (gammaGroundZeroRVLiftBijection W.underlying).map.inverse _ (g.bijection.map
        ((gammaGroundZeroRVLiftBijection V.underlying).map
          ((gammaGroundZeroRVLiftBijection V.underlying).map.inverse _
            (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map a)))))
    exact congrArg (fun u => (gammaGroundZeroRVLiftBijection W.underlying).map.inverse _ (g.bijection.map u))
      ((gammaGroundZeroRVLiftBijection V.underlying).map.apply_inverse _ _).symm

instance gammaGroundZeroMeasuredRVToVF_faithful :
    (gammaGroundZeroMeasuredRVToVF (hc := hc) (B := B)).Faithful where
  map_injective {U V} f g he := by
    apply GammaGroundMeasuredRVHom.ext
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro u
    have h := congrArg (fun f : gammaGroundMeasuredObjectLift U ⟶ gammaGroundMeasuredObjectLift V =>
      (gammaGroundZeroRVLiftBijection V.underlying).map
        (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).symm.map u))) he
    change (gammaGroundZeroRVLiftBijection V.underlying).map
      ((gammaGroundZeroRVLiftBijection V.underlying).map.inverse _
        (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map
          ((gammaGroundZeroRVLiftBijection U.underlying).map.inverse _ u)))) =
      (gammaGroundZeroRVLiftBijection V.underlying).map
      ((gammaGroundZeroRVLiftBijection V.underlying).map.inverse _
        (g.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map
          ((gammaGroundZeroRVLiftBijection U.underlying).map.inverse _ u)))) at h
    simpa only [GammaGroundMap.apply_inverse] using h

/-- Every genuine pointwise form-preserving map between degree-zero
lifts descends to the same original-ground measured RV map. -/
def gammaGroundZeroMeasuredRVPreimage {U V : GammaGroundMeasuredRVObject hc B 0}
    (f : gammaGroundMeasuredObjectLift U ⟶ gammaGroundMeasuredObjectLift V) : U ⟶ V where
  bijection := (gammaGroundZeroRVLiftBijection V.underlying).comp
    (f.bijection.comp (gammaGroundZeroRVLiftBijection U.underlying).symm)
  preserves a := by
    simp only [GammaGroundMeasuredRVObject.zero_combinedWeight]
    have h := f.preserves ((gammaGroundZeroRVLiftBijection U.underlying).symm.map a)
    change gammaGroundFormValue U.form
      ((gammaGroundZeroRVLiftBijection U.underlying).map
        ((gammaGroundZeroRVLiftBijection U.underlying).map.inverse _ a)) =
      gammaGroundFormValue V.form ((gammaGroundZeroRVLiftBijection V.underlying).map
        (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map.inverse _ a))) at h
    change gammaGroundFormValue U.form a =
      gammaGroundFormValue V.form ((gammaGroundZeroRVLiftBijection V.underlying).map
        (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map.inverse _ a)))
    simpa only [GammaGroundMap.apply_inverse] using h

instance gammaGroundZeroMeasuredRVToVF_full :
    (gammaGroundZeroMeasuredRVToVF (hc := hc) (B := B)).Full where
  map_surjective {U V} f := by
    refine ⟨gammaGroundZeroMeasuredRVPreimage f,?_⟩
    apply GammaGroundZeroMeasuredVFHom.ext
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro a
    change (gammaGroundZeroRVLiftBijection V.underlying).map.inverse _
      ((gammaGroundZeroRVLiftBijection V.underlying).map
        (f.bijection.map ((gammaGroundZeroRVLiftBijection U.underlying).map.inverse _
          ((gammaGroundZeroRVLiftBijection U.underlying).map a)))) = f.bijection.map a
    simp only [GammaGroundMap.inverse_apply]
end DiamondIntegral.Section3
