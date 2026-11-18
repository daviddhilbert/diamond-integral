import «section 3».GammaGroundRVBaseReduction
import «section 3».GammaGroundMeasuredRVCoproducts
import «section 3».GammaNativeElementaryLocalComparison
import IntegrationSection6.GammaFieldBaseReduction

/-! Original-base descent keeps genuine coproducts and preserves the
algebraic center condition of each actual measured elementary operation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)} {k : ℕ}

theorem gammaGroundRVReduceObject_coprod (H : GammaDefinableBaseReduction C B)
    (U V : GammaGroundRVObject hc C k) :
    gammaGroundRVReduceObject H (U.coprod V) =
      (gammaGroundRVReduceObject H U).coprod (gammaGroundRVReduceObject H V) := by
  rfl

theorem gammaGroundMeasuredRVReduceObject_coprod (H : GammaDefinableBaseReduction C B)
    (U V : GammaGroundMeasuredRVObject hc C k) :
    gammaGroundMeasuredRVReduceObject H (U.coprod V) =
      (gammaGroundMeasuredRVReduceObject H U).coprod (gammaGroundMeasuredRVReduceObject H V) := by
  rfl

theorem gammaGroundRVReduceObject_admissible (H : GammaDefinableBaseReduction C B)
    (U : GammaGroundRVObject hc C k) (i : Fin k)
    (hAd : GammaAdmissible (Section5.groundRVAt U).toGamma.toGammaRVObject i) :
    GammaAdmissible (Section5.groundRVAt (gammaGroundRVReduceObject H U)).toGamma.toGammaRVObject i := by
  let V := gammaGroundRVReduceObject H U
  let A := Section5.groundRVAt V
  let D := Section5.groundRVAt U
  let f (u : rvObjectDomain A.object.obj) :=
    Section5.groundRVAtDomainEquiv U ((Section5.groundRVAtDomainEquiv V).symm u)
  have hVolume (u : rvObjectDomain A.object.obj) :
      gammaVolumeValue A.toGamma.toGammaRVObject u = gammaVolumeValue D.toGamma.toGammaRVObject (f u) := by
    have hNew := Section5.groundRVAt_volume_eq V u
    have hOld := Section5.groundRVAt_volume_eq U (f u)
    exact hNew.trans hOld.symm
  constructor
  · intro u
    rw [hVolume u]
    exact hAd.nonzero (f u)
  · intro u
    rw [hVolume u]
    exact H.coordinate_algebraic i (gammaVolumeValue D.toGamma.toGammaRVObject (f u)) _ (hAd.algebraic (f u))

end DiamondIntegral.Section3
