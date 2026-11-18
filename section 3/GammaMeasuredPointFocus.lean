import «section 3».GammaMeasuredNormalizedPoint
import «section 3».GammaElementaryClosureExistence
import «section 5».Completed18LocalLift
import IntegrationSection6.GammaBasicAdmissibility

/-! The normalized measured point has an actual original-ground focus
without choosing a real representative of a named Gamma parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem gammaMeasuredPoint_admissible : GammaAdmissible
    (Section5.groundRVAt (gammaMeasuredPointZeroArity hc B).underlying).toGamma.toGammaRVObject 0 where
  nonzero u := by
    have h := congrArg (fun z : Fin 1 → CanonicalRV.RVSort M => (z 0).val)
      (Section5.groundRVAt_volume_eq (gammaMeasuredPointZeroArity hc B).underlying u)
    change _ = iRVOne at h
    exact fun hz => RVCalc.rv_one_ne_zero (inferInstance : M ⊨ Axioms.ACVF) (h.symm.trans hz)
  algebraic u := by
    have h := congrArg (fun z : Fin 1 → CanonicalRV.RVSort M => (z 0).val)
      (Section5.groundRVAt_volume_eq (gammaMeasuredPointZeroArity hc B).underlying u)
    change (gammaVolumeValue (Section5.groundRVAt (gammaMeasuredPointZeroArity hc B).underlying).toGamma.toGammaRVObject u 0).val = iRVOne at h
    exact h.symm ▸ gamma_rv_one_algebraic _

theorem gammaMeasuredPoint_focus_exists
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B)) :
    Nonempty (ElementaryLiftDiagram
      (Section5.groundRVAt (gammaMeasuredPointZeroArity hc B).underlying).toGamma.toGammaRVObject 0) :=
  gammaElementaryDiagram_exists_original hκ hs h00 hr hg hB (Set.subset_univ _) gammaMeasuredPoint_admissible

end DiamondIntegral.Section3
