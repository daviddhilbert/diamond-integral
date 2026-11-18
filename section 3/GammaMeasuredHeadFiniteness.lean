import «section 3».GammaMeasuredHeadFactor
import «section 5».Completed18LocalLift
import IntegrationSection6.FiniteGammaVolumeDeletion

/-! Native original-Gamma admissibility supplies the finite head needed
by the weighted factorization. No finiteness assumption is added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaMeasuredHead_finite_of_admissible
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundRVObject hc B (n+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U).toGamma.toGammaRVObject (Fin.last n)) :
    (gammaRVHeadMap U).FiniteFibres := by
  let NU := Section5.groundRVAt U
  let E := Section5.groundRVAtDomainEquiv U
  let f := gammaVolumeValue NU.toGamma.toGammaRVObject
  have hf (t : Fin (n+1) → CanonicalRV.RVSort M) : {u | f u = t}.Finite := by
    apply (NU.toGamma.finite_volume ⟨t,Set.mem_univ _⟩).subset
    intro u hu
    exact Subtype.ext hu
  intro t
  have hdel := finite_fibres_coordinate_deletion f (Fin.last n) (0 : CanonicalRV.RVSort M) hf
    (hAd.finite_label_slices hκ hs h00 hr) t.val
  apply Set.Finite.of_injOn (f := E) (t := {u | (fun j => f u ((Fin.last n).succAbove j)) = t.val}) ?_ E.injective.injOn hdel
  intro u hu
  have he : f (E u) = (U.volume u).val := by
    change (rvObjectVolume NU.object.obj (E u)).val = _
    exact (Section5.groundRVAt_volume_eq U (E u)).trans
      (congrArg (fun a : U.domain => (U.volume a).val) (E.symm_apply_apply u))
  change (fun j : Fin n => f (E u) ((Fin.last n).succAbove j)) = t.val
  calc
    _ = (fun j : Fin n => (U.volume u).val j.castSucc) := by
      funext j
      exact (congrFun he ((Fin.last n).succAbove j)).trans (congrArg ((U.volume u).val) (Fin.succAbove_last_apply j))
    _ = t.val := congrArg Subtype.val hu

end DiamondIntegral.Section3
