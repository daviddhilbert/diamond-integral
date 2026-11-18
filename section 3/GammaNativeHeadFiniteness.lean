import «section 3».GammaMeasuredHeadFiniteness
import «section 3».GammaNativeStructuralValues

/-! Original-ground native admissibility gives a finite head directly in
the literal local full-weight conversion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaNativeHead_finite_of_admissible
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last n)) :
    (gammaRVHeadMap (Section5.nativeRVGroundObject (hc := hc) U hfull)).FiniteFibres := by
  let V := Section5.nativeRVGroundObject (hc := hc) U hfull
  let E := Section5.nativeRVGroundDomainEquiv (hc := hc) U
  let f := gammaVolumeValue U.toGamma.toGammaRVObject
  have hf (t : Fin (n+1) → CanonicalRV.RVSort M) : {u | f u = t}.Finite := by
    apply (U.toGamma.finite_volume ⟨t,Set.mem_univ _⟩).subset
    intro u hu
    exact Subtype.ext hu
  intro t
  have hdel := finite_fibres_coordinate_deletion f (Fin.last n) (0 : CanonicalRV.RVSort M) hf
    (hAd.finite_label_slices hκ hs h00 hr) t.val
  apply Set.Finite.of_injOn (f := E) (t := {u | (fun j => f u ((Fin.last n).succAbove j)) = t.val}) ?_ E.injective.injOn hdel
  intro u hu
  have he : f (E u) = (V.volume u).val := (gammaNativeRVGroundVolume_value U u).symm
  change (fun j : Fin n => f (E u) ((Fin.last n).succAbove j)) = t.val
  calc
    _ = (fun j : Fin n => (V.volume u).val j.castSucc) := by
      funext j
      exact (congrFun he ((Fin.last n).succAbove j)).trans
        (congrArg ((V.volume u).val) (Fin.succAbove_last_apply j))
    _ = t.val := congrArg Subtype.val hu

end DiamondIntegral.Section3
