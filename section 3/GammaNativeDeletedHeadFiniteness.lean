import «section 3».GammaNativeHeadFiniteness

/-! Original-ground admissibility gives finite fibres after deleting
any specified structural coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
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

def gammaRVDeletedHeadMap (U : GammaGroundRVObject hc B (n+1)) (i : Fin (n+1)) :=
  (gammaGroundRVSelectCoordinates i.succAbove (GammaGroundDefSet.univ hc B (rawRVSpace (n+1)))).comp U.volume

theorem gammaNativeDeletedHead_finite
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    (gammaRVDeletedHeadMap (Section5.nativeRVGroundObject (hc := hc) U hfull) i).FiniteFibres := by
  let V := Section5.nativeRVGroundObject (hc := hc) U hfull
  let E := Section5.nativeRVGroundDomainEquiv (hc := hc) U
  let f := gammaVolumeValue U.toGamma.toGammaRVObject
  have hf (t : Fin (n+1) → CanonicalRV.RVSort M) : {u | f u = t}.Finite := by
    apply (U.toGamma.finite_volume ⟨t,Set.mem_univ _⟩).subset
    intro u hu
    exact Subtype.ext hu
  intro t
  have hd := finite_fibres_coordinate_deletion f i (0 : CanonicalRV.RVSort M) hf
    (hAd.finite_label_slices hκ hs h00 hr) t.val
  apply Set.Finite.of_injOn (f := E) (t := {u | (fun j => f u (i.succAbove j)) = t.val}) ?_ E.injective.injOn hd
  intro u hu
  have he : f (E u) = (V.volume u).val := (gammaNativeRVGroundVolume_value U u).symm
  change (fun j => f (E u) (i.succAbove j)) = t.val
  exact (congrArg (fun v : Fin (n+1) → CanonicalRV.RVSort M => fun j => v (i.succAbove j)) he).trans
    (congrArg Subtype.val hu)

end DiamondIntegral.Section3
