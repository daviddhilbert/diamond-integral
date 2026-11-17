import «section 3».GammaNormalizedLiftInclusions

/-! Label-compatible full native lift bijections restrict to actual
bijections of the full-weight local lifts. The complete RV label map is
retained, including its original Gamma graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
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
variable (U V : GammaObjectAt B Set.univ (n+1))
variable (E : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
variable (H : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U))
  (Section5.nativeRVGroundDomain (gammaHighRestrictionAt V)))
variable (hSquare : ∀ u, gammaNativeHighLabelInclusion V (H.map u) = E.map (gammaNativeHighLabelInclusion U u))
variable (f : GammaGroundBijection (gammaNativeUnitLift (hc := hc) U.toGamma).domain (gammaNativeUnitLift V.toGamma).domain)
variable (hl : ∀ p, gammaNativeLiftLabel V (f.map p) = E.map (gammaNativeLiftLabel U p))

def gammaNormalizedLiftMap : GammaGroundMap
    (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U)))
    (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt V) (gammaHighRestriction_fullWeight V))) :=
  (f.map.comp (gammaNormalizedLiftInclusion U)).corestrict (fun p => by
    let u := gammaGroundObjectLiftLabel (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
      (gammaHighRestriction_fullWeight U)) p
    have he : gammaNativeLiftLabel V (f.map (gammaNormalizedLiftInclusion U p)) =
        gammaNativeHighLabelInclusion V (H.map u) :=
      (hl _).trans ((congrArg E.map (gammaNormalizedLiftInclusion_label U p)).trans (hSquare u).symm)
    exact gammaNormalizedLift_of_label V (f.map (gammaNormalizedLiftInclusion U p)) (H.map u)
      (congrArg Subtype.val he).symm)

def gammaNormalizedLiftBijection : GammaGroundBijection
    (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U)))
    (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt V) (gammaHighRestriction_fullWeight V))) := by
  let g := gammaNormalizedLiftMap U V E H hSquare f hl
  have hSquareInv : ∀ v, gammaNativeHighLabelInclusion U (H.symm.map v) = E.symm.map (gammaNativeHighLabelInclusion V v) := by
    intro v
    apply E.bijective.1
    have he := hSquare (H.symm.map v)
    have hh : H.map (H.symm.map v) = v := H.map.apply_inverse H.bijective v
    rw [hh] at he
    exact he.symm.trans (E.map.apply_inverse E.bijective _).symm
  have hlInv : ∀ q, gammaNativeLiftLabel U (f.symm.map q) = E.symm.map (gammaNativeLiftLabel V q) := by
    intro q
    apply E.bijective.1
    have he := hl (f.symm.map q)
    have hf : f.map (f.symm.map q) = q := f.map.apply_inverse f.bijective q
    rw [hf] at he
    exact he.symm.trans (E.map.apply_inverse E.bijective _).symm
  let g' := gammaNormalizedLiftMap V U E.symm H.symm hSquareInv f.symm hlInv
  refine ⟨g,?_,?_⟩
  · intro p q hpq
    have he : f.map (gammaNormalizedLiftInclusion U p) = f.map (gammaNormalizedLiftInclusion U q) :=
      Subtype.ext (congrArg (fun z : gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt V) (gammaHighRestriction_fullWeight V)) => z.val) hpq)
    exact Subtype.ext (congrArg (fun z : (gammaNativeUnitLift (hc := hc) U.toGamma).domain => z.val) (f.bijective.1 he))
  · intro q
    refine ⟨g' q,?_⟩
    apply Subtype.ext
    have he := f.map.apply_inverse f.bijective (gammaNormalizedLiftInclusion V q)
    exact congrArg (fun z : (gammaNativeUnitLift (hc := hc) V.toGamma).domain => z.val) he

@[simp] theorem gammaNormalizedLiftBijection_val
    (p : gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U))) :
    ((gammaNormalizedLiftBijection U V E H hSquare f hl).map p).val =
      (f.map (gammaNormalizedLiftInclusion U p)).val := rfl

theorem gammaNormalizedLiftBijection_label
    (p : gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U))) :
    gammaGroundObjectLiftLabel (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt V) (gammaHighRestriction_fullWeight V))
      ((gammaNormalizedLiftBijection U V E H hSquare f hl).map p) =
      H.map (gammaGroundObjectLiftLabel (Section5.nativeRVGroundObject (hc := hc) (gammaHighRestrictionAt U)
        (gammaHighRestriction_fullWeight U)) p) := by
  apply Subtype.ext
  have he := (hl (gammaNormalizedLiftInclusion U p)).trans
    ((congrArg E.map (gammaNormalizedLiftInclusion_label U p)).trans (hSquare _).symm)
  exact congrArg (fun z : Section5.nativeRVGroundDomain (hc := hc) V => z.val) he

end DiamondIntegral.Section3
