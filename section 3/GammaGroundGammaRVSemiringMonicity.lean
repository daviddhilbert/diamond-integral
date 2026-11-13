import «section 3».GammaGroundGammaRVMonicity
import «section 3».GammaGroundGammaGradedComparison
import «section 3».GammaGroundFiniteGammaSemiringInclusion
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def gammaGroundGammaDirectSumToRV : GammaGroundGammaDirectSum hc B →+ GammaGroundRVDirectSum hc B :=
  DirectSum.map (fun _ => gammaGroundGammaToRVKPlus)

/-- The lower coefficient homomorphism preserves the actual positive
direct-sum grading. This is independent of its injectivity proof. -/
theorem gammaGroundGammaRVLift_grading (x : GammaGroundGammaPositiveSemiring hc B) :
    gammaGroundRVPresentationToDirectSum (gammaGroundGammaToRVSemiring x) =
      gammaGroundGammaDirectSumToRV (gammaGroundGammaPresentationToDirectSum x) := by
  let f : GammaGroundGammaDirectSum hc B →+ GammaGroundRVDirectSum hc B :=
    gammaGroundRVPresentationToDirectSum.toAddMonoidHom.comp
      (gammaGroundGammaToRVSemiring.toAddMonoidHom.comp gammaGroundGammaDirectSumToPresentation.toAddMonoidHom)
  have hf : f = gammaGroundGammaDirectSumToRV := by
    apply DirectSum.addHom_ext
    intro n
    intro a
    obtain ⟨A,rfl⟩ := gammaGroundGammaClass_surjective a
    change gammaGroundRVPresentationToDirectSum
        (gammaGroundGammaToRVSemiring (gammaGroundGammaDirectSumToPresentation (gammaGroundGammaDirectSumClass hc A))) =
      DirectSum.map (fun _ => gammaGroundGammaToRVKPlus)
        (DirectSum.of (GammaGroundGammaKPlus hc B) n (gammaGroundGammaClass A))
    rw [gammaGroundGammaDirectSumToPresentation_class,gammaGroundGammaToRVSemiring_class,
      gammaGroundRVPresentationToDirectSum_class,DirectSum.map_of,gammaGroundGammaToRVKPlus_class]
    rfl
  have h := DFunLike.congr_fun hf (gammaGroundGammaPresentationToDirectSum x)
  change gammaGroundRVPresentationToDirectSum
      (gammaGroundGammaToRVSemiring (gammaGroundGammaDirectSumToPresentation (gammaGroundGammaPresentationToDirectSum x))) = _ at h
  have hr : gammaGroundGammaDirectSumToPresentation (gammaGroundGammaPresentationToDirectSum x) = x :=
    (gammaGroundGammaSemiringEquivDirectSum (hc := hc) (ground := B)).symm_apply_apply x
  rw [hr] at h
  exact h

/-- The intended lower horizontal coefficient map is a monomorphism
already in the positive semiring, in every degree and finite sum of degrees. -/
theorem gammaGroundGammaToRVSemiring_injective [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (n : ℕ) (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b)) :
    Function.Injective (gammaGroundGammaToRVSemiring (hc := hc) (ground := B)) := by
  have hin : Function.Injective (gammaGroundGammaDirectSumToRV (hc := hc) (B := B)) :=
    (DirectSum.map_injective (fun _ => gammaGroundGammaToRVKPlus)).mpr
      (fun n => gammaGroundGammaToRVKPlus_injective hκ hs h00 hsmall hγsmall (RY n))
  intro a b hab
  apply (gammaGroundGammaSemiringEquivDirectSum (hc := hc) (ground := B)).injective
  apply hin
  exact (gammaGroundGammaRVLift_grading a).symm.trans
    ((congrArg gammaGroundRVPresentationToDirectSum hab).trans (gammaGroundGammaRVLift_grading b))

/-- The upper finite-Gamma-to-RES arrow is a positive semiring
monomorphism by the checked square and lower monomorphism. -/
theorem gammaGroundFiniteGammaToRESSemiring_injective [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (n : ℕ) (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b)) :
    Function.Injective (gammaGroundFiniteGammaToRESSemiring (hc := hc) (ground := B)) := by
  intro a b hab
  apply gammaGroundFiniteGammaToGammaSemiring_injective
  apply gammaGroundGammaToRVSemiring_injective hκ hs h00 hsmall hγsmall RY
  have h := congrArg gammaGroundRESToRVSemiring hab
  have ha := RingHom.congr_fun (gammaGroundFiniteGamma_semiring_square (hc := hc) (ground := B)) a
  have hb := RingHom.congr_fun (gammaGroundFiniteGamma_semiring_square (hc := hc) (ground := B)) b
  exact ha.symm.trans (h.trans hb)

end DiamondIntegral.Section3
