import «section 3».GammaGroundRVGenericBijection
import «section 3».RVGenericOriginalGroundWeights
import «section 3».GammaGroundAffinePartitionLift
import «section 3».GammaGroundGammaSemiring
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Every actual bijection of two single full RV preimages yields a
Gamma-category isomorphism. Its new full RV lift may differ from the
original bijection on residue coordinates. -/
theorem gammaGroundGammaSingle_reflects_RV_bijection [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (H : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (f : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J)) :
    Nonempty (GammaGroundGammaHom (GammaGroundGammaObject.single G) (GammaGroundGammaObject.single J)) := by
  obtain ⟨h,hh⟩ := gammaGroundRVBijection_generic_bijection hκ hs h00 hsmall hγsmall G J f
  have hpoint : ∀ γ : G, ∃ F : OriginalGroundAffineRVFormula hc B n,
      (h.map γ).val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.val := by
    intro γ
    obtain ⟨C,c,hC,_,hcoeff,hcdef⟩ := gammaGroundRVGeneric_original_coefficients
      hκ hs h00 hsmall H G J f.map f.bijective.1 h.map hh γ
    exact ⟨⟨C,hC,c,hcdef⟩,hcoeff⟩
  obtain ⟨N,F,P,hP,hcover,hformula⟩ := gammaGroundAffine_finite_partition hκ.le hs hsmall hγsmall G J h.map hpoint
  obtain ⟨L,hL⟩ := gammaGroundAffine_partition_full_lift G J h F P hP hcover hformula
  refine ⟨gammaGroundGammaSingleHomOfUnitBijection G J L ?_⟩
  intro u v
  have hLv : rvUnitTupleValues (L.map u).val =
      (h.map (gammaGroundFullPreimageValueMap G u)).val := congrArg Subtype.val (hL u)
  have hRv : rvUnitTupleValues (L.map v).val =
      (h.map (gammaGroundFullPreimageValueMap G v)).val := congrArg Subtype.val (hL v)
  rw [hLv,hRv]
  constructor
  · intro hv
    exact congrArg (fun γ : G => (h.map γ).val) (Subtype.ext hv)
  · intro hv
    exact congrArg Subtype.val (h.bijective.1 (Subtype.ext hv))

/-- The single-piece reflection already takes place in the positive
semiring; no additive cancellation or group completion occurs. -/
theorem gammaGroundGammaSemiringClass_single_eq_of_RV_bijection [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (H : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (f : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J)) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single J) := by
  obtain ⟨g⟩ := gammaGroundGammaSingle_reflects_RV_bijection hκ hs h00 hsmall hγsmall H G J f
  exact gammaGroundGammaSemiringClass_iso (asIso (show _ ⟶ _ from g))

end DiamondIntegral.Section3
