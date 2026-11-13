import «section 3».GammaGroundGammaRVLift
import «section 3».GammaGroundGammaCodeRestrictions
import «section 3».GammaGroundRVFamilyRestrictions
import «section 3».GammaGroundGammaScissors
import «section 3».GammaGroundRVScissors
import «section 3».GammaGroundCarrierBijections
import «section 3».GammaGroundEmptyBijections
import «section 3».GammaGroundRVProductScissors
/-! The actual Gamma lift descends to the fixed-degree positive scissor
quotients. Both the source base and all RV code representatives are retained. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundGammaRVClass_empty :
    gammaGroundRVClass (GammaGroundGammaObject.empty hc ground k).rvLift = 0 := by
  have he : (GammaGroundGammaObject.empty hc ground k).rvLift.domain.carrier = ∅ := by
    ext t
    constructor
    · rintro ⟨i, _, _⟩
      exact i.elim0
    · exact False.elim
  have e : (GammaGroundGammaObject.empty hc ground k).rvLift ≅ GammaGroundRVObject.empty hc ground k :=
    asIso (show (GammaGroundGammaObject.empty hc ground k).rvLift ⟶ GammaGroundRVObject.empty hc ground k from
      GammaGroundBijection.ofEmpty he rfl)
  exact (gammaGroundRVClass_iso e).trans gammaGroundRVClass_empty

theorem GammaGroundGammaObject.rvLift_restrict_subset (U : GammaGroundGammaObject hc ground k)
    (X : Fin U.tags → GammaGroundGammaPiece hc ground k)
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    (U.restrict X).rvLift.domain.carrier ⊆ U.rvLift.domain.carrier :=
  gammaGroundRVFamilyRealization_mono _ _ (fun i => gammaGroundGammaRVCodeLift_mono (hX i))

theorem GammaGroundGammaObject.rvLift_difference (U : GammaGroundGammaObject hc ground k)
    (X : Fin U.tags → GammaGroundGammaPiece hc ground k) :
    (U.restrict (U.difference X)).rvLift.domain.carrier =
      (U.rvLift.difference (U.restrict X).rvLift.domain).carrier := by
  change (GammaGroundFiniteFamily.rvRealization ⟨U.tags,
      fun i => (gammaGroundGammaCodeToRV ((U.piece i).sdiff (X i))).image⟩).carrier =
    (GammaGroundFiniteFamily.rvRealization ⟨U.tags, fun i => (gammaGroundGammaCodeToRV (U.piece i)).image⟩).carrier \
      (GammaGroundFiniteFamily.rvRealization ⟨U.tags, fun i => (gammaGroundGammaCodeToRV (X i)).image⟩).carrier
  have hp (i : Fin U.tags) :
      (gammaGroundGammaCodeToRV ((U.piece i).sdiff (X i))).image =
      ((gammaGroundGammaCodeToRV (U.piece i)).image.sdiff (gammaGroundGammaCodeToRV (X i)).image) :=
    GammaGroundDefSet.eq_of_carrier_eq (gammaGroundGammaRVCodeLift_sdiff (U.piece i) (X i))
  rw [← gammaGroundRVFamilyRealization_sdiff
    (fun i : Fin U.tags => (gammaGroundGammaCodeToRV (U.piece i)).image)
    (fun i => (gammaGroundGammaCodeToRV (X i)).image)]
  exact congrArg (fun Y : Fin U.tags → GammaGroundDefSet hc ground (rawRVSpace (M := M) k) =>
    (show Set (rawRVSpace (M := M) (U.tags + k)).Carrier from
      (GammaGroundFiniteFamily.rvRealization ⟨U.tags, Y⟩).carrier)) (funext hp)

theorem gammaGroundGammaRVClass_scissor (U : GammaGroundGammaObject hc ground k)
    (X : Fin U.tags → GammaGroundGammaPiece hc ground k)
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    gammaGroundRVClass (U.restrict X).rvLift + gammaGroundRVClass (U.restrict (U.difference X)).rvLift = gammaGroundRVClass U.rvLift := by
  let W := U.rvLift
  let Y := (U.restrict X).rvLift.domain
  have hY : Y.carrier ⊆ W.domain.carrier := U.rvLift_restrict_subset X hX
  have hA : gammaGroundRVClass (U.restrict X).rvLift = gammaGroundRVClass (W.restrict Y hY) :=
    gammaGroundRVClass_iso (asIso (show (U.restrict X).rvLift ⟶ W.restrict Y hY from
      GammaGroundBijection.ofCarrierEq rfl))
  have hB : gammaGroundRVClass (U.restrict (U.difference X)).rvLift =
      gammaGroundRVClass (W.restrict (W.difference Y) (fun _ h => h.1)) :=
    gammaGroundRVClass_iso (asIso (show (U.restrict (U.difference X)).rvLift ⟶
      W.restrict (W.difference Y) (fun _ h => h.1) from
        GammaGroundBijection.ofCarrierEq (U.rvLift_difference X)))
  rw [hA, hB]
  exact gammaGroundRVClass_scissor W Y hY

def gammaGroundGammaToRVKPlus : GammaGroundGammaKPlus hc ground k →+ GammaGroundRVKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundGammaPresentation hc ground k) {
    toFun A := gammaGroundRVClass A.rvLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := gammaGroundGammaHom_lift_iso e.hom
      exact gammaGroundRVClass_iso E
    empty := gammaGroundGammaRVClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      rw [gammaGroundGammaRVClass_empty, add_zero]
      exact gammaGroundGammaRVClass_scissor U X hX }

@[simp] theorem gammaGroundGammaToRVKPlus_class (A : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaToRVKPlus (gammaGroundGammaClass A) = gammaGroundRVClass A.rvLift := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
