import «section 3».GammaRVLift
import «section 3».GammaCodeRestrictions
import «section 3».RVFamilyRestrictions
import «section 3».GammaScissors
import «section 3».RVScissors
import «section 3».CarrierBijections

/-! The actual Gamma lift descends to the fixed-degree positive scissor
quotients. Both the source base and all RV code representatives are retained. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem defSet_eq_of_carrier_eq {L : Language} {N : Type} [L.Structure N]
    {P : Space L N} {T : Set N} {A B : DefSet P T} (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem gammaRVClass_empty :
    rvClass (GammaObject.empty hc S k).rvLift = 0 := by
  have he : (GammaObject.empty hc S k).rvLift.domain.carrier = ∅ := by
    ext t
    constructor
    · rintro ⟨i, _, _⟩
      exact i.elim0
    · exact False.elim
  have e : (GammaObject.empty hc S k).rvLift ≅ RVObject.empty S k :=
    asIso (show (GammaObject.empty hc S k).rvLift ⟶ RVObject.empty S k from
      DefinableBijection.ofEmpty he rfl)
  exact (rvClass_iso e).trans rvClass_empty

theorem GammaObject.rvLift_restrict_subset (U : GammaObject hc S k)
    (X : Fin U.tags → GammaPiece hc S k)
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    (U.restrict X).rvLift.domain.carrier ⊆ U.rvLift.domain.carrier :=
  rvFamilyRealization_mono _ _ (fun i => gammaRVCodeLift_mono (hX i))

theorem GammaObject.rvLift_difference (U : GammaObject hc S k)
    (X : Fin U.tags → GammaPiece hc S k) :
    (U.restrict (U.difference X)).rvLift.domain.carrier =
      (U.rvLift.difference (U.restrict X).rvLift.domain).carrier := by
  change (FiniteFamily.rvRealization ⟨U.tags,
      fun i => (gammaCodeToRV ((U.piece i).sdiff (X i))).image⟩).carrier =
    (FiniteFamily.rvRealization ⟨U.tags, fun i => (gammaCodeToRV (U.piece i)).image⟩).carrier \
      (FiniteFamily.rvRealization ⟨U.tags, fun i => (gammaCodeToRV (X i)).image⟩).carrier
  have hp (i : Fin U.tags) :
      (gammaCodeToRV ((U.piece i).sdiff (X i))).image =
      ((gammaCodeToRV (U.piece i)).image.sdiff (gammaCodeToRV (X i)).image) :=
    defSet_eq_of_carrier_eq (gammaRVCodeLift_sdiff (U.piece i) (X i))
  rw [← rvFamilyRealization_sdiff
    (fun i : Fin U.tags => (gammaCodeToRV (U.piece i)).image)
    (fun i => (gammaCodeToRV (X i)).image)]
  exact congrArg (fun Y : Fin U.tags → DefSet (rawRVSpace (M := M) k) S =>
    (show Set (rawRVSpace (M := M) (U.tags + k)).Carrier from
      (FiniteFamily.rvRealization ⟨U.tags, Y⟩).carrier)) (funext hp)

theorem gammaRVClass_scissor (U : GammaObject hc S k)
    (X : Fin U.tags → GammaPiece hc S k)
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    rvClass (U.restrict X).rvLift + rvClass (U.restrict (U.difference X)).rvLift = rvClass U.rvLift := by
  let W := U.rvLift
  let Y := (U.restrict X).rvLift.domain
  have hY : Y.carrier ⊆ W.domain.carrier := U.rvLift_restrict_subset X hX
  have hA : rvClass (U.restrict X).rvLift = rvClass (W.restrict Y hY) :=
    rvClass_iso (asIso (show (U.restrict X).rvLift ⟶ W.restrict Y hY from
      DefinableBijection.ofCarrierEq rfl))
  have hB : rvClass (U.restrict (U.difference X)).rvLift =
      rvClass (W.restrict (W.difference Y) (fun _ h => h.1)) :=
    rvClass_iso (asIso (show (U.restrict (U.difference X)).rvLift ⟶
      W.restrict (W.difference Y) (fun _ h => h.1) from
        DefinableBijection.ofCarrierEq (U.rvLift_difference X)))
  rw [hA, hB]
  exact rvClass_scissor W Y hY

def gammaToRVKPlus : GammaKPlus hc S k →+ RVKPlus S k :=
  PositiveAdditiveGrothendieck.lift (gammaPresentation hc S k) {
    toFun A := rvClass A.rvLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := gammaHom_lift_iso e.hom
      exact rvClass_iso E
    empty := gammaRVClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      rw [gammaRVClass_empty, add_zero]
      exact gammaRVClass_scissor U X hX }

@[simp] theorem gammaToRVKPlus_class (A : GammaObject hc S k) :
    gammaToRVKPlus (gammaClass A) = rvClass A.rvLift := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
