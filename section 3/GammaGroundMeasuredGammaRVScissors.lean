import «section 3».GammaGroundMeasuredGammaRestrictions
import «section 3».GammaGroundMeasuredGammaRVMorphisms
import «section 3».GammaGroundMeasuredRVScissors
import «section 3».GammaGroundCarrierBijections
import «section 3».GammaGroundEmptyBijections
/-! The measured Gamma lift descends to the actual pointwise measured
RV positive scissor quotient. Forms are inherited through every cut. -/

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

def gammaGroundMeasuredGammaRVRestrictionHom (U : GammaGroundMeasuredGammaObject hc ground k)
    (X : Fin U.underlying.tags → GammaGroundGammaPiece hc ground k)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier)
    (D : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.underlying.rvLift.arity))
    (hD : D.carrier ⊆ U.underlying.rvLift.domain.carrier)
    (he : (U.restrict X hX).rvLift.underlying.domain.carrier = D.carrier) :
    GammaGroundMeasuredRVHom (U.restrict X hX).rvLift (U.rvLift.restrict D hD) where
  bijection := GammaGroundBijection.ofCarrierEq he
  preserves a := by
    change gammaGroundFormValue (gammaGroundMeasuredGammaLiftForm (U.restrict X hX)) a * _ =
      gammaGroundFormValue (gammaGroundMeasuredGammaLiftForm U)
        (GammaGroundMap.inclusion hD ((GammaGroundBijection.ofCarrierEq he).map a)) * _
    rw [gammaGroundMeasuredGammaLiftForm_restrict]
    rfl

theorem gammaGroundMeasuredGammaRVClass_empty :
    gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground k).rvLift = 0 := by
  have he : (GammaGroundMeasuredGammaObject.empty hc ground k).rvLift.underlying.domain.carrier = ∅ := by
    ext t
    constructor
    · rintro ⟨i, _, _⟩
      exact i.elim0
    · exact False.elim
  let f : GammaGroundMeasuredRVHom (GammaGroundMeasuredGammaObject.empty hc ground k).rvLift (GammaGroundMeasuredRVObject.empty hc ground k) :=
    ⟨GammaGroundBijection.ofEmpty he rfl, fun a =>
      False.elim ((Set.notMem_empty a.val) (he ▸ a.property))⟩
  exact (gammaGroundMeasuredRVClass_iso (asIso (show _ ⟶ _ from f))).trans (gammaGroundMeasuredRVClass_empty)

theorem gammaGroundMeasuredGammaRVClass_scissor (U : GammaGroundMeasuredGammaObject hc ground k)
    (X : Fin U.underlying.tags → GammaGroundGammaPiece hc ground k)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier) :
    gammaGroundMeasuredRVClass (U.restrict X hX).rvLift +
      gammaGroundMeasuredRVClass (U.restrict (U.underlying.difference X) (fun i _ h => h.1)).rvLift =
        gammaGroundMeasuredRVClass U.rvLift := by
  let W := U.rvLift
  let Y := (U.restrict X hX).rvLift.underlying.domain
  have hY : Y.carrier ⊆ W.underlying.domain.carrier := U.underlying.rvLift_restrict_subset X hX
  have hA : gammaGroundMeasuredRVClass (U.restrict X hX).rvLift = gammaGroundMeasuredRVClass (W.restrict Y hY) :=
    gammaGroundMeasuredRVClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaRVRestrictionHom U X hX Y hY rfl))
  have hd : (U.restrict (U.underlying.difference X) (fun i _ h => h.1)).rvLift.underlying.domain.carrier =
      (W.underlying.difference Y).carrier := U.underlying.rvLift_difference X
  have hB : gammaGroundMeasuredRVClass (U.restrict (U.underlying.difference X) (fun i _ h => h.1)).rvLift =
      gammaGroundMeasuredRVClass (W.restrict (W.underlying.difference Y) (fun _ h => h.1)) :=
    gammaGroundMeasuredRVClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaRVRestrictionHom U
      (U.underlying.difference X) (fun i _ h => h.1) (W.underlying.difference Y) (fun _ h => h.1) hd))
  rw [hA, hB]
  exact gammaGroundMeasuredRVClass_scissor W Y hY

def gammaGroundMeasuredGammaToRVKPlus : GammaGroundMeasuredGammaKPlus hc ground k →+ GammaGroundMeasuredRVKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredGammaPresentation hc ground k) {
    toFun A := gammaGroundMeasuredRVClass A.rvLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := gammaGroundMeasuredGammaHom_lift_iso e.hom
      exact gammaGroundMeasuredRVClass_iso E
    empty := gammaGroundMeasuredGammaRVClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      rw [gammaGroundMeasuredGammaRVClass_empty, add_zero]
      exact gammaGroundMeasuredGammaRVClass_scissor U X hX }

@[simp] theorem gammaGroundMeasuredGammaToRVKPlus_class (A : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaToRVKPlus (gammaGroundMeasuredGammaClass A) = gammaGroundMeasuredRVClass A.rvLift :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
