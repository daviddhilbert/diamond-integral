import «section 3».MeasuredGammaRestrictions
import «section 3».MeasuredGammaRVMorphisms
import «section 3».MeasuredRVScissors
import «section 3».CarrierBijections

/-! The measured Gamma lift descends to the actual pointwise measured
RV positive scissor quotient. Forms are inherited through every cut. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def measuredGammaRVRestrictionHom (U : MeasuredGammaObject hc S k)
    (X : Fin U.underlying.tags → GammaPiece hc S k)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier)
    (D : DefSet (rawRVSpace (M := M) U.underlying.rvLift.arity) S)
    (hD : D.carrier ⊆ U.underlying.rvLift.domain.carrier)
    (he : (U.restrict X hX).rvLift.underlying.domain.carrier = D.carrier) :
    MeasuredRVHom (U.restrict X hX).rvLift (U.rvLift.restrict hc D hD) where
  bijection := DefinableBijection.ofCarrierEq he
  preserves a := by
    change gammaFormValue (measuredGammaLiftForm (U.restrict X hX)) a * _ =
      gammaFormValue (measuredGammaLiftForm U)
        (Map.inclusion hD ((DefinableBijection.ofCarrierEq he).map a)) * _
    rw [measuredGammaLiftForm_restrict]
    rfl

theorem measuredGammaRVClass_empty :
    measuredRVClass hc (MeasuredGammaObject.empty hc S k).rvLift = 0 := by
  have he : (MeasuredGammaObject.empty hc S k).rvLift.underlying.domain.carrier = ∅ := by
    ext t
    constructor
    · rintro ⟨i, _, _⟩
      exact i.elim0
    · exact False.elim
  let f : MeasuredRVHom (MeasuredGammaObject.empty hc S k).rvLift (MeasuredRVObject.empty S k) :=
    ⟨DefinableBijection.ofEmpty he rfl, fun a =>
      False.elim ((Set.notMem_empty a.val) (he ▸ a.property))⟩
  exact (measuredRVClass_iso hc (asIso (show _ ⟶ _ from f))).trans (measuredRVClass_empty hc)

theorem measuredGammaRVClass_scissor (U : MeasuredGammaObject hc S k)
    (X : Fin U.underlying.tags → GammaPiece hc S k)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier) :
    measuredRVClass hc (U.restrict X hX).rvLift +
      measuredRVClass hc (U.restrict (U.underlying.difference X) (fun i _ h => h.1)).rvLift =
        measuredRVClass hc U.rvLift := by
  let W := U.rvLift
  let Y := (U.restrict X hX).rvLift.underlying.domain
  have hY : Y.carrier ⊆ W.underlying.domain.carrier := U.underlying.rvLift_restrict_subset X hX
  have hA : measuredRVClass hc (U.restrict X hX).rvLift = measuredRVClass hc (W.restrict hc Y hY) :=
    measuredRVClass_iso hc (asIso (show _ ⟶ _ from measuredGammaRVRestrictionHom U X hX Y hY rfl))
  have hd : (U.restrict (U.underlying.difference X) (fun i _ h => h.1)).rvLift.underlying.domain.carrier =
      (W.underlying.difference Y).carrier := U.underlying.rvLift_difference X
  have hB : measuredRVClass hc (U.restrict (U.underlying.difference X) (fun i _ h => h.1)).rvLift =
      measuredRVClass hc (W.restrict hc (W.underlying.difference Y) (fun _ h => h.1)) :=
    measuredRVClass_iso hc (asIso (show _ ⟶ _ from measuredGammaRVRestrictionHom U
      (U.underlying.difference X) (fun i _ h => h.1) (W.underlying.difference Y) (fun _ h => h.1) hd))
  rw [hA, hB]
  exact measuredRVClass_scissor hc W Y hY

def measuredGammaToRVKPlus : MeasuredGammaKPlus hc S k →+ MeasuredRVKPlus hc S k :=
  PositiveAdditiveGrothendieck.lift (measuredGammaPresentation hc S k) {
    toFun A := measuredRVClass hc A.rvLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := measuredGammaHom_lift_iso e.hom
      exact measuredRVClass_iso hc E
    empty := measuredGammaRVClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      rw [measuredGammaRVClass_empty, add_zero]
      exact measuredGammaRVClass_scissor U X hX }

@[simp] theorem measuredGammaToRVKPlus_class (A : MeasuredGammaObject hc S k) :
    measuredGammaToRVKPlus (measuredGammaClass A) = measuredRVClass hc A.rvLift :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
