import «section 6».NormalizedBinaryHeadStarts

/-! The full binary head-start map lands in the literal lift of its
RV object, transports the original form exactly, and has unit total
Jacobian outside its actual lower-dimensional lifted exception. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 2 r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin 2)}
namespace NormalizedBinaryMeasuredContraction

theorem headStart_target_eq (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) :
    rvHeadStartBundle F.target k (F.oldIndex ∘ π)=rvLift (F.headStartObject k π) :=
  (defSet_eq_of_carrier_eq (preparedHeadStartRVObject_lift_carrier F.target k _
    F.preparedContraction.lift.originalTarget_pullback F.target_tagged)).symm

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))

def headStartLift (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r) :
    Map (rvHeadStartBundle A k π) (rvLift (F.headStartObject k π)) :=
  changeMapTarget (F.headStartBijection h00 hc linear hκ hs hv hsmall hΓ k π).map (F.headStart_target_eq k π)

theorem headStartLift_value (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) (p : rvHeadStartBundle A k π) :
    (F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π p).val=
      ((F.headStartBijection h00 hc linear hκ hs hv hsmall hΓ k π).map p).val :=
  changeMapTarget_value _ _ p

theorem headStartLift_fixed (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) (p : rvHeadStartBundle A k π) :
    headStartExtraVF 2 k (F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π p).val.1=
      headStartExtraVF 2 k p.val.1 := by
  rw [headStartLift_value]
  exact (F.headStartBijection h00 hc linear hκ hs hv hsmall hΓ k π).fixed p

def headStartLabelMap (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) : Map (rvHeadStartBundle A k π) (F.headStartObject k π).domain :=
  (pureRVTagQuotient (rvHeadStartBundle F.target k (F.oldIndex ∘ π))).comp
    (F.headStartBijection h00 hc linear hκ hs hv hsmall hΓ k π).map

theorem headStartLabelMap_value (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) (p : rvHeadStartBundle A k π) :
    (F.headStartLabelMap h00 hc linear hκ hs hv hsmall hΓ k π p).val=
      (F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π p).val.2 := by
  rw [headStartLift_value]
  rfl

theorem headStart_form_transport (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) (p : rvHeadStartBundle A k π) :
    headStartRVForm F.target k (F.oldIndex ∘ π) F.form F.form_same_tags
      (F.headStartLabelMap h00 hc linear hκ hs hv hsmall hΓ k π p)=
        ω (headStartBaseProjection A k π p) := by
  change headStartRVForm F.target k (F.oldIndex ∘ π) F.form F.form_same_tags
    (pureRVTagQuotient _ ((F.headStartBijection h00 hc linear hκ hs hv hsmall hΓ k π).map p))=_
  rw [headStartRVForm_at,(F.headStartBijection h00 hc linear hκ hs hv hsmall hΓ k π).base]
  exact Subtype.ext (F.form_transport _)

theorem headStartLift_homeomorphism (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) :
    ProperCovariantHomeomorphism (F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π) :=
  (carryHeadStartBijection_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ F.map
    (F.homeomorphism h00 hc linear hκ hs hv hsmall hΓ).bijective
    (F.homeomorphism h00 hc linear hκ hs hv hsmall hΓ) k π _ (fun p i => F.retained p (π i))).changeMapTarget _

theorem headStartLift_unit_derivative_ae (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) :
    ∃ E : DefSet (rawMixedSpace (M := M) (2+k) r) S,E.carrier ⊆ (rvHeadStartBundle A k π).carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < 2+k ∧
      ∀ p : rvHeadStartBundle A k π,p.val ∉ E.carrier →
        HasMixedUnitDerivativeAt (F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π) p := by
  obtain ⟨E,hEA,hDim,hUnit⟩ := F.normalization.normalizedOrderedMap_unit_derivative_ae
    h00 hc hκ hs hv hsmall (by decide) F.preparedContraction.lift
  obtain ⟨hSub,hD,hU⟩ := carryHeadStartBijection_unit_derivative_ae h00 hc hκ hs hv hsmall
    F.map (F.homeomorphism h00 hc linear hκ hs hv hsmall hΓ).bijective F.normalization.sourceProper
    k π (F.oldIndex ∘ π) (fun p i => F.retained p (π i)) E hEA hDim hUnit
  exact ⟨rvHeadStartBundle E k π,hSub,hD,fun p hp => (hU p hp).changeMapTarget _⟩

end NormalizedBinaryMeasuredContraction
end DiamondIntegral.Section6
