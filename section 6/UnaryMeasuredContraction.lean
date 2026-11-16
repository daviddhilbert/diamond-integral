import «section 6».UnaryMeasuredPartitionPreparation

/-! The actual RV contraction and descended Gamma form of a constructed
unary measured preparation. Its full graph, surjectivity, exact inverse
transport and factorization of the original form are all checked. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i, (C i).carrier ⊆ A.carrier}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

namespace UnaryMeasuredPreparation

def contraction (T : UnaryMeasuredPreparation (G := G) A C hCA ω) : Map A (rvTagQuotient T.target) :=
  (rvTagQuotientMap T.target).comp T.map

theorem contraction_surjective (T : UnaryMeasuredPreparation (G := G) A C hCA ω)
    (h00 : M ⊨ Axioms.ACVF00) : Function.Surjective T.contraction :=
  (rvTagQuotientMap_surjective T.target).comp (T.special.bijective h00).surjective

theorem rv_target_bounded (T : UnaryMeasuredPreparation (G := G) A C hCA ω) :
    RVSupportDoublyBounded (rvTagQuotient T.target).carrier :=
  rvTagQuotient_rvBounded T.target T.proper.rvBounded

def descendedForm (T : UnaryMeasuredPreparation (G := G) A C hCA ω) : (Fin T.arity → M) → Gamma M :=
  rvContractedGamma T.target.carrier (gammaFormExtension T.form)

theorem descendedForm_graph_definable (T : UnaryMeasuredPreparation (G := G) A C hCA ω) :
    S.Definable LRV (rawGammaFamilyGraph (rvInputValues '' (Prod.snd '' T.target.carrier))
      (fun t => {T.descendedForm t})) :=
  rvContractedGamma_graph_definable T.target.carrier (gammaFormExtension T.form)
    (gammaFormExtension_graph_definable T.form) T.constant

theorem form_factorization (T : UnaryMeasuredPreparation (G := G) A C hCA ω) (p : A) :
    T.descendedForm (rvInputValues (T.contraction p).val.2) = (ω p).val := by
  change rvContractedGamma T.target.carrier (gammaFormExtension T.form) (rvInputValues (T.map p).val.2) = _
  rw [rvContractedGamma_at T.target.carrier (gammaFormExtension T.form) T.constant (T.map p).val (T.map p).property,
    gammaFormExtension_at]
  exact T.transport p

theorem form_at_inverse (T : UnaryMeasuredPreparation (G := G) A C hCA ω)
    (h00 : M ⊨ Axioms.ACVF00) (q : T.target) :
    (T.form q).val = (ω (T.map.inverse (T.special.bijective h00) q)).val := by
  have h := T.transport (T.map.inverse (T.special.bijective h00) q)
  rw [Map.apply_inverse] at h
  exact h

theorem contraction_retains_rv (T : UnaryMeasuredPreparation (G := G) A C hCA ω) :
    ∃ h : r ≤ T.arity, ∀ p : A, ∀ i : Fin r,
      (T.contraction p).val.2 (rvTailIndex h i) = p.val.2 i := T.special.retainsRV

end UnaryMeasuredPreparation
end DiamondIntegral.Section6
