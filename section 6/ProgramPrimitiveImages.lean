import «section 6».SequentialCentripetalPrograms
import «section 6».CentripetalPullbackPreservation

/-! Exact primitive images and terminal preparation tests on actual
mixed fibres. No geometric input is needed for identity or regularization
semantics, and admissible prefixes preserve an ambient RV-pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}

theorem identity_pieceTarget_fibre
    (A C : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hCA : (C.fibre a).carrier ⊆ (A.fibre a).carrier) :
    ((CentripetalProgramTemplate.identity r).pieceTarget A C).fibre a=C.fibre a := by
  have h := mixedRelationImageTemplate_at_restriction C (identityParameterTransition A)
    (identityParameterTransition_definable A) a (Map.id (A.fibre a)) hCA
    (identityParameterTransition_at A a)
  change ((CentripetalProgramTemplate.identity r).pieceTarget A C).fibre a=_ at h
  refine h.trans (defSet_eq_of_carrier_eq ?_)
  ext q
  exact ⟨fun ⟨c,hc⟩ => hc ▸ c.property,fun hq => ⟨⟨q,hq⟩,rfl⟩⟩

theorem identity_preparedGood_iff
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier) :
    a ∈ (CentripetalProgramTemplate.identity r).preparedGood A P ↔
      ∀ i,IsRVPullback ((P i).fibre a).carrier := by
  change (a ∈ Set.univ ∧ a ∈ ⋂ i,rvPullbackParameterLocus
    ((CentripetalProgramTemplate.identity r).pieceTarget A (P i)).typedGraph) ↔ _
  simp only [Set.mem_univ,true_and,Set.mem_iInter]
  apply forall_congr'
  intro i
  rw [mem_rvPullbackParameterLocus_iff _ a
    (((CentripetalProgramTemplate.identity r).pieceTarget A (P i)).fibre a)
    (((CentripetalProgramTemplate.identity r).pieceTarget A (P i)).fibre_code a).symm,
    identity_pieceTarget_fibre A (P i) a (hPA i)]

theorem regularization_pieceTarget_fibre
    (A C : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hCA : (C.fibre a).carrier ⊆ (A.fibre a).carrier) :
    ((CentripetalProgramTemplate.regularize r).pieceTarget A C).fibre a=
      ((regularization (A.fibre a)).restrict hCA).image :=
  mixedRelationImageTemplate_at_restriction C (regularizationParameterTransition A)
    (regularizationParameterTransition_definable A) a (regularization (A.fibre a)) hCA
    (regularizationParameterTransition_at A a)

theorem regularization_pieceTarget_mem_iff
    (A C : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hCA : (C.fibre a).carrier ⊆ (A.fibre a).carrier) (x : Mixed M n r) :
    regularize x ∈ (((CentripetalProgramTemplate.regularize r).pieceTarget A C).fibre a).carrier ↔
      x ∈ (C.fibre a).carrier := by
  rw [regularization_pieceTarget_fibre A C a hCA]
  constructor
  · rintro ⟨c,hc⟩
    exact regularize_injective hc ▸ c.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramRealization.output_rvPullback
    (h00 : M ⊨ Axioms.ACVF00)
    {T : CentripetalProgramTemplate (M := M) S p n r s}
    {A : MixedSetParameterTemplate (M := M) S p n r}
    {P : Fin k → MixedSetParameterTemplate (M := M) S p n r} {a : Fin p → M}
    (F : CentripetalProgramRealization (G := G) T A P a) (hA : IsRVPullback (A.fibre a).carrier) :
    IsRVPullback ((T.target A).fibre a).carrier := F.chain.toChain.target_rvPullback h00 hA

end DiamondIntegral.Section6
