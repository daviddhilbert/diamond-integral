import IntegrationSection5.NonrectangleHeadPresentations
import IntegrationSection5.MatchedUnaryPreparation
import IntegrationSection5.MatchedHeadCompletion
import IntegrationSection5.GammaStandardProgramGraphs

/-! Apply Lemma5.2 once to the actual global head-source bijection, retaining its full commuting square, and construct both standard programs over one common real presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
namespace PositionedCellLabelInjection
variable {m : ℕ} {A : Set (Point (M := M) 2 m)}

structure NonrectangleMatchedHeads (T : PositionedCellLabelInjection G A) where
  first : NonrectangleHeadPresentations T
  unary : MatchedUnaryPreparation (G := G)
    (carrier (first.left.toHead first.left_saturated).contractedSet)
    (carrier (first.right.toHead first.right_saturated).contractedSet) first.headIso.equiv
  contains : first.left.codes ∪ first.right.codes ⊆ unary.codes

theorem nonrectangle_matched_heads {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) : Nonempty (NonrectangleMatchedHeads T) := by
  obtain ⟨P⟩ := T.nonrectangle_head_presentations δ hδ1
  have hL := gamma_headImage P.left.target P.left.target_gamma
  have hR := gamma_headImage P.right.target P.right.target_gamma
  obtain ⟨Q,hQ⟩ := matched_unary_preparation_over hκ hs hsmall h00 δ hδ hδ1 F
    (P.left.codes ∪ P.right.codes) _ _ hL hR P.headIso
  exact ⟨⟨P,Q,hQ⟩⟩


namespace NonrectangleMatchedHeads
variable {T : PositionedCellLabelInjection G A}

def containsLeft (Q : NonrectangleMatchedHeads T) : Q.first.left.codes ⊆ Q.unary.codes :=
  fun _ hx => Q.contains (Or.inl hx)

def containsRight (Q : NonrectangleMatchedHeads T) : Q.first.right.codes ⊆ Q.unary.codes :=
  fun _ hx => Q.contains (Or.inr hx)

def completion (Q : NonrectangleMatchedHeads T) : MatchedHeadCompletion (G := G)
    (Q.first.left.toHead Q.first.left_saturated) (Q.first.right.toHead Q.first.right_saturated) where
  codes := Q.unary.codes
  containsA := Q.containsLeft
  containsB := Q.containsRight
  arityA := Q.unary.arityA
  arityB := Q.unary.arityB
  targetA := Q.unary.targetA
  targetB := Q.unary.targetB
  tailA := headCompletionTail _ Q.containsLeft Q.unary.sourceA_eq Q.unary.specialA
  tailB := headCompletionTail _ Q.containsRight Q.unary.sourceB_eq Q.unary.specialB
  pullbackA := Q.unary.pullbackA
  pullbackB := Q.unary.pullbackB
  graphA := gamma_headCompletionTail _ Q.containsLeft Q.unary.sourceA_eq Q.unary.specialA
    (GammaChainDefinable.graph (gammaLogicInput G) Q.unary.specialA.chain Q.unary.gammaA)
  graphB := gamma_headCompletionTail _ Q.containsRight Q.unary.sourceB_eq Q.unary.specialB
    (GammaChainDefinable.graph (gammaLogicInput G) Q.unary.specialB.chain Q.unary.gammaB)
  targetA_gamma := GammaChainDefinable.target G Q.unary.specialA.chain Q.unary.gammaA
  targetB_gamma := GammaChainDefinable.target G Q.unary.specialB.chain Q.unary.gammaB
  iso := Q.unary.iso
  hom_graph := Q.unary.hom_graph
  inv_graph := Q.unary.inv_graph

def source (Q : NonrectangleMatchedHeads T) := extendBase Q.first.left.source Q.containsLeft

def sourceSwapped (Q : NonrectangleMatchedHeads T) := extendBase Q.first.right.source Q.containsRight

theorem source_eq (Q : NonrectangleMatchedHeads T) : carrier Q.source = nonrectangleFamilyBranch T.target :=
  Q.first.left.source_eq

theorem sourceSwapped_eq (Q : NonrectangleMatchedHeads T) : carrier Q.sourceSwapped = T.swappedNonrectangleFamily :=
  Q.first.right.source_eq

theorem source_swapped_presentation (Q : NonrectangleMatchedHeads T) :
    Q.sourceSwapped = vfPermutationImage Q.source (Equiv.swap 0 1) := by
  apply PresentedSet.eq_of_carrier_eq
  ext p
  change p ∈ carrier Q.sourceSwapped ↔ p ∈ carrier (vfPermutationImage Q.source (Equiv.swap 0 1))
  rw [vfPermutationImage_mem_mixed,Q.sourceSwapped_eq,Q.source_eq]
  change (vfPermutation (Equiv.swap 0 1) p ∈ nonrectangleFamilyBranch T.target) ↔
    (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p ∈ nonrectangleFamilyBranch T.target)
  rw [Equiv.symm_swap]

def contraction12 (Q : NonrectangleMatchedHeads T) : StandardContraction Q.source (Equiv.refl _) :=
  standardContractionOfProgram Q.source Q.source (Equiv.refl _)
    (vfPermutationImage_identity Q.source).symm Q.completion.programA

def contraction21 (Q : NonrectangleMatchedHeads T) : StandardContraction Q.source (Equiv.swap 0 1) :=
  standardContractionOfProgram Q.source Q.sourceSwapped (Equiv.swap 0 1)
    Q.source_swapped_presentation Q.completion.programB

theorem programA_gamma (Q : NonrectangleMatchedHeads T) : GammaProgramDefinable G Q.completion.programA :=
  Q.completion.programA_gamma Q.first.left.graph Q.first.left.target_gamma

theorem programB_gamma (Q : NonrectangleMatchedHeads T) : GammaProgramDefinable G Q.completion.programB :=
  Q.completion.programB_gamma Q.first.right.graph Q.first.right.target_gamma

theorem contraction12_gamma (Q : NonrectangleMatchedHeads T) : GammaProgramDefinable G Q.contraction12.program :=
  standardProgram_program_gamma Q.source Q.source (Equiv.refl _)
    (vfPermutationImage_identity Q.source).symm Q.completion.programA Q.programA_gamma

theorem contraction21_gamma (Q : NonrectangleMatchedHeads T) : GammaProgramDefinable G Q.contraction21.program :=
  standardProgram_program_gamma Q.source Q.sourceSwapped (Equiv.swap 0 1)
    Q.source_swapped_presentation Q.completion.programB Q.programB_gamma

end NonrectangleMatchedHeads

end PositionedCellLabelInjection
end IntegrationInACVF.Section5
