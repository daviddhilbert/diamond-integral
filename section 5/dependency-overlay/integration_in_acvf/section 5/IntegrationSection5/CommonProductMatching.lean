import IntegrationSection5.CommonProductHeadPair
import IntegrationSection5.CompletedHeadComparison
import IntegrationSection5.NonrectangleRVComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

namespace CommonProductHeadPair
variable {T : PositionedCellLabelInjection G A}
def oldHeads (P : CommonProductHeadPair T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) : NonrectangleHeadPresentations T :=
  T.nonrectanglePresentationsOfStages δ hδ P.position P.labels P.spec P.left.branch P.left_sat P.right.branch P.right_sat
end CommonProductHeadPair

structure CommonProductMatching (T : PositionedCellLabelInjection G A) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) where
  first : CommonProductHeadPair T
  unary : MatchedUnaryPreparation (G := G)
    (carrier ((first.oldHeads δ hδ).left.toHead (first.oldHeads δ hδ).left_saturated).contractedSet)
    (carrier ((first.oldHeads δ hδ).right.toHead (first.oldHeads δ hδ).right_saturated).contractedSet)
    (first.oldHeads δ hδ).headIso.equiv
  contains : first.rectangle.codes ⊆ unary.codes

namespace CommonProductMatching
variable {T : PositionedCellLabelInjection G A} {δ : Values.Gamma (M := M)} {hδ : 1 < δ}
def asOld (Q : CommonProductMatching T δ hδ) : NonrectangleMatchedHeads T where
  first := Q.first.oldHeads δ hδ
  unary := Q.unary
  contains := by
    intro x hx
    rcases hx with h | h
    · exact Q.contains (Q.first.containsLeft h)
    · exact Q.contains (Q.first.containsRight h)
end CommonProductMatching

theorem common_product_matching {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) : Nonempty (CommonProductMatching T δ hδ1) := by
  obtain ⟨P⟩ := T.common_product_head_pair hs h00 hsmall F δ hδ1
  let H := P.oldHeads δ hδ1
  obtain ⟨Q,hQ⟩ := matched_unary_preparation_over hκ hs hsmall h00 δ hδ hδ1 F P.rectangle.codes _ _
    (gamma_headImage H.left.target H.left.target_gamma) (gamma_headImage H.right.target H.right.target_gamma) H.headIso
  exact ⟨⟨P,Q,hQ⟩⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
