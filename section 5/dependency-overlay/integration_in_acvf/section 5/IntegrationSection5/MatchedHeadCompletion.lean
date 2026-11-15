import IntegrationSection5.MatchedUnaryPreparation
import IntegrationSection5.GammaHeadUnaryCompletion

/-! Assemble two original-base first stages and their matched actual unary
tails over a single internal real presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S R : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 2 m} {B : DefSet (M := M) R 2 l}

structure MatchedHeadCompletion (T : HeadPreparation A) (U : HeadPreparation B) where
  codes : Set M
  containsA : S ⊆ codes
  containsB : R ⊆ codes
  arityA : ℕ
  arityB : ℕ
  targetA : DefSet (M := M) codes 1 arityA
  targetB : DefSet (M := M) codes 1 arityB
  tailA : SpecialBijection (T.extendBase containsA).contractedSet targetA
  tailB : SpecialBijection (U.extendBase containsB).contractedSet targetB
  pullbackA : IsRVPullback (carrier targetA)
  pullbackB : IsRVPullback (carrier targetB)
  graphA : GammaGraphDefinable G (pointMapGraph tailA.toMap)
  graphB : GammaGraphDefinable G (pointMapGraph tailB.toMap)
  targetA_gamma : GammaSetDefinable G (carrier targetA)
  targetB_gamma : GammaSetDefinable G (carrier targetB)
  iso : pullbackObject targetA ≅ pullbackObject targetB
  hom_graph : GammaGraphDefinable G (rvPullbackMapGraph (unaryIsoHomMap iso))
  inv_graph : GammaGraphDefinable G (rvPullbackMapGraph (unaryIsoInvMap iso))

theorem matched_head_completion {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (T : HeadPreparation A) (U : HeadPreparation B)
    (hT : GammaSetDefinable G (carrier T.contractedSet))
    (hU : GammaSetDefinable G (carrier U.contractedSet))
    (e : GammaIso G (carrier T.contractedSet) (carrier U.contractedSet)) :
    Nonempty (MatchedHeadCompletion (G := G) T U) := by
  obtain ⟨Q,hQ⟩ := matched_unary_preparation_over hκ hs hsmall h00 δ hδ hδ1 F
    (S ∪ R) _ _ hT hU e
  let hSQ : S ⊆ Q.codes := fun _ hx => hQ (Or.inl hx)
  let hRQ : R ⊆ Q.codes := fun _ hx => hQ (Or.inr hx)
  exact ⟨{
    codes := Q.codes
    containsA := hSQ
    containsB := hRQ
    arityA := Q.arityA
    arityB := Q.arityB
    targetA := Q.targetA
    targetB := Q.targetB
    tailA := headCompletionTail T hSQ Q.sourceA_eq Q.specialA
    tailB := headCompletionTail U hRQ Q.sourceB_eq Q.specialB
    pullbackA := Q.pullbackA
    pullbackB := Q.pullbackB
    graphA := gamma_headCompletionTail T hSQ Q.sourceA_eq Q.specialA
      (GammaChainDefinable.graph (gammaLogicInput G) Q.specialA.chain Q.gammaA)
    graphB := gamma_headCompletionTail U hRQ Q.sourceB_eq Q.specialB
      (GammaChainDefinable.graph (gammaLogicInput G) Q.specialB.chain Q.gammaB)
    targetA_gamma := GammaChainDefinable.target G Q.specialA.chain Q.gammaA
    targetB_gamma := GammaChainDefinable.target G Q.specialB.chain Q.gammaB
    iso := Q.iso
    hom_graph := Q.hom_graph
    inv_graph := Q.inv_graph }⟩

namespace MatchedHeadCompletion
variable {T : HeadPreparation A} {U : HeadPreparation B}

def preparationA (Q : MatchedHeadCompletion (G := G) T U) :
    HeadPreparation (T.extendBase Q.containsA).contractedSet :=
  ⟨Q.arityA,Q.targetA,Q.tailA.toMap,unary_specialRelative Q.tailA,headSaturated_of_pullback Q.pullbackA⟩

def preparationB (Q : MatchedHeadCompletion (G := G) T U) :
    HeadPreparation (U.extendBase Q.containsB).contractedSet :=
  ⟨Q.arityB,Q.targetB,Q.tailB.toMap,unary_specialRelative Q.tailB,headSaturated_of_pullback Q.pullbackB⟩

def programA (Q : MatchedHeadCompletion (G := G) T U) :
    OrderedContractionProgram Q.codes (extendBase A Q.containsA) (headImage Q.targetA) :=
  .step (T.extendBase Q.containsA) (.step Q.preparationA (.zero (headImage Q.targetA)))

def programB (Q : MatchedHeadCompletion (G := G) T U) :
    OrderedContractionProgram Q.codes (extendBase B Q.containsB) (headImage Q.targetB) :=
  .step (U.extendBase Q.containsB) (.step Q.preparationB (.zero (headImage Q.targetB)))

theorem programA_gamma (Q : MatchedHeadCompletion (G := G) T U)
    (hT : GammaGraphDefinable G (pointMapGraph T.map))
    (hTarget : GammaSetDefinable G (carrier T.target)) : GammaProgramDefinable G Q.programA :=
  ⟨gamma_extendPointMap T.map Q.containsA hT,hTarget,Q.graphA,Q.targetA_gamma,
    gamma_headImage Q.targetA Q.targetA_gamma⟩

theorem programB_gamma (Q : MatchedHeadCompletion (G := G) T U)
    (hU : GammaGraphDefinable G (pointMapGraph U.map))
    (hTarget : GammaSetDefinable G (carrier U.target)) : GammaProgramDefinable G Q.programB :=
  ⟨gamma_extendPointMap U.map Q.containsB hU,hTarget,Q.graphB,Q.targetB_gamma,
    gamma_headImage Q.targetB Q.targetB_gamma⟩

end MatchedHeadCompletion
end IntegrationInACVF.Section5
