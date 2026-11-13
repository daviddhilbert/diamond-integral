import «section 4».Section3GammaChartBridge
import «section 4».Section3GammaRelationBridge
import «section 4».GammaBijectiveRelations

/-! Actual partial Gamma maps, retaining the full original-base graph. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaMapBridge
open GammaOrderLogic FiniteTupleBlocks Section3GammaCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def map {n m : ℕ} {G : GammaGroundGammaPiece hc B n} {H : GammaGroundGammaPiece hc B m}
    (f : GammaGroundMap G H) (γ : Fin n → Values.Gamma (M := M)) : Fin m → Values.Gamma (M := M) :=
  if hγ : γ ∈ G.carrier then (f ⟨γ, hγ⟩).val else fun _ => 1

theorem map_apply {n m : ℕ} {G : GammaGroundGammaPiece hc B n} {H : GammaGroundGammaPiece hc B m}
    (f : GammaGroundMap G H) (a : G) : map f a.val = (f a).val := by
  simp only [map, dite_eq_left a.property]

theorem map_definable {n m : ℕ} {G : GammaGroundGammaPiece hc B n} {H : GammaGroundGammaPiece hc B m}
    (f : GammaGroundMap G H) : GammaDefinable B (GammaBijectiveRelations.graphOn G.carrier (map f)) := by
  have h := (Section3GammaRelationBridge.relation_iff f.graph).mp f.relation_definable
  have he : {z : Fin (m + n) → Values.Gamma (M := M) |
      f.graph (z ∘ headIndex m n) (z ∘ tailIndex m n)} = GammaBijectiveRelations.graphOn G.carrier (map f) := by
    ext z
    change (∃ a : G, a.val = z ∘ headIndex m n ∧ (f a).val = z ∘ tailIndex m n) ↔
      z ∘ headIndex m n ∈ G.carrier ∧ map f (z ∘ headIndex m n) = z ∘ tailIndex m n
    constructor
    · rintro ⟨a, ha, hf⟩
      refine ⟨ha ▸ a.property, ?_⟩
      exact (congrArg (map f) ha).symm.trans ((map_apply f a).trans hf)
    · rintro ⟨hz, he⟩
      exact ⟨⟨z ∘ headIndex m n, hz⟩, rfl, (map_apply f ⟨_, hz⟩).symm.trans he⟩
  exact (congrArg (GammaDefinable B) he).mp h

def nativeMap (hc : CanonicalStructure.IsCanonical (M := M)) {n m : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (F : (Fin n → Values.Gamma (M := M)) → (Fin m → Values.Gamma (M := M)))
    (hF : GammaDefinable B (GammaBijectiveRelations.graphOn I F)) :
    GammaGroundMap (native hc I hI) (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m))) where
  toFun a := ⟨F a.val, Set.mem_univ _⟩
  graph_definable := by
    change GammaGroundRelationDefinable hc B ((volumeGammaSpace hc).power (Fin n))
      ((volumeGammaSpace hc).power (Fin m))
        (fun x y => ∃ a : native hc I hI, a.val = x ∧ F a.val = y)
    apply (Section3GammaRelationBridge.relation_iff _).mpr
    have he : {z : Fin (m + n) → Values.Gamma (M := M) |
        ∃ a : native hc I hI, a.val = z ∘ headIndex m n ∧ F a.val = z ∘ tailIndex m n} =
        GammaBijectiveRelations.graphOn I F := by
      ext z
      change (∃ a : native hc I hI, a.val = z ∘ headIndex m n ∧ F a.val = z ∘ tailIndex m n) ↔
        z ∘ headIndex m n ∈ I ∧ F (z ∘ headIndex m n) = z ∘ tailIndex m n
      constructor
      · rintro ⟨a, ha, he⟩
        exact ⟨ha ▸ a.property, (congrArg F ha).symm.trans he⟩
      · rintro ⟨hz, he⟩
        exact ⟨⟨_, hz⟩, rfl, he⟩
    exact (congrArg (GammaDefinable B) he).mpr hF

end DiamondIntegral.Section4.Section3GammaMapBridge
