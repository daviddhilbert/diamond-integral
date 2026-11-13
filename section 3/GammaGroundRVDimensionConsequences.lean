import «section 3».GammaGroundRVDimension
import «section 3».GammaGroundRVRankUpper
import «section 3».GammaGroundRVFiniteMapRank
import «section 3».GammaGroundRealization
import «section 3».GammaGroundFiniteGluing
import Section4.RVDimensionRank
import Section4.GammaRVIndependence
import Section3.GammaProjection
import «section 3».GammaGroundRealFibres
import «section 3».GammaGroundMapImages
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundSyntaxBridge
import Section4.RelationFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {n : ℕ}

theorem gammaGroundRVDim_eq_zero_iff_finite
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    gammaGroundRVDim A = 0 ↔ A.carrier.Finite := by
  constructor
  · intro he
    have hmap := gammaGroundRVDim_attained A
    rw [he] at hmap
    obtain ⟨f, hf⟩ := hmap
    let b : GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) 0) := ⟨Fin.elim0, Set.mem_univ _⟩
    apply ((hf b).image (fun a : A => a.val)).subset
    intro x hx
    refine ⟨⟨x, hx⟩, Subtype.ext (funext (fun i : Fin 0 => i.elim0)), rfl⟩
  · intro hA
    apply Nat.eq_zero_of_le_zero
    apply gammaGroundRVDim_le_of_finite_map A
    let f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) 0)) :=
      GammaGroundMap.ofGlobal _ _ (Map.toSubsingleton
        (DefSet.univ (rawRVSpace (M := M) n) ground.real) (rawRVSpace 0)) (fun _ => Set.mem_univ _)
    exact ⟨f, fun b => (hA.preimage Subtype.val_injective.injOn).subset (fun a _ => a.property)⟩

theorem gammaGroundRVDim_ofReal
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hγ : GammaRVAlgebraicityInput (M := M) κ)
    (hS : Cardinal.mk ground.real < κ)
    (A : DefSet (rawRVSpace (M := M) n) ground.real) :
    gammaGroundRVDim (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A) = rvDim A := by
  apply Nat.le_antisymm
  · apply (gammaGroundRVDim_le_iff_point_rank hex hκ hs hγ hS _ _).mpr
    intro a
    exact rvTupleRank_le_rvDim hc hex A a
  · apply (rvDim_le_iff_point_rank hc hex hs hS A _).mpr
    exact (gammaGroundRVDim_le_iff_point_rank hex hκ hs hγ hS
      (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A) _).mp le_rfl

def gammaGroundRVDimension (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) : WithBot ℕ :=
  if A.carrier.Nonempty then (gammaGroundRVDim A : WithBot ℕ) else ⊥

@[simp] theorem gammaGroundRVDimension_eq_bot_iff
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    gammaGroundRVDimension A = ⊥ ↔ A.carrier = ∅ := by
  by_cases hA : A.carrier.Nonempty
  · simp [gammaGroundRVDimension, hA, Set.nonempty_iff_ne_empty.mp hA]
  · simp [gammaGroundRVDimension, hA, Set.not_nonempty_iff_eq_empty.mp hA]

end DiamondIntegral.Section3
