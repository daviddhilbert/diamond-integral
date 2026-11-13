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

def GammaGroundRVHasFiniteMap (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) (k : ℕ) : Prop :=
  ∃ f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)), f.FiniteFibres

theorem gammaGroundRVHasFiniteMap_self (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    GammaGroundRVHasFiniteMap A n :=
  ⟨(GammaGroundMap.id A).toUniv, GammaGroundMap.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun z : GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) n) => z.val) he))⟩

def gammaGroundRVDim (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) : ℕ :=
  Nat.find (show ∃ k, GammaGroundRVHasFiniteMap A k from ⟨n, gammaGroundRVHasFiniteMap_self A⟩)

theorem gammaGroundRVDim_attained (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    GammaGroundRVHasFiniteMap A (gammaGroundRVDim A) := Nat.find_spec _

theorem gammaGroundRVDim_le_of_finite_map (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    {k : ℕ} (hf : GammaGroundRVHasFiniteMap A k) : gammaGroundRVDim A ≤ k := Nat.find_min' _ hf

theorem gammaGroundRVDim_le_arity (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    gammaGroundRVDim A ≤ n := gammaGroundRVDim_le_of_finite_map A (gammaGroundRVHasFiniteMap_self A)

theorem gammaGroundRVDim_le_iff_point_rank
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hγ : GammaRVAlgebraicityInput (M := M) κ)
    (hS : Cardinal.mk ground.real < κ)
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) (k : ℕ) :
    gammaGroundRVDim A ≤ k ↔ ∀ a : A, rvTupleRank hc hex ground.real a.val ≤ k := by
  constructor
  · intro hk a
    obtain ⟨f, hf⟩ := gammaGroundRVDim_attained A
    exact (gammaGroundRVTupleRank_le_of_finite_map hex hκ hγ hS f hf a).trans
      ((rvTupleRank_le_arity hc hex ground.real (f a).val).trans hk)
  · intro hrank
    exact gammaGroundRVDim_le_of_finite_map A
      (gammaGroundRVFiniteMap_of_point_rank hex hκ hs hS A k hrank)

end DiamondIntegral.Section3
