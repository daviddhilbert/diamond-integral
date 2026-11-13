import «section 4».GammaCoordinateIsomorphisms
import «section 4».Section3RVProductBridge
import «section 4».Section3GammaChartBridge
import «section 3».GammaGroundMeasuredGammaProductWeights

/-! Cartesian Gamma products agree after the definable permutation of
the two coordinate blocks, with the full original RV lift retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaProductBridge
open Section3GammaChartBridge Section3RVProductBridge FiniteTupleBlocks GammaRVChartPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem append_permute {n m : ℕ} (x : Fin n → Values.Gamma (M := M))
    (y : Fin m → Values.Gamma (M := M)) :
    Fin.append x y ∘ productIndices n m = join n m y x := by
  apply FiniteTupleGraphProduct.block_ext n m
  · funext i
    simp only [Function.comp_apply, productIndices, join_head, Fin.append_right]
  · funext i
    simp only [Function.comp_apply, productIndices, join_tail, Fin.append_left]

def permutation (n m : ℕ) : Fin (n + m) ≃ Fin (n + m) :=
  Equiv.ofBijective (productIndices n m)
    ((Finite.surjective_iff_bijective).mp (productIndices_surjective n m))

theorem product_bijOn {n m : ℕ} (G : GammaGroundGammaPiece hc B n)
    (H : GammaGroundGammaPiece hc B m) :
    Set.BijOn (fun z => z ∘ permutation n m) (chart (gammaGroundGammaAppendMap G H).image).support
      (GammaOrdinaryCharts.product (chart H) (chart G)).support := by
  refine ⟨?_, (permutation n m).surjective.injective_comp_right.injOn, ?_⟩
  · intro z hz
    obtain ⟨p, rfl⟩ := hz
    change (Fin.append p.val.1 p.val.2 ∘ productIndices n m) ∈ GammaProfileProducts.productSet H.carrier G.carrier
    rw [append_permute]
    change ((join n m p.val.2 p.val.1 ∘ headIndex n m) ∈ H.carrier) ∧
      ((join n m p.val.2 p.val.1 ∘ tailIndex n m) ∈ G.carrier)
    simpa only [show join n m p.val.2 p.val.1 ∘ headIndex n m = p.val.2 from funext (join_head n m _ _),
      show join n m p.val.2 p.val.1 ∘ tailIndex n m = p.val.1 from funext (join_tail n m _ _)] using
      And.intro p.property.2 p.property.1
  · intro z hz
    change z ∘ headIndex n m ∈ H.carrier ∧ z ∘ tailIndex n m ∈ G.carrier at hz
    refine ⟨Fin.append (z ∘ tailIndex n m) (z ∘ headIndex n m), ?_, ?_⟩
    · exact ⟨⟨(z ∘ tailIndex n m, z ∘ headIndex n m), hz.2, hz.1⟩, rfl⟩
    · change Fin.append _ _ ∘ productIndices n m = z
      rw [append_permute]
      apply FiniteTupleGraphProduct.block_ext n m
      · funext i; exact join_head n m _ _ i
      · funext i; exact join_tail n m _ _ i

def ordinary {n m : ℕ} (G : GammaGroundGammaPiece hc B n) (H : GammaGroundGammaPiece hc B m) :
    GammaOrdinaryCharts.Iso (chart (gammaGroundGammaAppendMap G H).image)
      (GammaOrdinaryCharts.product (chart H) (chart G)) :=
  GammaCoordinateIsomorphisms.ordinary _ _ (permutation n m) (product_bijOn G H)

end DiamondIntegral.Section4.Section3GammaProductBridge
