import «section 3».GammaGroundRVProductLaws
import «section 3».GammaGroundMeasuredRVProducts

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n m k l : ℕ}

def gammaGroundRVPackPair (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (a : A) (b : B) : gammaGroundRVProductDomain A B :=
  (gammaGroundRVPack A B).toImage ⟨(a.val, b.val), a.property, b.property⟩

theorem exists_gammaGroundRVPackPair (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (p : gammaGroundRVProductDomain A B) :
    ∃ a : A, ∃ b : B, gammaGroundRVPackPair A B a b = p := by
  obtain ⟨ab, hab⟩ := (gammaGroundRVPack A B).toImage_bijective (gammaGroundRVPack_injective A B) |>.surjective p
  exact ⟨⟨ab.val.1, ab.property.1⟩, ⟨ab.val.2, ab.property.2⟩, hab⟩

@[simp] theorem gammaGroundRVUnpack_pair (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (a : A) (b : B) :
    gammaGroundRVUnpack A B (gammaGroundRVPackPair A B a b) = ⟨(a.val, b.val), a.property, b.property⟩ :=
  GammaGroundMap.inverse_apply _ _ _

@[simp] theorem GammaGroundMeasuredRVObject.product_combined_pair (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) (a : U.underlying.domain) (b : V.underlying.domain) :
    (U.product V).combinedWeight (gammaGroundRVPackPair U.underlying.domain V.underlying.domain a b) =
      U.combinedWeight a * V.combinedWeight b := by
  rw [GammaGroundMeasuredRVObject.product_combined]
  change U.combinedWeight ⟨(gammaGroundRVUnpack _ _ (gammaGroundRVPackPair _ _ a b)).val.1, _⟩ *
    V.combinedWeight ⟨(gammaGroundRVUnpack _ _ (gammaGroundRVPackPair _ _ a b)).val.2, _⟩ = _
  rw [gammaGroundRVUnpack_pair]

end DiamondIntegral.Section3
