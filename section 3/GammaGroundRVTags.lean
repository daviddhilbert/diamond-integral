import «section 3».GammaGroundMapUnions
import Section4.RVTagging

/-! Actual disjoint RV tags and their definable inverses over the full
Gamma ground. The tags are the existing RV zero and one. -/
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
variable {n m : ℕ}

def gammaGroundRVLeftTag (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) (m : ℕ) :
    GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (1 + (n + m)))) :=
  .ofGlobal A _ (rvLeftTagMap (DefSet.univ (rawRVSpace n) ground.real) m) (fun _ => Set.mem_univ _)

def gammaGroundRVRightTag (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (n : ℕ) :
    GammaGroundMap B (GammaGroundDefSet.univ hc ground (rawRVSpace (1 + (n + m)))) :=
  .ofGlobal B _ (rvRightTagMap (DefSet.univ (rawRVSpace m) ground.real) n) (fun _ => Set.mem_univ _)

theorem gammaGroundRVLeftTag_injective (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) (m : ℕ) :
    Function.Injective (gammaGroundRVLeftTag A m) := by
  intro a b he
  exact Subtype.ext (rvLeftTag_injective m (congrArg Subtype.val he))

theorem gammaGroundRVRightTag_injective (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (n : ℕ) :
    Function.Injective (gammaGroundRVRightTag B n) := by
  intro a b he
  exact Subtype.ext (rvRightTag_injective n (congrArg Subtype.val he))

theorem gammaGroundRVTaggedImages_disjoint (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) :
    Disjoint (gammaGroundRVLeftTag A m).image.carrier (gammaGroundRVRightTag B n).image.carrier := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha⟩ ⟨b, hb⟩
  exact rvTag_disjoint a.val b.val (ha.trans hb.symm)

def gammaGroundRVUntagLeft (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) (m : ℕ) :
    GammaGroundMap (gammaGroundRVLeftTag A m).image A :=
  (gammaGroundRVLeftTag A m).toImage.inverse
    ((gammaGroundRVLeftTag A m).toImage_bijective (gammaGroundRVLeftTag_injective A m))

def gammaGroundRVUntagRight (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (n : ℕ) :
    GammaGroundMap (gammaGroundRVRightTag B n).image B :=
  (gammaGroundRVRightTag B n).toImage.inverse
    ((gammaGroundRVRightTag B n).toImage_bijective (gammaGroundRVRightTag_injective B n))

end DiamondIntegral.Section3
