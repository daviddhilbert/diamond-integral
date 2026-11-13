import «section 3».GammaGroundMapImages
import Section4.VFCoproductBounds

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
variable {n r m s : ℕ}

def gammaGroundMixedLeftTag (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (m s : ℕ) :
    GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawMixedSpace (n + m) (1 + (r + s)))) :=
  GammaGroundMap.ofGlobal A _ (mixedLeftTagMap (DefSet.univ _ ground.real) m s) (fun _ => Set.mem_univ _)

def gammaGroundMixedRightTag (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) (n r : ℕ) :
    GammaGroundMap B (GammaGroundDefSet.univ hc ground (rawMixedSpace (n + m) (1 + (r + s)))) :=
  GammaGroundMap.ofGlobal B _ (mixedRightTagMap (DefSet.univ _ ground.real) n r) (fun _ => Set.mem_univ _)

theorem gammaGroundMixedLeftTag_injective (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (m s : ℕ) :
    Function.Injective (gammaGroundMixedLeftTag A m s) := by
  intro a b he
  exact Subtype.ext (mixedLeftTag_injective m s (congrArg Subtype.val he))

theorem gammaGroundMixedRightTag_injective (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) (n r : ℕ) :
    Function.Injective (gammaGroundMixedRightTag B n r) := by
  intro a b he
  exact Subtype.ext (mixedRightTag_injective n r (congrArg Subtype.val he))

theorem gammaGroundMixedTaggedImages_disjoint
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) :
    Disjoint (gammaGroundMixedLeftTag A m s).image.carrier (gammaGroundMixedRightTag B n r).image.carrier := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  exact mixedTag_disjoint a.val b.val (ha.trans hb.symm)

theorem gammaGroundFiniteRVFibres_leftTag
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) (m s : ℕ)
    (hA : ∀ a, {t | (a, t) ∈ A.carrier}.Finite) :
    ∀ a, {t | (a, t) ∈ (gammaGroundMixedLeftTag A m s).image.carrier}.Finite := by
  intro a
  apply ((hA (a ∘ Fin.castAdd m)).image (rvLeftTag s)).subset
  rintro t ⟨u, hu⟩
  change mixedLeftTag m s u.val = (a, t) at hu
  have hx : u.val.1 = a ∘ Fin.castAdd m := by
    funext i
    simpa only [mixedLeftTag, vfAppend, Fin.append_left, Function.comp_apply] using
      congrFun (congrArg Prod.fst hu) (Fin.castAdd m i)
  refine ⟨u.val.2, ?_, congrArg Prod.snd hu⟩
  change (a ∘ Fin.castAdd m, u.val.2) ∈ A.carrier
  rw [← hx]
  exact u.property

theorem gammaGroundFiniteRVFibres_rightTag
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) (n r : ℕ)
    (hB : ∀ b, {t | (b, t) ∈ B.carrier}.Finite) :
    ∀ b, {t | (b, t) ∈ (gammaGroundMixedRightTag B n r).image.carrier}.Finite := by
  intro b
  apply ((hB (b ∘ Fin.natAdd n)).image (rvRightTag r)).subset
  rintro t ⟨u, hu⟩
  change mixedRightTag n r u.val = (b, t) at hu
  have hx : u.val.1 = b ∘ Fin.natAdd n := by
    funext i
    simpa only [mixedRightTag, vfAppend, Fin.append_right, Function.comp_apply] using
      congrFun (congrArg Prod.fst hu) (Fin.natAdd n i)
  refine ⟨u.val.2, ?_, congrArg Prod.snd hu⟩
  change (b ∘ Fin.natAdd n, u.val.2) ∈ B.carrier
  rw [← hx]
  exact u.property

end DiamondIntegral.Section3
