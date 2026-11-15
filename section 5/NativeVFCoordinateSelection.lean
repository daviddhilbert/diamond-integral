import «section 3».GammaGroundMixedProducts
import «section 5».NativeMixedCodeBridge

/-! A fixed selection of VF coordinates is an actual original-language
map. On a stratum where every omitted VF coordinate is zero, it gives a
native Gamma-ground bijection onto its image and retains all RV labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r d : ℕ}

def universalMixedVFSelection (S : Set M) (j : Fin d → Fin n) :
    Map (DefSet.univ (rawMixedSpace (M := M) n r) S) (DefSet.univ (rawMixedSpace d r) S) := by
  let f (q : Section2.Mixed M n r) : Section2.Mixed M d r := (q.1 ∘ j,q.2)
  let F (z : Fin n ⊕ Fin r → M) : Fin d ⊕ Fin r → M := z ∘ Sum.map j id
  have hcode (c : (rawMixedSpace (M := M) n r).domain) :
      mixedValues (f ((rawMixedSpace n r).decode c)) = F c.val := by
    funext i
    cases i with
    | inl t => exact congrFun (mixedValues_decode c) (.inl (j t))
    | inr t => exact congrFun (mixedValues_decode c) (.inr t)
  refine Map.ofCodes _ f F (fun _ => Set.DefinableFun.proj LRV)
    (fun c => (hcode c) ▸ mixedValues_mem_domain (f ((rawMixedSpace n r).decode c))) ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode _).trans (hcode c).symm

def nativeVFCoordinateSelection (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) d r)) :=
  GammaGroundMap.ofGlobal A _ (universalMixedVFSelection B.real j) (fun _ => Set.mem_univ _)

theorem nativeVFCoordinateSelection_value (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (a : A) :
    ((nativeVFCoordinateSelection A j) a).val = (a.val.1 ∘ j,a.val.2) := rfl

theorem nativeVFCoordinateSelection_injective
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n)
    (hzero : ∀ a : A,∀ i : Fin n,i ∉ Set.range j → a.val.1 i = 0) :
    Function.Injective (nativeVFCoordinateSelection A j) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  change (a.val.1 ∘ j,a.val.2) = (b.val.1 ∘ j,b.val.2) at h
  have hr : a.val.2 = b.val.2 := congrArg (fun q : Section2.Mixed M d r => q.2) h
  apply Subtype.ext
  refine Prod.ext (funext (fun i => ?_)) hr
  by_cases hi : i ∈ Set.range j
  · obtain ⟨t,rfl⟩ := hi
    exact congrFun (congrArg Prod.fst h) t
  · exact (hzero a i hi).trans (hzero b i hi).symm

def nativeDropZeroVFBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n)
    (hzero : ∀ a : A,∀ i : Fin n,i ∉ Set.range j → a.val.1 i = 0) :
    GammaGroundBijection A (nativeVFCoordinateSelection A j).image :=
  ⟨(nativeVFCoordinateSelection A j).toImage,
    (nativeVFCoordinateSelection A j).toImage_bijective (nativeVFCoordinateSelection_injective A j hzero)⟩

theorem nativeDropZeroVF_nonzero
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d → Fin n)
    (hnonzero : ∀ a : A,∀ t : Fin d,a.val.1 (j t) ≠ 0)
    (a : (nativeVFCoordinateSelection A j).image) (i : Fin d) : a.val.1 i ≠ 0 := by
  obtain ⟨b,hb⟩ := a.property
  change ((nativeVFCoordinateSelection A j) b).val = a.val at hb
  exact (congrArg (fun q : Section2.Mixed M d r => q.1 i) hb) ▸ hnonzero b i

end DiamondIntegral.Section5
