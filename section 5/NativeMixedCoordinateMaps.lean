import «section 3».GammaGroundMixedProducts
import «section 5».NativeMixedCodeBridge

/-! Independent selections of actual VF and RV coordinates are original
real-language maps. Coordinate equivalences give native Gamma-ground
bijections onto the corresponding literal images. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r d s : ℕ}

def universalMixedCoordinateMap (S : Set M) (j : Fin d → Fin n) (h : Fin s → Fin r) :
    Map (DefSet.univ (rawMixedSpace (M := M) n r) S) (DefSet.univ (rawMixedSpace d s) S) := by
  let f (q : Section2.Mixed M n r) : Section2.Mixed M d s := (q.1 ∘ j,q.2 ∘ h)
  let F (z : Fin n ⊕ Fin r → M) : Fin d ⊕ Fin s → M := z ∘ Sum.map j h
  have hcode (c : (rawMixedSpace (M := M) n r).domain) :
      mixedValues (f ((rawMixedSpace n r).decode c)) = F c.val := by
    funext i
    cases i with
    | inl t => exact congrFun (mixedValues_decode c) (.inl (j t))
    | inr t => exact congrFun (mixedValues_decode c) (.inr (h t))
  refine Map.ofCodes _ f F (fun _ => Set.DefinableFun.proj LRV)
    (fun c => (hcode c) ▸ mixedValues_mem_domain (f ((rawMixedSpace n r).decode c))) ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode _).trans (hcode c).symm

def nativeMixedCoordinateMap (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (h : Fin s → Fin r) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) d s)) :=
  GammaGroundMap.ofGlobal A _ (universalMixedCoordinateMap B.real j h) (fun _ => Set.mem_univ _)

theorem nativeMixedCoordinateMap_value (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (h : Fin s → Fin r) (a : A) :
    ((nativeMixedCoordinateMap A j h) a).val = (a.val.1 ∘ j,a.val.2 ∘ h) := rfl

theorem nativeMixedCoordinateMap_injective
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (j : Fin d → Fin n) (h : Fin s → Fin r) (hj : Function.Surjective j) (hh : Function.Surjective h) :
    Function.Injective (nativeMixedCoordinateMap A j h) := by
  intro a b hab
  have he : (a.val.1 ∘ j,a.val.2 ∘ h) = (b.val.1 ∘ j,b.val.2 ∘ h) := congrArg Subtype.val hab
  apply Subtype.ext
  apply Prod.ext
  · funext i
    obtain ⟨t,rfl⟩ := hj i
    exact congrFun (congrArg Prod.fst he) t
  · funext i
    obtain ⟨t,rfl⟩ := hh i
    exact congrFun (congrArg Prod.snd he) t

def nativeMixedCoordinateBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (j : Fin d ≃ Fin n) (h : Fin s ≃ Fin r) :
    GammaGroundBijection A (nativeMixedCoordinateMap A j h).image :=
  ⟨(nativeMixedCoordinateMap A j h).toImage,
    (nativeMixedCoordinateMap A j h).toImage_bijective (nativeMixedCoordinateMap_injective A j h j.surjective h.surjective)⟩

end DiamondIntegral.Section5
