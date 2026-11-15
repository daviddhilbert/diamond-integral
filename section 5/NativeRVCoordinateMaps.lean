import «section 3».GammaGroundRVFamilyObjects

/-! Native original-ground RV coordinate equivalences and deletion of
fixed zero coordinates retain every other RV parameter. All graphs are
the actual original-language projection graphs. -/
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

theorem nativeRVSelectCoordinates_value {m k : ℕ}
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (j : Fin k → Fin m) (x : X) :
    ((gammaGroundRVSelectCoordinates j X) x).val = x.val ∘ j := rfl

theorem nativeRVSelectCoordinates_injective {m k : ℕ}
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (j : Fin k → Fin m)
    (hj : Function.Surjective j) : Function.Injective (gammaGroundRVSelectCoordinates j X) := by
  intro x y h
  apply Subtype.ext
  funext i
  obtain ⟨t,rfl⟩ := hj i
  exact congrArg (fun u : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k) => u.val t) h

def nativeRVCoordinateBijection {m k : ℕ}
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (j : Fin k ≃ Fin m) :
    GammaGroundBijection X (gammaGroundRVSelectCoordinates j X).image :=
  ⟨(gammaGroundRVSelectCoordinates j X).toImage,
    (gammaGroundRVSelectCoordinates j X).toImage_bijective (nativeRVSelectCoordinates_injective X j j.surjective)⟩

def nativeRVZeroBlockIndices (j : Fin d → Fin n) : Fin (d+r) → Fin (n+r) :=
  Fin.addCases (fun i => Fin.castAdd r (j i)) (Fin.natAdd n)

def nativeRVZeroBlockMap (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n+r))) (j : Fin d → Fin n) :
    GammaGroundMap X (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) (d+r))) :=
  gammaGroundRVSelectCoordinates (nativeRVZeroBlockIndices j) X

theorem nativeRVZeroBlockMap_value
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n+r))) (j : Fin d → Fin n) (x : X) :
    ((nativeRVZeroBlockMap X j) x).val = Fin.append (x.val ∘ Fin.castAdd r ∘ j) (x.val ∘ Fin.natAdd n) := by
  funext i
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i <;>
    simp only [nativeRVZeroBlockMap,nativeRVZeroBlockIndices,gammaGroundRVSelectCoordinates,GammaGroundMap.ofGlobal,
      rvSelectCoordinates,Map.ofCodes_apply,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

theorem nativeRVZeroBlockMap_injective
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n+r))) (j : Fin d → Fin n)
    (hz : ∀ x : X,∀ i : Fin n,i ∉ Set.range j → (x.val (Fin.castAdd r i)).val = iRVZero) :
    Function.Injective (nativeRVZeroBlockMap X j) := by
  intro x y h
  have he : x.val ∘ nativeRVZeroBlockIndices j = y.val ∘ nativeRVZeroBlockIndices j := congrArg Subtype.val h
  apply Subtype.ext
  funext i
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i
  · by_cases ht : t ∈ Set.range j
    · obtain ⟨u,rfl⟩ := ht
      have hi := congrFun he (Fin.castAdd r u)
      simpa only [nativeRVZeroBlockIndices,Function.comp_apply,Fin.addCases_left] using hi
    · exact Subtype.ext ((hz x t ht).trans (hz y t ht).symm)
  · have hi := congrFun he (Fin.natAdd d t)
    simpa only [nativeRVZeroBlockIndices,Function.comp_apply,Fin.addCases_right] using hi

def nativeRVZeroBlockBijection
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n+r))) (j : Fin d → Fin n)
    (hz : ∀ x : X,∀ i : Fin n,i ∉ Set.range j → (x.val (Fin.castAdd r i)).val = iRVZero) :
    GammaGroundBijection X (nativeRVZeroBlockMap X j).image :=
  ⟨(nativeRVZeroBlockMap X j).toImage,
    (nativeRVZeroBlockMap X j).toImage_bijective (nativeRVZeroBlockMap_injective X j hz)⟩

end DiamondIntegral.Section5
