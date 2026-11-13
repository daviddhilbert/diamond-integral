import «section 3».GammaGroundRVFamilyMaps
import «section 3».GammaGroundRVCategories

/-! A finite tagged family of subsets of nonzero RV^k is an actual
RV[k] object. The finite-to-one map forgets precisely the finite tag. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundRVSelectCoordinates {n k : ℕ} (π : Fin k → Fin n)
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace k)) :=
  GammaGroundMap.ofGlobal _ _ (rvSelectCoordinates π (DefSet.univ (rawRVSpace n) ground.real)) (fun _ => Set.mem_univ _)

def GammaGroundFiniteFamily.rvTarget (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k)) :
    GammaGroundMap A.rvRealization (GammaGroundDefSet.univ hc ground (rawRVSpace k)) :=
  gammaGroundRVSelectCoordinates (fun i => Fin.natAdd A.tags i) A.rvRealization

theorem GammaGroundFiniteFamily.rvTarget_finite (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k)) :
    A.rvTarget.FiniteFibres := by
  intro t
  have hf := Set.finite_range (fun i : Fin A.tags => rvAppend (rvFamilyTag (M := M) i) t.val)
  apply (hf.preimage (show Function.Injective (fun a : A.rvRealization => a.val) from
    Subtype.val_injective).injOn).subset
  intro a ha
  obtain ⟨i, u, hu⟩ := a.property
  have hut : u.val = t.val := by
    funext j
    have he := congrArg (fun b : GammaGroundDefSet.univ hc ground (rawRVSpace k) => b.val j) ha
    change a.val (Fin.natAdd A.tags j) = t.val j at he
    rw [← hu] at he
    simpa only [gammaGroundRVFamilyTagMap, GammaGroundMap.ofGlobal, rvFamilyTagMap, rvMapOfCode, Map.ofCodes, rvAppend, Fin.append_right] using he
  refine ⟨i, ?_⟩
  rw [← hut]
  exact hu

def GammaGroundFiniteFamily.rvObject (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k))
    (hA : ∀ i, ∀ a : A.piece i, ∀ j, (a.val j).val ≠ iRVZero) : GammaGroundRVObject hc ground k where
  arity := A.tags + k
  domain := A.rvRealization
  volume := A.rvTarget
  finite := A.rvTarget_finite
  nonzero a j := by
    obtain ⟨i, u, hu⟩ := a.property
    change (a.val (Fin.natAdd A.tags j)).val ≠ iRVZero
    rw [← hu]
    simpa only [gammaGroundRVFamilyTagMap, GammaGroundMap.ofGlobal, rvFamilyTagMap, rvMapOfCode, Map.ofCodes, rvAppend, Fin.append_right] using hA i u j

def gammaGroundRVFamilyIso {A B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k)}
    (hA : ∀ i, ∀ a : A.piece i, ∀ j, (a.val j).val ≠ iRVZero)
    (hB : ∀ i, ∀ a : B.piece i, ∀ j, (a.val j).val ≠ iRVZero)
    (f : GammaGroundFamilyBijection A B) : A.rvObject hA ≅ B.rvObject hB :=
  asIso (show A.rvObject hA ⟶ B.rvObject hB from f.rvRealization)

end DiamondIntegral.Section3
