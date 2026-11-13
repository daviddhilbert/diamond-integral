import «section 3».RVFamilyMaps

/-! A finite tagged family of subsets of nonzero RV^k is an actual
RV[k] object. The finite-to-one map forgets precisely the finite tag. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def FiniteFamily.rvTarget (A : FiniteFamily (rawRVSpace (M := M) k) S) :
    Map A.rvRealization (DefSet.univ (rawRVSpace k) S) :=
  rvSelectCoordinates (fun i => Fin.natAdd A.tags i) A.rvRealization

theorem FiniteFamily.rvTarget_finite (A : FiniteFamily (rawRVSpace (M := M) k) S) :
    A.rvTarget.FiniteFibres := by
  intro t
  have hf := Set.finite_range (fun i : Fin A.tags => rvAppend (rvFamilyTag (M := M) i) t.val)
  apply (hf.preimage (show Function.Injective (fun a : A.rvRealization => a.val) from
    Subtype.val_injective).injOn).subset
  intro a ha
  obtain ⟨i, u, hu⟩ := a.property
  have hut : u.val = t.val := by
    funext j
    have he := congrArg (fun b : DefSet.univ (rawRVSpace k) S => b.val j) ha
    change a.val (Fin.natAdd A.tags j) = t.val j at he
    rw [← hu] at he
    simpa only [rvFamilyTagMap, rvMapOfCode, Map.ofCodes, rvAppend, Fin.append_right] using he
  refine ⟨i, ?_⟩
  rw [← hut]
  exact hu

def FiniteFamily.rvObject (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (hA : ∀ i, ∀ a : A.piece i, ∀ j, (a.val j).val ≠ iRVZero) : RVObject S k where
  arity := A.tags + k
  domain := A.rvRealization
  volume := A.rvTarget
  finite := A.rvTarget_finite
  nonzero a j := by
    obtain ⟨i, u, hu⟩ := a.property
    change (a.val (Fin.natAdd A.tags j)).val ≠ iRVZero
    rw [← hu]
    simpa only [rvFamilyTagMap, rvMapOfCode, Map.ofCodes, rvAppend, Fin.append_right] using hA i u j

def rvFamilyIso {A B : FiniteFamily (rawRVSpace (M := M) k) S}
    (hA : ∀ i, ∀ a : A.piece i, ∀ j, (a.val j).val ≠ iRVZero)
    (hB : ∀ i, ∀ a : B.piece i, ∀ j, (a.val j).val ≠ iRVZero)
    (f : FamilyBijection A B) : A.rvObject hA ≅ B.rvObject hB :=
  asIso (show A.rvObject hA ⟶ B.rvObject hB from f.rvRealization)

end DiamondIntegral.Section3
