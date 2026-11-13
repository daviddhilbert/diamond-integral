import «section 3».RVFamilyObjects
import «section 3».RESScissors

/-! Finite valuation support is preserved by the explicit finite tags
used to realize RV families. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem FiniteFamily.rvObject_res (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (hA : ∀ i, ∀ a : A.piece i, ∀ j, (a.val j).val ≠ iRVZero)
    (h : ∀ i, ((fun t j => Values.vrv (t j)) '' (A.piece i).carrier).Finite) :
    resProperty S k (A.rvObject hA) := by
  let extend (i : Fin A.tags) (γ : Fin k → Section2.GammaInfinity M) :=
    Fin.append (fun j => Values.vrv (rvFamilyTag (M := M) i j)) γ
  have hf := Set.finite_iUnion (fun i => (h i).image (extend i))
  apply hf.subset
  rintro _ ⟨t, ⟨i, u, hu⟩, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, fun j => Values.vrv (u.val j), ⟨u.val, u.property, rfl⟩, ?_⟩
  rw [← hu]
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [extend, rvFamilyTagMap, rvMapOfCode, Map.ofCodes, rvAppend, Fin.append_left]
  · simp only [extend, rvFamilyTagMap, rvMapOfCode, Map.ofCodes, rvAppend, Fin.append_right]

end DiamondIntegral.Section3
