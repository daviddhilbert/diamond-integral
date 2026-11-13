import «section 4».GammaWeightedBoundary
import «section 4».GammaPartialEvaluation
import «section 4».EulerEnumeratedExpansion

/-! Uniform canonical point-and-ray decomposition of an actual weighted
Gamma family. The finite boundary graphs carry original-base definable
coefficient weights; each actual fibre is recovered exactly. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCanonicalExpansion
open GammaOrderLogic GammaDefinableEuler GammaFamilyIntegration GammaWeightedFamilies GammaGermFamilies
open GammaPartialEvaluation GammaFiniteGraphPartition EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def activeIndices {B : Base (M := M)} {n : ℕ} {R : Set (Fin (n + 1) → Values.Gamma (M := M))}
    (P : FiniteGraphPartition B R) (y : Fin n → Values.Gamma (M := M)) : Finset (Fin P.size) :=
  Finset.univ.filter (fun i => y ∈ P.domain i)

def pointWeight (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (P : FiniteGraphPartition B (GammaWeightedBoundary.Boundary f)) (i : Fin P.size) :
    (Fin n → Values.Gamma (M := M)) → ℤ :=
  restrictedValue (P.domain i) (P.function i) (pointCoefficientFamily h00 B k f hf)

def rayWeight (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (P : FiniteGraphPartition B (GammaWeightedBoundary.Boundary f)) (i : Fin P.size) :
    (Fin n → Values.Gamma (M := M)) → ℤ :=
  restrictedValue (P.domain i) (P.function i) (rayCoefficientFamily h00 B k f hf)

theorem pointWeight_definable (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (P : FiniteGraphPartition B (GammaWeightedBoundary.Boundary f)) (i : Fin P.size) :
    IntegerFamilyDefinable B (pointWeight h00 B k f hf P i) :=
  restrictedValue_definable B _ (P.domain_definable i) _ (P.graph_definable i) _
    (pointCoefficientFamily_definable h00 B k f hf)

theorem rayWeight_definable (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (P : FiniteGraphPartition B (GammaWeightedBoundary.Boundary f)) (i : Fin P.size) :
    IntegerFamilyDefinable B (rayWeight h00 B k f hf P i) :=
  restrictedValue_definable B _ (P.domain_definable i) _ (P.graph_definable i) _
    (rayCoefficientFamily_definable h00 B k f hf)

theorem breakpoint_indexing (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (P : FiniteGraphPartition B (GammaWeightedBoundary.Boundary f))
    (y : Fin n → Values.Gamma (M := M)) :
    Set.BijOn (fun i => toPaperGamma (P.function i y)) (activeIndices P y : Set (Fin P.size))
      (breakpoints k (fibreFunction h00 B k f hf y) : Set (PaperGamma (M := M))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hy : y ∈ P.domain i := (Finset.mem_filter.mp hi).2
    have hR : Fin.cons (P.function i y) y ∈ GammaWeightedBoundary.Boundary f :=
      (P.covers _).mpr ⟨i, hy, rfl⟩
    exact (mem_breakpoints_iff k _ _).mpr
      ((GammaWeightedBoundary.boundary_iff h00 B k f hf (Fin.cons (P.function i y) y)).mp hR)
  · intro i hi j hj he
    by_contra hij
    have hyi : y ∈ P.domain i := (Finset.mem_filter.mp hi).2
    have hyj : y ∈ P.domain j := (Finset.mem_filter.mp hj).2
    have hraw : P.function j y = P.function i y := (toPaperGamma.injective he).symm
    apply Set.disjoint_left.mp (P.disjoint hij)
      (show Fin.cons (P.function i y) y ∈
        {z : Fin (n + 1) → Values.Gamma (M := M) |
          (fun l => z l.succ) ∈ P.domain i ∧ P.function i (fun l => z l.succ) = z 0} from ⟨hyi, rfl⟩)
      (show Fin.cons (P.function i y) y ∈
        {z : Fin (n + 1) → Values.Gamma (M := M) |
          (fun l => z l.succ) ∈ P.domain j ∧ P.function j (fun l => z l.succ) = z 0} from ⟨hyj, hraw⟩)
  · intro a ha
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective a
    have hR : Fin.cons γ y ∈ GammaWeightedBoundary.Boundary f :=
      (GammaWeightedBoundary.boundary_iff h00 B k f hf (Fin.cons γ y)).mpr
        ((mem_breakpoints_iff k _ _).mp ha)
    obtain ⟨i, hy, he⟩ := (P.covers _).mp hR
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hy⟩, congrArg toPaperGamma he⟩

theorem fibre_expansion (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (P : FiniteGraphPartition B (GammaWeightedBoundary.Boundary f))
    (y : Fin n → Values.Gamma (M := M)) :
    fibreFunction h00 B k f hf y = tailFamily h00 B k f hf y • line k +
      (∑ i : Fin P.size, pointWeight h00 B k f hf P i y • point k (toPaperGamma (P.function i y))) +
      ∑ i : Fin P.size, rayWeight h00 B k f hf P i y • ray k (toPaperGamma (P.function i y)) := by
  let F := fibreFunction h00 B k f hf y
  let v := (coefficientEquiv k).symm F
  let t := fun i : Fin P.size => toPaperGamma (P.function i y)
  have he := coefficient_expansion_of_finite_enumeration k F (activeIndices P y) t
    (breakpoint_indexing h00 B k f hf P y)
  have hp (i : Fin P.size) : pointWeight h00 B k f hf P i y =
      if y ∈ P.domain i then v.2.1 (t i) else 0 := rfl
  have hq (i : Fin P.size) : rayWeight h00 B k f hf P i y =
      if y ∈ P.domain i then v.2.2 (t i) else 0 := rfl
  have hpSum : (∑ i ∈ activeIndices P y, v.2.1 (t i) • point k (t i)) =
      ∑ i : Fin P.size, pointWeight h00 B k f hf P i y • point k (t i) := by
    rw [activeIndices, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp]
    by_cases hy : y ∈ P.domain i <;> simp only [hy, ite_true, ite_false, zero_zsmul]
  have hqSum : (∑ i ∈ activeIndices P y, v.2.2 (t i) • ray k (t i)) =
      ∑ i : Fin P.size, rayWeight h00 B k f hf P i y • ray k (t i) := by
    rw [activeIndices, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [hq]
    by_cases hy : y ∈ P.domain i <;> simp only [hy, ite_true, ite_false, zero_zsmul]
  rw [hpSum, hqSum] at he
  exact he

end DiamondIntegral.Section4.GammaCanonicalExpansion
