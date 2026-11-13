import «section 4».GammaFamilySlices
import «section 4».GammaFamilyIntegration

/-! Keep two Gamma coordinates free while naming a finite suffix tuple.
The slice and its integer-valued level sets retain full RV-code fibres. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFamilySlicesTwo
open GammaOrderLogic GammaRelationLogic GammaQuantifierLogic GammaBaseExtension GammaFamilyIntegration

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem slice_definable_base (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 2) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (y : Fin n → Values.Gamma (M := M)) :
    GammaDefinable (withGamma B (Set.range y))
      {u : Fin 2 → Values.Gamma (M := M) | Fin.cons (u 0) (Fin.cons (u 1) y) ∈ R} := by
  let B' := withGamma B (Set.range y)
  have hfix (i : Fin n) : GammaDefinable B'
      {z : Fin (n + 2) → Values.Gamma (M := M) | z i.succ.succ = y i} :=
    preimage_definable_base B' _ ((unary_definable_iff B' {y i}).mpr
      (gammaName_extend B (Set.range y) (y i) (Set.mem_range_self i))) (fun _ : Fin 1 => i.succ.succ)
  have hA := inter_definable_base B' R _ (gammaRelation_extend B (Set.range y) hR)
    (finite_iInter_definable_base B' _ hfix)
  let π : Fin 2 → Fin (n + 2) := ![0, (0 : Fin (n + 1)).succ]
  have hπ : Function.Injective π := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [π]
  have h := image_definable_base B' _ hA π hπ
  convert h using 1
  ext u
  change Fin.cons (u 0) (Fin.cons (u 1) y) ∈ R ↔
    ∃ z ∈ R ∩ (⋂ i : Fin n, {z | z i.succ.succ = y i}), z ∘ π = u
  constructor
  · intro hu
    refine ⟨Fin.cons (u 0) (Fin.cons (u 1) y), ⟨hu, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq, Fin.cons_succ, implies_true]
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨z, ⟨hzR, hz⟩, he⟩
    have hzero : z 0 = u 0 := congrFun he 0
    have hone : z (0 : Fin (n + 1)).succ = u 1 := congrFun he 1
    have htail (i : Fin n) : z i.succ.succ = y i := Set.mem_iInter.mp hz i
    have hez : Fin.cons (u 0) (Fin.cons (u 1) y) = z := by
      funext i
      exact Fin.cases hzero.symm (fun j => Fin.cases hone.symm (fun l => (htail l).symm) j) i
    rwa [hez]

def sliceTwo {n : ℕ} (f : (Fin (n + 2) → Values.Gamma (M := M)) → ℤ)
    (y : Fin n → Values.Gamma (M := M)) (u : Fin 2 → Values.Gamma (M := M)) : ℤ :=
  f (Fin.cons (u 0) (Fin.cons (u 1) y))

theorem sliceTwo_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin (n + 2) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) :
    IntegerFamilyDefinable (withGamma B (Set.range y)) (sliceTwo f y) := by
  refine ⟨hf.1.subset ?_, ?_⟩
  · rintro m ⟨u, rfl⟩
    exact ⟨Fin.cons (u 0) (Fin.cons (u 1) y), rfl⟩
  · intro m
    exact slice_definable_base B {z | f z = m} (hf.2 m) y

end DiamondIntegral.Section4.GammaFamilySlicesTwo
