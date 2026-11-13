import «section 4».GammaFunctionProvenance

/-! The converse unary definability bridge, via closure of finite-range
integer functions under finite linear combinations. Every order-cut
generator is defined over exactly its Gamma singleton's original base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaDefinableFunctions
open GammaOrderLogic GammaDefinableEuler EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem empty_definable_base (B : Base (M := M)) :
    GammaDefinableOverBase B (∅ : Set (Values.Gamma (M := M))) := by
  apply (unary_definable_iff B ∅).mp
  unfold GammaDefinable
  convert DefinableOverBase.empty B (fun _ : Fin 1 => .rv) using 1
  ext z
  simp

theorem univ_definable_base (B : Base (M := M)) :
    GammaDefinableOverBase B (Set.univ : Set (Values.Gamma (M := M))) := by
  simpa only [Set.compl_empty] using complement_definable_base B ∅ (empty_definable_base B)

theorem inter_definable_base (B : Base (M := M)) (A C : Set (Values.Gamma (M := M)))
    (hA : GammaDefinableOverBase B A) (hC : GammaDefinableOverBase B C) :
    GammaDefinableOverBase B (A ∩ C) := by
  apply (unary_definable_iff B (A ∩ C)).mp
  exact formula_definable_base B (![A, C] : Fin 2 → Set (Values.Gamma (M := M)))
    (fun i => by fin_cases i; exact hA; exact hC)
    (.and (.unary (n := 1) 0 0) (.unary 1 0))

def IntegerDefinable (B : Base (M := M)) (f : Values.Gamma (M := M) → ℤ) : Prop :=
  (Set.range f).Finite ∧ ∀ m : ℤ, GammaDefinableOverBase B {γ | f γ = m}

theorem integerDefinable_const (B : Base (M := M)) (n : ℤ) :
    IntegerDefinable B (fun _ => n) := by
  refine ⟨(Set.finite_singleton n).subset ?_, ?_⟩
  · rintro m ⟨x, rfl⟩
    rfl
  · intro m
    by_cases h : n = m
    · simpa only [h, Set.ofPred_true] using univ_definable_base B
    · simpa only [h, Set.ofPred_false] using empty_definable_base B

theorem integerDefinable_indicator (B : Base (M := M))
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A) :
    IntegerDefinable B (fun γ => if γ ∈ A then 1 else 0) := by
  refine ⟨(Set.toFinite ({0, 1} : Set ℤ)).subset ?_, ?_⟩
  · rintro m ⟨x, rfl⟩
    by_cases hx : x ∈ A <;> simp [hx]
  · intro m
    by_cases hm1 : m = 1
    · subst m
      have he : {γ | (if γ ∈ A then (1 : ℤ) else 0) = 1} = A := by
        ext γ
        by_cases hγ : γ ∈ A <;> simp [hγ]
      rwa [he]
    · by_cases hm0 : m = 0
      · subst m
        have he : {γ | (if γ ∈ A then (1 : ℤ) else 0) = 0} = Aᶜ := by
          ext γ
          by_cases hγ : γ ∈ A <;> simp [hγ]
        rw [he]
        exact complement_definable_base B A hA
      · have he : {γ | (if γ ∈ A then (1 : ℤ) else 0) = m} = ∅ := by
          ext γ
          by_cases hγ : γ ∈ A <;> simp [hγ, Ne.symm hm1, Ne.symm hm0]
        rw [he]
        exact empty_definable_base B

theorem IntegerDefinable.map {B : Base (M := M)} {f : Values.Gamma (M := M) → ℤ}
    (hf : IntegerDefinable B f) (F : ℤ → ℤ) : IntegerDefinable B (fun γ => F (f γ)) := by
  refine ⟨(hf.1.image F).subset ?_, ?_⟩
  · rintro m ⟨x, rfl⟩
    exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  · intro m
    let s := hf.1.toFinset.filter (fun a => F a = m)
    have he : {γ | F (f γ) = m} = ⋃ a ∈ s, {γ | f γ = a} := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨f γ, Finset.mem_filter.mpr ⟨hf.1.mem_toFinset.mpr ⟨γ, rfl⟩, h⟩, rfl⟩
      · rintro ⟨a, ha, he⟩
        rw [he]
        exact (Finset.mem_filter.mp ha).2
    rw [he]
    exact finite_union_definable_base B s _ (fun a _ => hf.2 a)

theorem IntegerDefinable.add {B : Base (M := M)} {f g : Values.Gamma (M := M) → ℤ}
    (hf : IntegerDefinable B f) (hg : IntegerDefinable B g) :
    IntegerDefinable B (fun γ => f γ + g γ) := by
  refine ⟨(Set.Finite.image2 (fun a b : ℤ => a + b) hf.1 hg.1).subset ?_, ?_⟩
  · rintro m ⟨x, rfl⟩
    exact ⟨f x, ⟨x, rfl⟩, g x, ⟨x, rfl⟩, rfl⟩
  · intro m
    have he : {γ | f γ + g γ = m} =
        ⋃ a ∈ hf.1.toFinset, {γ | f γ = a} ∩ {γ | g γ = m - a} := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h
        refine ⟨f γ, hf.1.mem_toFinset.mpr ⟨γ, rfl⟩, rfl, ?_⟩
        omega
      · rintro ⟨a, _, ha, hg⟩
        omega
    rw [he]
    exact finite_union_definable_base B hf.1.toFinset _
      (fun a _ => inter_definable_base B _ _ (hf.2 a) (hg.2 (m - a)))

theorem integerDefinable_finsetSum {ι : Type} (B : Base (M := M)) (s : Finset ι)
    (f : ι → Values.Gamma (M := M) → ℤ) (hf : ∀ i ∈ s, IntegerDefinable B (f i)) :
    IntegerDefinable B (fun γ => ∑ i ∈ s, f i γ) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using integerDefinable_const B 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem rightRay_definable_base (B : Base (M := M)) (a : Values.Gamma (M := M))
    (ha : GammaDefinableClosureAtBase B a) : GammaDefinableOverBase B {γ | a < γ} := by
  apply (unary_definable_iff B {γ | a < γ}).mp
  have h := formula_definable_base B (fun _ : Unit => ({a} : Set (Values.Gamma (M := M))))
    (fun _ => ha) (.ex (.and (.unary (n := 2) () 0) (.lt 0 1)))
  have he : {z : Fin 1 → Values.Gamma (M := M) |
      Formula.Realize (fun _ : Unit => ({a} : Set (Values.Gamma (M := M))))
        (.ex (.and (.unary () 0) (.lt 0 1))) z} = {z | a < z 0} := by
    ext z
    change (∃ x, x ∈ ({a} : Set (Values.Gamma (M := M))) ∧ x < z 0) ↔ a < z 0
    simp
  rwa [he] at h

theorem point_integerDefinable (B : Base (M := M)) (k : EulerKind)
    (a : PaperGamma (M := M)) (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    IntegerDefinable B (fun γ => point k a (toPaperGamma γ)) := by
  have he : (fun γ : Values.Gamma (M := M) => point k a (toPaperGamma γ)) =
      (fun γ => if γ ∈ ({toPaperGamma.symm a} : Set (Values.Gamma (M := M))) then 1 else 0) := by
    funext γ
    have heq : toPaperGamma γ = a ↔ γ = toPaperGamma.symm a := toPaperGamma.eq_symm_apply.symm
    simp only [point_eval, Set.mem_singleton_iff, heq]
  rw [he]
  convert integerDefinable_indicator B {toPaperGamma.symm a} ha using 1
  funext γ
  split_ifs <;> rfl

theorem ray_integerDefinable (B : Base (M := M)) (k : EulerKind)
    (a : PaperGamma (M := M)) (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    IntegerDefinable B (fun γ => ray k a (toPaperGamma γ)) := by
  have he : (fun γ : Values.Gamma (M := M) => ray k a (toPaperGamma γ)) =
      (fun γ => if γ ∈ {γ : Values.Gamma (M := M) | toPaperGamma.symm a < γ} then 1 else 0) := by
    funext γ
    have hlt : a < toPaperGamma γ ↔ toPaperGamma.symm a < γ := Iff.rfl
    simp only [ray_eval, Set.mem_ofPred_eq, hlt]
  rw [he]
  convert integerDefinable_indicator B {γ | toPaperGamma.symm a < γ}
    (rightRay_definable_base B _ ha) using 1
  funext γ
  split_ifs <;> rfl

theorem linearCombination_integerDefinable (B : Base (M := M)) (k : EulerKind)
    (v : StepCoefficients (PaperGamma (M := M)))
    (hv : ∀ a, v.2.1 a ≠ 0 ∨ v.2.2 a ≠ 0 →
      GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    IntegerDefinable B (fun γ => linearCombination k v (toPaperGamma γ)) := by
  have hp : IntegerDefinable B
      (fun γ => ∑ a ∈ v.2.1.support, v.2.1 a * point k a (toPaperGamma γ)) :=
    integerDefinable_finsetSum B v.2.1.support _ (fun a ha =>
      (point_integerDefinable B k a (hv a (Or.inl (Finsupp.mem_support_iff.mp ha)))).map
        (fun m => v.2.1 a * m))
  have hq : IntegerDefinable B
      (fun γ => ∑ a ∈ v.2.2.support, v.2.2 a * ray k a (toPaperGamma γ)) :=
    integerDefinable_finsetSum B v.2.2.support _ (fun a ha =>
      (ray_integerDefinable B k a (hv a (Or.inr (Finsupp.mem_support_iff.mp ha)))).map
        (fun m => v.2.2 a * m))
  have h := ((integerDefinable_const B v.1).add hp).add hq
  have he (γ : Values.Gamma (M := M)) : linearCombination k v (toPaperGamma γ) =
      v.1 + (∑ a ∈ v.2.1.support, v.2.1 a * point k a (toPaperGamma γ)) +
        ∑ a ∈ v.2.2.support, v.2.2 a * ray k a (toPaperGamma γ) := by
    simp only [linearCombination, eval_add, eval_finsuppSum, eval_zsmul, line_eval]
    simp only [zsmul_eq_mul, Int.cast_id, mul_one, Finsupp.sum]
  simpa only [he] using h

theorem integerDefinable_iff_coefficients (B : Base (M := M)) (k : EulerKind)
    (g : EulerFunction k (PaperGamma (M := M))) :
    IntegerDefinable B (fun γ => g (toPaperGamma γ)) ↔
      ∀ a, ((coefficientEquiv k).symm g).2.1 a ≠ 0 ∨
        ((coefficientEquiv k).symm g).2.2 a ≠ 0 →
          GammaDefinableClosureAtBase B (toPaperGamma.symm a) := by
  constructor
  · intro hg a ha
    exact GammaFunctionProvenance.coefficient_threshold_definable_base B k g hg.2 a ha
  · intro hg
    have h := linearCombination_integerDefinable B k ((coefficientEquiv k).symm g) hg
    have he : linearCombination k ((coefficientEquiv k).symm g) = g := by
      rw [← ofCoefficients_eq_linearCombination]
      exact (coefficientEquiv k).apply_symm_apply g
    rwa [he] at h

end DiamondIntegral.Section4.GammaDefinableFunctions
