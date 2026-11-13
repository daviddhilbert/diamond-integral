import «section 4».FieldPositiveExpressions

/-! Positive expressions depend on finitely many generators. Their set
domains and ring evaluations respect agreement on just those generators. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FieldPositiveExpressions
variable {ι : Type*}

theorem Expr.eval_congr {R : Type*} [Semiring R] (e : Expr ι) (v w : ι → R)
    (h : ∀ i ∈ e.vars, v i = w i) : e.eval v = e.eval w := by
  induction e with
  | zero => rfl
  | one => rfl
  | atom i => exact h i (Finset.mem_singleton_self i)
  | add a b ha hb =>
    exact congrArg₂ (· + ·) (ha (fun i hi => h i (Finset.mem_union_left _ hi)))
      (hb (fun i hi => h i (Finset.mem_union_right _ hi)))
  | mul a b ha hb =>
    exact congrArg₂ (· * ·) (ha (fun i hi => h i (Finset.mem_union_left _ hi)))
      (hb (fun i hi => h i (Finset.mem_union_right _ hi)))

theorem Expr.eval_hom {R S : Type*} [Semiring R] [Semiring S]
    (e : Expr ι) (v : ι → R) (f : R →+* S) : f (e.eval v) = e.eval (f ∘ v) := by
  induction e with
  | zero => exact map_zero f
  | one => exact map_one f
  | atom i => rfl
  | add a b ha hb => simpa only [Expr.eval, map_add, ha, hb]
  | mul a b ha hb => simpa only [Expr.eval, map_mul, ha, hb]

theorem Expr.domain_congr {F : Type*} [Field F] (arity : ι → ℕ)
    (D E : ∀ i, Set (Fin (arity i) → F)) (e : Expr ι)
    (h : ∀ i ∈ e.vars, D i = E i) : e.domain arity D = e.domain arity E := by
  induction e with
  | zero => rfl
  | one => rfl
  | atom i => exact h i (Finset.mem_singleton_self i)
  | add a b ha hb =>
    have hA := ha (fun i hi => h i (Finset.mem_union_left _ hi))
    have hB := hb (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [Expr.domain, hA, hB]
  | mul a b ha hb =>
    have hA := ha (fun i hi => h i (Finset.mem_union_left _ hi))
    have hB := hb (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [Expr.domain, hA, hB]

end DiamondIntegral.Section4.FieldPositiveExpressions
