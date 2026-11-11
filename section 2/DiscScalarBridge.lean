import «section 2».DiscTupleLogic

/-! The scalar disc-parameter interface used for algebraicity and the
mixed-tuple interface used for atomicity define the same unary VF sets.
The conversions retain the full invariant Gamma-code relation, its finite
ground support, and every actual DC name. No centre or radius is added to
the base by this bridge. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem append_vf_vf (n : ℕ) :
    Fin.append (fun _ : Fin n => SortTag.vf) (fun _ : Fin 1 => .vf) =
      (fun _ : Fin (n+1) => .vf) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-- Repackage a scalar relation as a unary VF tuple relation. -/
def FinitePolydiscRelation.toTuple {B : ParameterBase M} {n : ℕ}
    {closed : Fin n → Bool} (R : FinitePolydiscRelation B closed) :
    FiniteDiscTupleRelation B closed (fun _ : Fin 1 => .vf) where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := {
    carrier := R.relation.carrier
    definable := R.relation.definable
    proper := by
      intro p hp
      simpa only [append_vf_vf] using R.relation.proper p hp
    invariant := R.relation.invariant }
  invariant := by
    intro a a' δ δ' he x
    simpa only [GammaParameters.Relation.fibre, Fin.append_right_eq_snoc] using R.invariant a a' δ δ' he (x 0)

theorem FinitePolydiscRelation.toTuple_fibre {B : ParameterBase M} {n : ℕ}
    {closed : Fin n → Bool} (R : FinitePolydiscRelation B closed)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    R.toTuple.fibre a δ = {x : Fin 1 → M | x 0 ∈ R.fibre a δ} := by
  ext x
  change Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
    R.relation.fibre (Fin.append R.support δ) ↔ _
  rw [Fin.append_right_eq_snoc]
  rfl

/-- Repackage a unary VF tuple relation in the scalar interface. -/
def FiniteDiscTupleRelation.toScalar {B : ParameterBase M} {n : ℕ}
    {closed : Fin n → Bool}
    (R : FiniteDiscTupleRelation B closed (fun _ : Fin 1 => .vf)) :
    FinitePolydiscRelation B closed where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := {
    carrier := R.relation.carrier
    definable := R.relation.definable
    proper := by
      intro p hp
      simpa only [append_vf_vf] using R.relation.proper p hp
    invariant := R.relation.invariant }
  invariant := by
    intro a a' δ δ' he x
    simpa only [GammaParameters.Relation.fibre, Fin.append_right_eq_snoc] using
      R.invariant a a' δ δ' he (fun _ : Fin 1 => x)

theorem FiniteDiscTupleRelation.toScalar_fibre {B : ParameterBase M} {n : ℕ}
    {closed : Fin n → Bool}
    (R : FiniteDiscTupleRelation B closed (fun _ : Fin 1 => .vf))
    (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    R.toScalar.fibre a δ = {x : M | (fun _ : Fin 1 => x) ∈ R.fibre a δ} := by
  ext x
  change Fin.snoc (SpecialTransformations.Section4.vfValues a) x ∈
    R.relation.fibre (Fin.append R.support δ) ↔ _
  change _ ↔ Fin.append (SpecialTransformations.Section4.vfValues a)
    (fun _ : Fin 1 => x) ∈ R.relation.fibre (Fin.append R.support δ)
  rw [Fin.append_right_eq_snoc (SpecialTransformations.Section4.vfValues a)
    (fun _ : Fin 1 => x)]

/-- Exact equivalence at the original real/Gamma base and actual disc names. -/
theorem definableOverFiniteDiscNames_unary_iff (B : ParameterBase M) {n : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) (A : Set M) :
    DefinableOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf)
        {x | x 0 ∈ A} ↔
      ∃ R : FinitePolydiscRelation B closed, R.fibre a δ = A := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R.toScalar, ?_⟩
    rw [R.toScalar_fibre, hR]
    rfl
  · rintro ⟨R, hR⟩
    exact ⟨R.toTuple, by rw [R.toTuple_fibre, hR]⟩

theorem algebraicOverFinitePolydiscNames_iff (B : ParameterBase M) {n : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) (b : VF M) :
    AlgebraicOverFinitePolydiscNames B closed a δ b ↔
      ∃ A : Set M, DefinableOverFiniteDiscNames B closed a δ
        (fun _ : Fin 1 => .vf) {x | x 0 ∈ A} ∧ A.Finite ∧ b.val ∈ A := by
  constructor
  · rintro ⟨R, hfin, hb⟩
    exact ⟨R.fibre a δ, (definableOverFiniteDiscNames_unary_iff B closed a δ _).mpr
      ⟨R, rfl⟩, hfin, hb⟩
  · rintro ⟨A, hA, hfin, hb⟩
    obtain ⟨R, rfl⟩ := (definableOverFiniteDiscNames_unary_iff B closed a δ A).mp hA
    exact ⟨R, hfin, hb⟩

end DiamondIntegral.Section2
