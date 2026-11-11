import «section 2».Discs
import Section3.GammaClosureLaws
import Section4.RealPresentations

/-! Finite-radius disc parameters for Lemma 2.18. Definability of a
relation on disc names means definability of the full code preimage and
invariance under equality of the actual DC names. Neither centres nor
radius representatives are silently added to the original ground base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A fixed finite chart records the open/closed designation in each
coordinate. All radii here are actual finite Gamma values. -/
noncomputable def finitePolydiscNames {n : ℕ} (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) : Fin n → DC (M := M) :=
  fun i => if closed i then closedDiscCode (a i) (δ i).val else openDiscCode (a i) (δ i)

/-- A ground-definable relation on a tuple of finite disc names and one
VF output. Existing Gamma parameters have finite support. The underlying
Gamma relation already has a full globally invariant proper-code preimage;
the last field additionally enforces invariance under equal DC names. -/
structure FinitePolydiscRelation (B : ParameterBase M) {n : ℕ} (closed : Fin n → Bool) where
  supportArity : ℕ
  support : Fin supportArity → Gamma M
  support_mem : ∀ j, support j ∈ B.gamma
  relation : GammaParameters.Relation B.real (supportArity + n) (n + 1) (fun _ => .vf)
  invariant : ∀ (a a' : Fin n → VF M) (δ δ' : Fin n → Gamma M),
    finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ' → ∀ x : M,
      Fin.snoc (SpecialTransformations.Section4.vfValues a) x ∈
          relation.fibre (Fin.append support δ) ↔
        Fin.snoc (SpecialTransformations.Section4.vfValues a') x ∈
          relation.fibre (Fin.append support δ')

def FinitePolydiscRelation.fibre {B : ParameterBase M} {n : ℕ} {closed : Fin n → Bool}
    (R : FinitePolydiscRelation B closed) (a : Fin n → VF M) (δ : Fin n → Gamma M) : Set M :=
  {x | Fin.snoc (SpecialTransformations.Section4.vfValues a) x ∈
    R.relation.fibre (Fin.append R.support δ)}

theorem FinitePolydiscRelation.fibre_eq_of_names {B : ParameterBase M} {n : ℕ}
    {closed : Fin n → Bool} (R : FinitePolydiscRelation B closed)
    (a a' : Fin n → VF M) (δ δ' : Fin n → Gamma M)
    (he : finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ') :
    R.fibre a δ = R.fibre a' δ' := Set.ext (R.invariant a a' δ δ' he)

private theorem scalar_fibre_definable (B : ParameterBase M) {n : ℕ}
    (a : Fin n → VF M) (R : Set ((Fin n → M) × M))
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ R}) :
    GammaParameters.DefinableAtBase
      ⟨B.real ∪ Set.range (SpecialTransformations.Section4.vfValues a), B.gamma⟩ .vf
      {x | (SpecialTransformations.Section4.vfValues a, x) ∈ R} := by
  let E : ParameterBase M :=
    ⟨B.real ∪ Set.range (SpecialTransformations.Section4.vfValues a), B.gamma⟩
  have hR' := hR.mono (show B.real ⊆ E.real from Set.subset_union_left) (Set.Subset.refl _)
  have ha (j : Fin n) : GammaParameters.DefinableClosureAtBase E .vf (a j).val :=
    GammaParameters.real_definableAtBase E .vf {(a j).val}
      (definableClosureAt_of_mem (Or.inr (Set.mem_range_self j)) (a j).property)
  have hnames := (GammaParameters.tuple_singleton_definable_base E (fun _ => .vf)
    (SpecialTransformations.Section4.vfValues a) ha).preimage_real
      (fun _ : Fin (n + 1) => .vf) Fin.castSucc
  have hp := (hR'.inter hnames).image_real (fun _ : Fin 1 => Fin.last n)
  change GammaParameters.DefinableOverBase E (fun _ : Fin 1 => .vf)
    {z | (SpecialTransformations.Section4.vfValues a, z 0) ∈ R}
  convert hp using 1
  all_goals try rfl
  ext z
  constructor
  · intro hz
    let w : Fin (n + 1) → M := Fin.snoc (SpecialTransformations.Section4.vfValues a) (z 0)
    have hwR : (Fin.init w, w (Fin.last n)) ∈ R := by simpa [w] using hz
    have hws := hR'.proper w hwR
    refine ⟨w, ⟨hwR, ?_⟩, ?_⟩
    · exact ⟨by simp [w], hws⟩
    · funext j
      fin_cases j
      simp [w]
  · rintro ⟨w, ⟨hwR, hwa, _⟩, he⟩
    have hwa' : Fin.init w = SpecialTransformations.Section4.vfValues a := hwa
    have hwl : w (Fin.last n) = z 0 := congrFun he 0
    change (SpecialTransformations.Section4.vfValues a, z 0) ∈ R
    change (Fin.init w, w (Fin.last n)) ∈ R at hwR
    rwa [hwa', hwl] at hwR

theorem FinitePolydiscRelation.definable_fibre {B : ParameterBase M} {n : ℕ}
    {closed : Fin n → Bool} (R : FinitePolydiscRelation B closed)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    GammaParameters.DefinableAtBase
      ⟨B.real ∪ Set.range (SpecialTransformations.Section4.vfValues a),
        B.gamma ∪ Set.range δ⟩ .vf (R.fibre a δ) := by
  let E : ParameterBase M := ⟨B.real, B.gamma ∪ Set.range δ⟩
  have hQ : GammaParameters.DefinableOverBase E (fun _ => .vf)
      (R.relation.fibre (Fin.append R.support δ)) := by
    refine ⟨R.supportArity + n, Fin.append R.support δ, ?_, R.relation, rfl⟩
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · change Fin.append R.support δ (Fin.castAdd n k) ∈ B.gamma ∪ Set.range δ
      simpa only [Fin.append_left, Set.mem_union] using Or.inl (R.support_mem k)
    · change Fin.append R.support δ (Fin.natAdd R.supportArity k) ∈ B.gamma ∪ Set.range δ
      simpa only [Fin.append_right, Set.mem_union] using Or.inr (Set.mem_range_self k)
  let P : Set ((Fin n → M) × M) :=
    {p | Fin.snoc p.1 p.2 ∈ R.relation.fibre (Fin.append R.support δ)}
  have hP : GammaParameters.DefinableOverBase E (fun _ : Fin (n + 1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ P} := by
    convert hQ using 1
    ext z
    change (Fin.snoc (Fin.init z) (z (Fin.last n)) : Fin (n + 1) → M) ∈
      R.relation.fibre (Fin.append R.support δ) ↔ z ∈ R.relation.fibre (Fin.append R.support δ)
    rw [Fin.snoc_init_self]
  exact scalar_fibre_definable E a P hP

/-- Algebraicity over the actual DC tuple: a finite fibre of a relation
whose entire proper-code preimage is ground-definable and DC-invariant. -/
def AlgebraicOverFinitePolydiscNames (B : ParameterBase M) {n : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) (b : VF M) : Prop :=
  ∃ R : FinitePolydiscRelation B closed, (R.fibre a δ).Finite ∧ b.val ∈ R.fibre a δ

/-- Naming the radii contributes no VF algebraicity. Only the temporary
VF centres remain in this intermediate conclusion. -/
theorem algebraic_over_disc_names_pointwise (B : ParameterBase M) {n : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M) (b : VF M)
    (hb : AlgebraicOverFinitePolydiscNames B closed a δ b) :
    AlgebraicAt (B.real ∪ Set.range (SpecialTransformations.Section4.vfValues a)) .vf b.val := by
  obtain ⟨R, hfin, hb⟩ := hb
  exact (GammaParameters.algebraic_vf_iff_real _ b).mp
    ⟨R.fibre a δ, R.definable_fibre a δ, hfin, hb⟩

end DiamondIntegral.Section2
