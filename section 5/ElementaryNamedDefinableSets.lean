import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.ModelTheory.Definability

/-! Actual sets defined by the same named parameters in an elementary
extension have a canonical restriction equivalence. Equality is reflected
for every ambient tuple, not only for tuples of the smaller model. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language} {M N P : Type} [L.Structure M] [L.Structure N]
variable (e : M ↪ₑ[L] N) (c : P → M) {n : ℕ}

def namedFormulaSet (c : P → M) (φ : L.Formula (P ⊕ Fin n)) : Set (Fin n → M) :=
  {x | φ.Realize (Sum.elim c x)}

theorem elementary_namedFormula_mem (φ : L.Formula (P ⊕ Fin n)) (x : Fin n → M) :
    e ∘ x ∈ namedFormulaSet (e ∘ c) φ ↔ x ∈ namedFormulaSet c φ := by
  have h := e.map_formula φ (Sum.elim c x)
  have he : e ∘ Sum.elim c x = Sum.elim (e ∘ c) (e ∘ x) := by
    funext i
    cases i <;> rfl
  simpa only [he,namedFormulaSet,Set.mem_setOf_eq] using h

theorem elementary_namedFormula_universal (φ : L.Formula (P ⊕ Fin n)) :
    (∀ x : Fin n → N,x ∈ namedFormulaSet (e ∘ c) φ) ↔
      ∀ x : Fin n → M,x ∈ namedFormulaSet c φ := by
  simpa only [Formula.realize_iAlls,namedFormulaSet,Set.mem_setOf_eq] using
    e.map_formula (φ.iAlls (Fin n)) c

theorem elementary_namedFormula_equality (φ ψ : L.Formula (P ⊕ Fin n)) :
    namedFormulaSet (e ∘ c) φ = namedFormulaSet (e ∘ c) ψ ↔
      namedFormulaSet c φ = namedFormulaSet c ψ := by
  rw [Set.ext_iff,Set.ext_iff]
  simpa only [namedFormulaSet,Set.mem_setOf_eq,Formula.realize_iff] using
    elementary_namedFormula_universal e c (φ.iff ψ)

abbrev NamedDefinableSet (c : P → M) (n : ℕ) :=
  {S : Set (Fin n → M) // ∃ φ : L.Formula (P ⊕ Fin n),S = namedFormulaSet c φ}

def NamedDefinableSet.ofFormula (φ : L.Formula (P ⊕ Fin n)) :
    NamedDefinableSet (L := L) c n := ⟨namedFormulaSet c φ,φ,rfl⟩

def elementaryNamedRestriction (S : NamedDefinableSet (L := L) (e ∘ c) n) :
    NamedDefinableSet (L := L) c n := by
  refine ⟨{x | e ∘ x ∈ S.val},?_⟩
  obtain ⟨φ,hφ⟩ := S.property
  refine ⟨φ,?_⟩
  ext x
  simp only [Set.mem_setOf_eq,hφ,elementary_namedFormula_mem]

theorem elementaryNamedRestriction_injective : Function.Injective
    (elementaryNamedRestriction e c (n := n)) := by
  intro S T he
  obtain ⟨φ,hφ⟩ := S.property
  obtain ⟨ψ,hψ⟩ := T.property
  apply Subtype.ext
  rw [hφ,hψ]
  apply (elementary_namedFormula_equality e c φ ψ).mpr
  ext x
  have h := congrArg (fun A : NamedDefinableSet (L := L) c n => x ∈ A.val) he
  change (e ∘ x ∈ S.val) = (e ∘ x ∈ T.val) at h
  simpa only [hφ,hψ,elementary_namedFormula_mem] using h.to_iff

theorem elementaryNamedRestriction_surjective : Function.Surjective
    (elementaryNamedRestriction e c (n := n)) := by
  intro S
  obtain ⟨φ,hφ⟩ := S.property
  refine ⟨NamedDefinableSet.ofFormula (e ∘ c) φ,?_⟩
  apply Subtype.ext
  ext x
  change e ∘ x ∈ namedFormulaSet (e ∘ c) φ ↔ x ∈ S.val
  rw [hφ,elementary_namedFormula_mem]

def elementaryNamedDefinableEquiv :
    NamedDefinableSet (L := L) (e ∘ c) n ≃ NamedDefinableSet (L := L) c n :=
  _root_.Equiv.ofBijective (elementaryNamedRestriction e c)
    ⟨elementaryNamedRestriction_injective e c,elementaryNamedRestriction_surjective e c⟩

variable {e c}

theorem namedDefinable_iff_actual {S : Set (Fin n → M)} :
    (∃ φ : L.Formula (P ⊕ Fin n),S = namedFormulaSet c φ) ↔
      (Set.range c).Definable L S := by
  rw [Set.definable_iff_exists_formula_sum]
  constructor
  · rintro ⟨φ,rfl⟩
    let j : P → Set.range c := fun p => ⟨c p,⟨p,rfl⟩⟩
    refine ⟨φ.relabel (Sum.map j id),?_⟩
    ext x
    simp only [namedFormulaSet,Set.mem_setOf_eq,Formula.realize_relabel]
    apply Iff.of_eq
    congr 1
    funext i
    cases i <;> rfl
  · rintro ⟨φ,rfl⟩
    let r : Set.range c → P := fun a => Classical.choose a.property
    have hr (a : Set.range c) : c (r a) = a.val := Classical.choose_spec a.property
    refine ⟨φ.relabel (Sum.map r id),?_⟩
    ext x
    simp only [namedFormulaSet,Set.mem_setOf_eq,Formula.realize_relabel]
    apply Iff.of_eq
    congr 1
    funext i
    cases i with
    | inl a => exact (hr a).symm
    | inr a => rfl

variable (c)
def namedActualDefinableEquiv :
    NamedDefinableSet (L := L) c n ≃ L.DefinableSet (Set.range c) (Fin n) where
  toFun S := ⟨S.val,namedDefinable_iff_actual.mp S.property⟩
  invFun S := ⟨S.val,namedDefinable_iff_actual.mpr S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (e)
def elementaryActualDefinableEquiv :
    L.DefinableSet (Set.range (e ∘ c)) (Fin n) ≃ L.DefinableSet (Set.range c) (Fin n) :=
  ((namedActualDefinableEquiv (e ∘ c)).symm.trans (elementaryNamedDefinableEquiv e c)).trans
    (namedActualDefinableEquiv c)

theorem elementaryActualDefinableEquiv_carrier
    (S : L.DefinableSet (Set.range (e ∘ c)) (Fin n)) :
    (elementaryActualDefinableEquiv e c S).val = {x | e ∘ x ∈ S.val} := rfl

theorem elementary_namedFormula_exists_row {m : ℕ}
    (φ : L.BoundedFormula (P ⊕ Fin n) m) (x : Fin n → M) :
    (∃ y : Fin m → N,φ.Realize (Sum.elim (e ∘ c) (e ∘ x)) y) ↔
      ∃ y : Fin m → M,φ.Realize (Sum.elim c x) y := by
  have h := e.map_formula φ.exs (Sum.elim c x)
  have he : e ∘ Sum.elim c x = Sum.elim (e ∘ c) (e ∘ x) := by
    funext i
    cases i <;> rfl
  simpa only [he,BoundedFormula.realize_exs] using h

end DiamondIntegral.Section5
