import Mathlib.ModelTheory.Algebra.Ring.Definability
import Mathlib.ModelTheory.Definability
import Mathlib.Analysis.Complex.Basic

/-! Constructible subsets of `ℂ^α`, as sets definable in the language of rings with parameters.

* `rdef_zero`, `rdef_ne`: the zero set of a polynomial and its complement.
* `rdef_preimage_poly`: the preimage of a constructible set under a polynomial map is
  constructible. -/

set_option autoImplicit false

noncomputable section

open FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section8.RingDefinable

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- A constructible subset of `ℂ^α`. -/
abbrev RDef {α : Type} (X : Set (α → ℂ)) : Prop := (Set.univ : Set ℂ).Definable Language.ring X

variable {α : Type}

theorem rdef_zero (G : MvPolynomial α ℂ) : RDef {c : α → ℂ | MvPolynomial.eval c G = 0} := by
  have h := FirstOrder.Ring.mvPolynomial_zeroLocus_definable ({G} : Finset (MvPolynomial α ℂ))
  have h' := h.mono (Set.subset_univ _)
  convert h' using 1
  rw [Finset.coe_singleton, MvPolynomial.zeroLocus_span]
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, MvPolynomial.aeval_eq_eval]

theorem rdef_ne (G : MvPolynomial α ℂ) : RDef {c : α → ℂ | MvPolynomial.eval c G ≠ 0} := by
  have h := (rdef_zero G).compl
  convert h using 1
  ext c
  rfl

theorem rdef_univ : RDef (Set.univ : Set (α → ℂ)) := Set.definable_univ

theorem rdef_iInter {ι : Type} [Finite ι] {f : ι → Set (α → ℂ)} (h : ∀ i, RDef (f i)) :
    RDef (⋂ i, f i) := Set.definable_iInter_of_finite h

theorem rdef_iUnion {ι : Type} [Finite ι] {f : ι → Set (α → ℂ)} (h : ∀ i, RDef (f i)) :
    RDef (⋃ i, f i) := Set.definable_iUnion_of_finite h

/-- The preimage of a constructible set under a polynomial map is constructible. -/
theorem rdef_preimage_poly [Finite α] {k : ℕ} (G : Fin k → MvPolynomial α ℂ) (D : Set (Fin k → ℂ))
    (hD : RDef D) : RDef {c : α → ℂ | (fun j => MvPolynomial.eval c (G j)) ∈ D} := by
  let H : Fin k → MvPolynomial (α ⊕ Fin k) ℂ := fun j =>
    MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (G j)
  let Z : Set (α ⊕ Fin k → ℂ) :=
    ((fun g : α ⊕ Fin k → ℂ => g ∘ Sum.inr) ⁻¹' D) ∩ ⋂ j, {z | MvPolynomial.eval z (H j) = 0}
  have hZ : RDef Z := (hD.preimage_comp Sum.inr).inter (rdef_iInter fun j => rdef_zero (H j))
  have hH : ∀ (z : α ⊕ Fin k → ℂ) (j : Fin k),
      MvPolynomial.eval z (H j) = z (Sum.inr j) - MvPolynomial.eval (z ∘ Sum.inl) (G j) := by
    intro z j
    simp only [H, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename]
  have himg := hZ.image_comp (Sum.inl : α → α ⊕ Fin k)
  convert himg using 1
  ext c
  constructor
  · intro hc
    refine ⟨Sum.elim c (fun j => MvPolynomial.eval c (G j)), ⟨hc, ?_⟩, rfl⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro j
    rw [hH]
    simp
  · rintro ⟨z, ⟨hzD, hz⟩, rfl⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hz
    have he : (fun j => MvPolynomial.eval (z ∘ Sum.inl) (G j)) = z ∘ Sum.inr := by
      funext j
      have := hz j
      rw [hH] at this
      exact (sub_eq_zero.mp this).symm
    change (fun j => MvPolynomial.eval (z ∘ Sum.inl) (G j)) ∈ D
    rw [he]
    exact hzD

end DiamondIntegral.Section8.RingDefinable
