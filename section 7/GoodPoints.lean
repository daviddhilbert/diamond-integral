import «section 6».CarriedExceptionalSets
import Section4.PolynomialCover
import Mathlib.Combinatorics.Nullstellensatz

/-! Good points for Corollary 7.15 (`contraction:same:perm:isp`, R126).

* A definable set of VF dimension less than `n` lies in the zero locus of one
  nonzero polynomial over the VF parameter field of its base
  (`exists_polynomial_vanishing_of_dim_lt`): its points are algebraically
  dependent (`not_mem_small_set_of_independent`), and saturation gives a
  finite cover by zero loci (Section 4 `exists_polynomial_vanishing_on_selection`).
* A nonzero polynomial does not vanish on a translated finite grid whose side
  exceeds its total degree (`exists_grid_nonzero`, by Mathlib's Combinatorial
  Nullstellensatz). In 7.15 the grid has small entries from the base field,
  so the grid point is close to the given point and definable from it. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.GoodPoints
open DiamondIntegral.Section6 DiamondIntegral.Section2

/-! ### A grid point off the zero locus -/

section Grid
variable {σ F : Type*} [Finite σ] [Field F]

/-- A nonzero polynomial is nonzero at some point `a + y` with every `y i` in
a finite set larger than its total degree. -/
theorem exists_grid_nonzero (P : MvPolynomial σ F) (hP : P ≠ 0) (a : σ → F) (C : Finset F)
    (hC : P.totalDegree < C.card) : ∃ y : σ → F, (∀ i, y i ∈ C) ∧ MvPolynomial.eval (a + y) P ≠ 0 := by
  by_contra! h
  apply hP
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun i => C.image (fun c => a i + c)) ?_ ?_
  · intro i
    rw [Finset.card_image_of_injective _ (add_right_injective (a i))]
    exact lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree P i) hC
  · intro x hx
    have hy : ∀ i, x i - a i ∈ C := by
      intro i
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp (hx i)
      rw [← hce, add_sub_cancel_left]
      exact hc
    have h' := h (fun i => x i - a i) hy
    have hxa : a + (fun i => x i - a i) = x := by
      funext i
      simp
    rwa [hxa] at h'

/-- The same for a polynomial with coefficients in a subfield, evaluated in
the ambient field. -/
theorem exists_grid_nonzero_subfield (K : Subfield F) (P : MvPolynomial σ K) (hP : P ≠ 0) (a : σ → F)
    (C : Finset F) (hC : P.totalDegree < C.card) :
    ∃ y : σ → F, (∀ i, y i ∈ C) ∧ P.eval₂ K.subtype (a + y) ≠ 0 := by
  have hinj : Function.Injective (MvPolynomial.map (σ := σ) K.subtype) :=
    MvPolynomial.map_injective _ K.subtype_injective
  have hP' : MvPolynomial.map K.subtype P ≠ 0 := by
    intro h0
    apply hP
    apply hinj
    rw [h0, map_zero]
  have hdeg : (MvPolynomial.map K.subtype P).totalDegree < C.card := by
    have he : (MvPolynomial.map K.subtype P).totalDegree = P.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [MvPolynomial.support_map_of_injective P K.subtype_injective]
    rw [he]
    exact hC
  obtain ⟨y, hy, hne⟩ := exists_grid_nonzero _ hP' a C hdeg
  refine ⟨y, hy, ?_⟩
  rwa [MvPolynomial.eval₂_eq_eval_map]

end Grid

/-! ### Sets of small VF dimension lie in a zero locus -/

section Dimension
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

/-- A definable set of VF dimension less than `n` lies in the zero locus of a
nonzero polynomial over the VF parameter field of its base. -/
theorem exists_polynomial_vanishing_of_dim_lt (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (E : DefSet (rawMixedSpace (M := M) n r) S) (hDim : vfDim (rawRVSpace (M := M) 1) E < n) :
    ∃ p : MvPolynomial (Fin n) (vfParameterField S), p ≠ 0 ∧
      ∀ a : E, p.eval₂ (vfParameterField S).subtype a.val.1 = 0 :=
  exists_polynomial_vanishing_on_selection hs hsmall E id
    (fun a hind => not_mem_small_set_of_independent hc E hDim a.val hind a.property)

end Dimension

end DiamondIntegral.Section7.GoodPoints
