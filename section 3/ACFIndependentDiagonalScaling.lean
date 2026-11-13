import «section 3».ACFIndependentFormulaTransport
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [CompatibleRing K] {n : ℕ}

/-- Scaling coordinates by coefficient-field units preserves actual
algebraic independence. -/
theorem acf_independent_diagonal_scale (E : Subfield K) (x : Fin n → K)
    (hx : AlgebraicIndependent E x) (a : Fin n → Eˣ) :
    AlgebraicIndependent E (fun i => (a i : K) * x i) := by
  have he : MvPolynomial.aeval (fun i => (a i : K) * x i) =
      (MvPolynomial.aeval x).comp (diagonalPolynomialEquiv a).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [diagonalPolynomialEquiv,Subfield.algebraMap_ofSubfield]
  rw [algebraicIndependent_iff_injective_aeval,he]
  exact (algebraicIndependent_iff_injective_aeval.mp hx).comp (diagonalPolynomialEquiv a).injective

/-- Infinitely many values of a single coordinate preserve genericity
while every other coordinate is kept literally fixed. -/
theorem acf_independent_coordinate_replacements_infinite (E : Subfield K)
    (x : Fin n → K) (hx : AlgebraicIndependent E x) (i : Fin n) :
    {z : K | AlgebraicIndependent E (Function.update x i z)}.Infinite := by
  let j : ℕ → Eˣ := fun m => Units.mk0 ((m : E)+1) (by exact_mod_cast Nat.succ_ne_zero m)
  have hj : Function.Injective j := by
    intro a b hab
    exact Nat.cast_injective (R := E) (add_right_cancel (congrArg Units.val hab))
  letI : Infinite Eˣ := Infinite.of_injective j hj
  let f : Eˣ → K := fun c => (c : K) * x i
  have hf : Function.Injective f := by
    intro a b hab
    apply Units.ext
    apply Subtype.val_injective
    exact mul_right_cancel₀ (algebraicallyIndependent_coordinate_ne_zero E x hx i) hab
  have hsub : Set.range f ⊆ {z : K | AlgebraicIndependent E (Function.update x i z)} := by
    rintro _ ⟨c,rfl⟩
    have h := acf_independent_diagonal_scale E x hx (Function.update (fun _ => 1) i c)
    have he : (fun j => ((Function.update (fun _ : Fin n => (1 : Eˣ)) i c) j : K) * x j) =
        Function.update x i (f c) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [f]
      · simp [hj]
    exact Eq.mp (congrArg (fun z => AlgebraicIndependent E z) he) h
  exact (Set.infinite_range_of_injective hf).mono hsub

/-- A definable relation has infinitely many generic replacements in
one coordinate on whichever side contains its generic tuple. -/
theorem acf_generic_coordinate_side_infinite (E : Subfield K)
    (R : Set (Fin n → K)) (hR : (E : Set K).Definable Language.ring R)
    (x : Fin n → K) (hx : AlgebraicIndependent E x) (i : Fin n) :
    (x ∈ R → {z : K | Function.update x i z ∈ R}.Infinite) ∧
      (x ∉ R → {z : K | Function.update x i z ∉ R}.Infinite) := by
  have hi := acf_independent_coordinate_replacements_infinite E x hx i
  constructor
  · intro h
    apply hi.mono
    intro z hz
    exact (acf_independent_definable_iff E R hR x _ hx hz).mp h
  · intro h
    apply hi.mono
    intro z hz hh
    exact h ((acf_independent_definable_iff E R hR x _ hx hz).mpr hh)

end DiamondIntegral.Section3
