import ProvedACFExtension
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Perfect
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CompatibleRing K]

/-- Ring-language quantifier-free formulas cannot distinguish two
elements with the same minimal polynomial over the parameter field. -/
theorem acf_qf_conjugate_invariant (E : Subfield K)
    (φ : Language.ring.BoundedFormula E 1) (hφ : φ.IsQF)
    {x y : K} (hxy : IsConjRoot E x y) :
    φ.Realize E.subtype (fun _ => x) ↔ φ.Realize E.subtype (fun _ => y) := by
  refine BoundedFormula.IsQF.recOn
    (motive := fun ψ _ => ψ.Realize E.subtype (fun _ => x) ↔
      ψ.Realize E.subtype (fun _ => y)) hφ ?_ ?_ ?_
  · rfl
  · intro ψ ha
    cases ha with
    | equal t₁ t₂ =>
      let p : Polynomial E := ACFValidation.termToPoly t₁ - ACFValidation.termToPoly t₂
      have hp : p.eval₂ E.subtype x = 0 ↔ p.eval₂ E.subtype y = 0 := by
        change Polynomial.aeval x p = 0 ↔ Polynomial.aeval y p = 0
        rw [← minpoly.dvd_iff,← minpoly.dvd_iff]
        rw [hxy]
      simp only [BoundedFormula.realize_bdEqual]
      rw [ACFValidation.eval₂_termToPoly,ACFValidation.eval₂_termToPoly,
        ACFValidation.eval₂_termToPoly,ACFValidation.eval₂_termToPoly]
      simpa only [p,Polynomial.eval₂_sub,sub_eq_zero] using hp
    | rel R _ => exact isEmptyElim R
  · intro φ ψ _ _ hφ hψ
    simp only [BoundedFormula.realize_imp]
    exact imp_congr hφ hψ

theorem acf_formula_conjugate_invariant (E : Subfield K)
    (φ : Language.ring.BoundedFormula E 1) {x y : K} (hxy : IsConjRoot E x y) :
    φ.Realize E.subtype (fun _ => x) ↔ φ.Realize E.subtype (fun _ => y) := by
  obtain ⟨ψ,hψ,he⟩ := ProvedACFExtension.fullQE E 1 φ
  exact (he K inferInstance E.subtype (fun _ => x)).trans
    ((acf_qf_conjugate_invariant E ψ hψ hxy).trans
      (he K inferInstance E.subtype (fun _ => y)).symm)

/-- In characteristic zero an original-field definable singleton lies
in that field. This proves the rational, rather than merely algebraic,
definable-closure step needed for generic residue maps. -/
theorem acf_singleton_formula_mem_subfield [CharZero K] (E : Subfield K)
    (φ : Language.ring.BoundedFormula E 1) (x : K)
    (hφ : ∀ y : K, φ.Realize E.subtype (fun _ => y) ↔ y = x) : x ∈ E := by
  have hconj : ∀ y : K, IsConjRoot E x y → y = x := by
    intro y hy
    apply (hφ y).mp
    exact (acf_formula_conjugate_invariant E φ hy).mp ((hφ x).mpr rfl)
  by_contra hx
  by_cases hi : IsIntegral E x
  · have hs : IsSeparable E x := (minpoly.irreducible hi).separable
    have hn : x ∉ (⊥ : Subalgebra E K) := by
      intro hm
      obtain ⟨a,ha⟩ := Algebra.mem_bot.mp hm
      apply hx
      change (a : K) = x at ha
      exact ha ▸ a.property
    obtain ⟨y,hne,hy⟩ := (notMem_iff_exists_ne_and_isConjRoot hs
      (IsAlgClosed.splits _)).mp hn
    exact hne (hconj y hy).symm
  · have hi' : ¬ IsIntegral E (x+1) := by
      intro h
      apply hi
      have hh := h.sub (isIntegral_one : IsIntegral E (1 : K))
      simpa using hh
    have hc : IsConjRoot E x (x+1) := by
      change minpoly E x = minpoly E (x+1)
      rw [minpoly.eq_zero hi,minpoly.eq_zero hi']
    have he := hconj (x+1) hc
    exact one_ne_zero (add_left_cancel (he.trans (add_zero x).symm))

theorem acf_definable_singleton_mem_subfield [CharZero K] (E : Subfield K) (x : K)
    (hx : (E : Set K).Definable Language.ring {z : Fin 1 → K | z 0 = x}) : x ∈ E := by
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hx
  let ψ : Language.ring.BoundedFormula E 1 :=
    BoundedFormula.relabel (id : E ⊕ Fin 1 → E ⊕ Fin 1) φ
  apply acf_singleton_formula_mem_subfield E ψ x
  intro y
  have he : φ.Realize (Sum.elim E.subtype (fun _ : Fin 1 => y)) ↔ y = x :=
    (Set.ext_iff.mp hφ (fun _ : Fin 1 => y)).symm
  have hz : (fun _ : Fin 0 => y) = (default : Fin 0 → K) := Subsingleton.elim _ _
  simp only [ψ,BoundedFormula.realize_relabel,Function.comp_def,Fin.castAdd_zero,
    id_eq,hz]
  convert he using 1
  rfl

end DiamondIntegral.Section3
