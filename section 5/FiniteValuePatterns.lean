import «section 5».PuiseuxValuePresentation
import «section 5».FiniteFrameComparison

/-! Native finite value support and finite Kummer weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance finitePatternsStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

theorem native_finite_value_patterns_iff {S : Set Carrier} {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) S) :
    (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite ↔
      (Set.range (fun u : A => fun i => value (taggedRVEquiv (u.val i)))).Finite := by
  constructor
  · intro h
    have hh := h.image (fun p : Fin n → Values.GammaTop (M := Carrier) => gammaNormalEquiv ∘ p)
    apply hh.subset
    rintro p ⟨u, rfl⟩
    exact ⟨_, ⟨u, rfl⟩, funext (fun i => gammaNormalEquiv_vrv (u.val i))⟩
  · intro h
    have hh := h.image (fun p : Fin n → WithTop ℚ => gammaNormalEquiv.symm ∘ p)
    have he (u : A) : (fun i => gammaNormalEquiv.symm (value (taggedRVEquiv (u.val i)))) =
        fun i => Values.vrv (u.val i) := by
      funext i
      rw [← gammaNormalEquiv_vrv, gammaNormalEquiv.symm_apply_apply]
    apply hh.subset
    rintro p ⟨u, rfl⟩
    exact ⟨_, ⟨u, rfl⟩, he u⟩

omit [Carrier ⊨ Axioms.ACVF] in
theorem rational_tuple_common_level (n : ℕ) (q : Fin n → ℚ) :
    ∃ N : ℕ+, ∃ a : Fin n → ℤ, ∀ i, q i = (a i : ℚ) / (N : ℕ) := by
  induction n with
  | zero => exact ⟨1, Fin.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨N, a, ha⟩ := ih (Fin.tail q)
    let d : ℕ+ := ⟨(q 0).den, (q 0).den_pos⟩
    refine ⟨d * N, Fin.cons ((q 0).num * (N : ℤ)) (fun i => (d : ℤ) * a i), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change q 0 = (((q 0).num * (N : ℤ) : ℤ) : ℚ) / ((d * N : ℕ+) : ℕ)
      have hN : (N : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
      calc
        q 0 = (q 0).num / (q 0).den := (Rat.num_div_den (q 0)).symm
        _ = _ := by
          push_cast
          dsimp only [d]
          field_simp
          rfl
    · change Fin.tail q j = (((d : ℤ) * a j : ℤ) : ℚ) / ((d * N : ℕ+) : ℕ)
      rw [ha j]
      have hN : (N : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
      have hd : (d : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
      push_cast
      field_simp

end DiamondIntegral.Section5.PuiseuxOriginal
