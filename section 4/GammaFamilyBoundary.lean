import «section 4».GammaUniformCuts
import «section 4».EulerControlledBreakpoints

/-! The intrinsic boundary of a unary Gamma fibre is an original-base
definable relation. Its finite size is uniformly bounded by the family's
cut bound. No choices of endpoint functions or RV sections are made. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFamilyBoundary
open GammaFormulaLogic GammaOrderLogic GammaUniformCuts EulerFunction

def interiorFormula (n : ℕ) : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 1) :=
  let π : Fin (n + 1) → Fin (n + 4) := Fin.cases 0 (fun j => j.succ.succ.succ.succ)
  let lt (i j : Fin (n + 4)) : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 4) := .lt i j
  let atom : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 4) := .pred () π
  let inside := ((lt (0 : Fin (n + 2)).succ.succ 0).and (lt 0 (0 : Fin (n + 3)).succ)).imp atom
  let bounded : GammaFormulaLogic.Formula (fun _ : Unit => n + 1) (n + 3) :=
    .and (.lt (0 : Fin (n + 2)).succ (0 : Fin (n + 1)).succ.succ)
      (.and (.lt (0 : Fin (n + 1)).succ.succ 0) inside.all)
  bounded.ex.ex

def Interior {α : Type} [LT α] {n : ℕ} (R : Set (Fin (n + 1) → α)) :
    Set (Fin (n + 1) → α) :=
  {z | ∃ l u, l < z 0 ∧ z 0 < u ∧ ∀ x, l < x → x < u → Fin.cons x (fun j => z j.succ) ∈ R}

theorem interiorFormula_realize {α : Type} [LT α] (n : ℕ)
    (R : Set (Fin (n + 1) → α)) (z : Fin (n + 1) → α) :
    (interiorFormula n).Realize (fun _ => R) z ↔ z ∈ Interior R := by
  simp only [interiorFormula, GammaFormulaLogic.Formula.Realize,
    GammaFormulaLogic.Formula.all_realize, GammaFormulaLogic.Formula.imp_realize,
    Fin.cons_zero, Fin.cons_succ]
  have he (l u x : α) :
      (Fin.cons x (Fin.cons u (Fin.cons l z)) ∘ Fin.cases 0 (fun j => j.succ.succ.succ.succ)) =
        (Fin.cons x (fun j => z j.succ) : Fin (n + 1) → α) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp_rw [he]
  simp only [Interior, Set.mem_ofPred_eq, and_imp]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem interior_definable_base (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    GammaDefinable B (Interior R) := by
  have h := GammaFormulaLogic.formula_definable_base B (fun _ : Unit => R) (fun _ => hR)
    (interiorFormula n)
  convert h using 1
  ext z
  exact (interiorFormula_realize n R z).symm

def Boundary {α : Type} [LT α] {n : ℕ} (R : Set (Fin (n + 1) → α)) :
    Set (Fin (n + 1) → α) := (Interior R ∪ Interior Rᶜ)ᶜ

theorem boundary_definable_base (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    GammaDefinable B (Boundary R) :=
  GammaRelationLogic.complement_definable_base B _
    (GammaQuantifierLogic.union_definable_base B _ _ (interior_definable_base B R hR)
      (interior_definable_base B Rᶜ (GammaRelationLogic.complement_definable_base B R hR)))

theorem boundary_iff_nonConstantNear {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (y : Fin n → Values.Gamma (M := M)) (x : Values.Gamma (M := M)) :
    Fin.cons x y ∈ Boundary R ↔
      ¬ ConstantNear (fun t => if Fin.cons t y ∈ R then (1 : ℤ) else 0) x := by
  have he : (Fin.cons x y ∈ Interior R ∪ Interior Rᶜ) ↔
      ConstantNear (fun t => if Fin.cons t y ∈ R then (1 : ℤ) else 0) x := by
    constructor
    · intro h
      rcases h with h | h
      · obtain ⟨l, u, hl, hu, hR⟩ := h
        have hx : Fin.cons x y ∈ R := hR x hl hu
        refine ⟨l, u, hl, hu, ?_⟩
        intro t hlt htu
        have ht : Fin.cons t y ∈ R := hR t hlt htu
        simp only [ht, hx, ite_true]
      · obtain ⟨l, u, hl, hu, hR⟩ := h
        have hx : Fin.cons x y ∉ R := hR x hl hu
        refine ⟨l, u, hl, hu, ?_⟩
        intro t hlt htu
        have ht : Fin.cons t y ∉ R := hR t hlt htu
        simp only [ht, hx, ite_false]
    · rintro ⟨l, u, hl, hu, hconst⟩
      by_cases hx : Fin.cons x y ∈ R
      · refine Or.inl ⟨l, u, hl, hu, ?_⟩
        intro t hlt htu
        have he := hconst t hlt htu
        change (if Fin.cons t y ∈ R then (1 : ℤ) else 0) =
          (if Fin.cons x y ∈ R then 1 else 0) at he
        change Fin.cons t y ∈ R
        by_contra ht
        simp only [hx, ht, ite_true, ite_false] at he
        omega
      · refine Or.inr ⟨l, u, hl, hu, ?_⟩
        intro t hlt htu
        have he := hconst t hlt htu
        change (if Fin.cons t y ∈ R then (1 : ℤ) else 0) =
          (if Fin.cons x y ∈ R then 1 else 0) at he
        change Fin.cons t y ∉ R
        intro ht
        simp only [hx, ht, ite_true, ite_false] at he
        omega
  exact not_congr he

theorem uniform_boundary_bound (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    ∃ N, ∀ y : Fin n → Values.Gamma (M := M),
      {x | Fin.cons x y ∈ Boundary R}.Finite ∧ {x | Fin.cons x y ∈ Boundary R}.ncard ≤ N := by
  obtain ⟨N, hN⟩ := uniform_cutBound h00 hκ hs B hr hγ R hR
  refine ⟨N, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := hN y
  let f : Values.Gamma (M := M) → ℤ := fun x => if Fin.cons x y ∈ R then 1 else 0
  have hc : CutDetermined a f := by
    intro x x' hcut
    have hmem := ha x x' (fun i => (cutCode_eq_iff (a i) x x').mp (hcut i))
    change (Fin.cons x y ∈ R ↔ Fin.cons x' y ∈ R) at hmem
    by_cases hx : Fin.cons x y ∈ R
    · have hx' : Fin.cons x' y ∈ R := hmem.mp hx
      simp only [f, hx, hx', ite_true]
    · have hx' : Fin.cons x' y ∉ R := fun h => hx (hmem.mpr h)
      simp only [f, hx, hx', ite_false]
  have he : {x | Fin.cons x y ∈ Boundary R} = {x | ¬ ConstantNear f x} := by
    ext x
    exact boundary_iff_nonConstantNear R y x
  rw [he]
  exact ⟨finite_nonConstantNear_of_cuts a f hc, ncard_nonConstantNear_le_cuts a f hc⟩

end DiamondIntegral.Section4.GammaFamilyBoundary
