import «section 4».GammaFamilyCutLogic

/-! Uniform original-base definability of unary-fibre Euler integration,
with any finite number of Gamma parameters. Endpoints are quantified, not
added to the conclusion's base. Saturation and smallness are explicit. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFamilyIntegration
open GammaOrderLogic GammaUniformCuts GammaFamilyEuler GammaFamilyCutLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem fibreEuler_level_definable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) (m : ℤ) :
    GammaDefinable B {y : Fin n → Values.Gamma (M := M) | fibreEuler h00 B k R hR y = m} := by
  obtain ⟨N, hN⟩ := uniform_cutBound h00 hκ hs B hr hγ R hR
  have hC := GammaFormulaLogic.formula_definable_base B (fun _ : Unit => R) (fun _ => hR)
    (controlsFormula N n)
  have hL := GammaRelationLogic.inter_definable_base B _ _ hC
    (cutSum_level_definable_base (N := N) B k R hR m)
  have h := GammaQuantifierLogic.image_definable_base B _ hL (Fin.natAdd N)
    (Fin.natAdd_injective n N)
  convert h using 1
  ext y
  change fibreEuler h00 B k R hR y = m ↔
    ∃ z : Fin (N + n) → Values.Gamma (M := M),
      ((controlsFormula N n).Realize (fun _ => R) z ∧ cutSum k R z = m) ∧ z ∘ Fin.natAdd N = y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := hN y
    have hC : (controlsFormula N n).Realize (fun _ => R) (Fin.append a y) := by
      apply (controlsFormula_realize N n R _).mpr
      simpa only [Fin.append_left, Fin.append_right] using ha
    have hsum : cutSum k R (Fin.append a y) = fibreEuler h00 B k R hR y := by
      rw [fibreEuler_cutSum h00 B k R hR y a ha]
      simp only [cutSum, Occupied, Fin.append_left, Fin.append_right]
    exact ⟨Fin.append a y, ⟨hC, hsum.trans hy⟩, funext (Fin.append_right a y)⟩
  · rintro ⟨z, ⟨hC, hsum⟩, he⟩
    have ha := (controlsFormula_realize N n R z).mp hC
    change (fun j => z (Fin.natAdd N j)) = y at he
    have ha' : Controls (fun i => z (Fin.castAdd n i)) {x | Fin.cons x y ∈ R} := by
      simpa only [he] using ha
    rw [fibreEuler_cutSum h00 B k R hR y (fun i => z (Fin.castAdd n i)) ha']
    convert hsum using 1
    simp only [cutSum, Occupied, he]

def IntegerFamilyDefinable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → ℤ) : Prop :=
  (Set.range f).Finite ∧ ∀ m : ℤ, GammaDefinable B {y | f y = m}

theorem fibreEuler_integerFamilyDefinable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    IntegerFamilyDefinable B (fibreEuler h00 B k R hR) :=
  ⟨fibreEuler_finite_range h00 hκ hs B hr hγ k R hR,
    fibreEuler_level_definable h00 hκ hs B hr hγ k R hR⟩

end DiamondIntegral.Section4.GammaFamilyIntegration
