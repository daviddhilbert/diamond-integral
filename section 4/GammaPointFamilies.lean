import «section 4».GammaGraphIntegration

/-! Actual finite-dimensional point masses have Euler integral equal to
their integer weight, whether or not the point is named in the base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPointFamilies
open GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaIteratedIntegral GammaGraphIntegration

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integrateAll_singleton (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (f : familySubgroup B n) (x : Fin n → Values.Gamma (M := M)) (w : ℤ)
    (he : ∀ z, f.val z = if z = x then w else 0) :
    integrateAll h00 hκ hs B hr hγ k n f = w := by
  induction n with
  | zero =>
    change f.val emptyTuple = w
    rw [he]
    simp only [Subsingleton.elim emptyTuple x, ite_true]
  | succ n ih =>
    apply ih (integrateFirst h00 hκ hs B hr hγ k n f) (Fin.tail x)
    intro y
    apply integralFirst_singleton h00 B k f.val f.property y (x 0)
      (if y = Fin.tail x then w else 0)
    intro a
    rw [he]
    have hcons : Fin.cons a y = x ↔ a = x 0 ∧ y = Fin.tail x := by
      calc
        Fin.cons a y = x ↔ Fin.cons a y = Fin.cons (x 0) (Fin.tail x) := by rw [Fin.cons_self_tail]
        _ ↔ a = x 0 ∧ y = Fin.tail x := Fin.cons_inj
    simp only [hcons]
    by_cases ha : a = x 0 <;> by_cases hy : y = Fin.tail x <;> simp [ha, hy]

end DiamondIntegral.Section4.GammaPointFamilies
