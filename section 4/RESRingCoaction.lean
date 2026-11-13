import «section 4».RESChartRing

/-! The actual degree labels give a polynomial coaction on the concrete
measured RES chart ring. Evaluation at one recovers the original element,
so the coaction is injective. Homogeneous pieces and their product rule
are constructed; full coefficient decomposition is a separate step. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESRingCoaction
open RVMeasuredCharts RVMeasuredProductProperties RESChartRing

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : RESChartRing.Ring B →+* R) (h : ∀ k (a : RESChart B k), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

def gradingInvariant (B : Base (M := M)) : Invariant B (Polynomial (RESChartRing.Ring B)) where
  value k a := Polynomial.monomial k (objectClass a)
  unit := by simp [objectClass_unit]
  product k l a b := by
    rw [objectClass_product, Polynomial.monomial_mul_monomial, Nat.add_comm k l]
  iso k a b F := congrArg (Polynomial.monomial k) (objectClass_iso F)
  empty k a ha := by rw [objectClass_empty a ha, map_zero]
  scissor k a b c d h := by
    simpa only [map_add] using congrArg (Polynomial.monomial k) (objectClass_scissor a b c d h)

def coaction (B : Base (M := M)) : RESChartRing.Ring B →+* Polynomial (RESChartRing.Ring B) :=
  lift B (gradingInvariant B)

theorem coaction_class (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    coaction B (objectClass a) = Polynomial.monomial k (objectClass a) := lift_objectClass B (gradingInvariant B) a

theorem coaction_counit (B : Base (M := M)) :
    (Polynomial.evalRingHom 1).comp (coaction B) = RingHom.id (RESChartRing.Ring B) := by
  apply hom_ext B
  intro k a
  change Polynomial.eval 1 (coaction B (objectClass a)) = objectClass a
  rw [coaction_class, Polynomial.eval_monomial, one_pow, mul_one]

theorem coaction_injective (B : Base (M := M)) : Function.Injective (coaction B) := by
  intro x y h
  have he := congrArg (Polynomial.eval 1) h
  exact (RingHom.congr_fun (coaction_counit B) x).symm.trans
    (he.trans (RingHom.congr_fun (coaction_counit B) y))

def gradedPiece (B : Base (M := M)) (n : ℕ) : AddSubgroup (RESChartRing.Ring B) where
  carrier := {x | coaction B x = Polynomial.monomial n x}
  zero_mem' := by change coaction B 0 = Polynomial.monomial n 0; rw [map_zero, map_zero]
  add_mem' := by
    intro x y hx hy
    change coaction B (x + y) = Polynomial.monomial n (x + y)
    calc
      _ = coaction B x + coaction B y := map_add _ _ _
      _ = Polynomial.monomial n x + Polynomial.monomial n y := congrArg₂ (· + ·) hx hy
      _ = _ := (map_add (Polynomial.monomial n) x y).symm
  neg_mem' := by
    intro x hx
    change coaction B (-x) = Polynomial.monomial n (-x)
    calc
      _ = -coaction B x := map_neg _ _
      _ = -Polynomial.monomial n x := congrArg Neg.neg hx
      _ = _ := (map_neg (Polynomial.monomial n) x).symm

theorem class_mem_gradedPiece (B : Base (M := M)) {n : ℕ} (a : RESChart B n) : objectClass a ∈ gradedPiece B n :=
  coaction_class B a

theorem one_mem_gradedPiece (B : Base (M := M)) : (1 : RESChartRing.Ring B) ∈ gradedPiece B 0 := by
  change coaction B 1 = Polynomial.monomial 0 1
  simp

theorem mul_mem_gradedPiece (B : Base (M := M)) {m n : ℕ} {x y : RESChartRing.Ring B}
    (hx : x ∈ gradedPiece B m) (hy : y ∈ gradedPiece B n) : x * y ∈ gradedPiece B (m + n) := by
  change coaction B x = Polynomial.monomial m x at hx
  change coaction B y = Polynomial.monomial n y at hy
  change coaction B (x * y) = Polynomial.monomial (m + n) (x * y)
  rw [map_mul, hx, hy, Polynomial.monomial_mul_monomial]

theorem gradedPiece_inter_zero (B : Base (M := M)) {m n : ℕ} (hmn : m ≠ n) {x : RESChartRing.Ring B}
    (hx : x ∈ gradedPiece B m) (hy : x ∈ gradedPiece B n) : x = 0 := by
  have hp : Polynomial.monomial m x = Polynomial.monomial n x := hx.symm.trans hy
  have hc := congrArg (fun p : Polynomial (RESChartRing.Ring B) => p.coeff m) hp
  simpa [Polynomial.coeff_monomial, Ne.symm hmn] using hc

end DiamondIntegral.Section4.RESRingCoaction
