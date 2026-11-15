import «section 5».PuiseuxGalois
import Mathlib.RingTheory.HahnSeries.Valuation
import RVClassEquality

/-! The actual principal-unit RV quotient of the concrete Puiseux field.
Its normal form is the rational exponent together with a nonzero leading
coefficient. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {k : Type*} [Field k]

/-- The multiplicative form of the actual rational-exponent valuation. -/
def puiseuxValuation (k : Type*) [Field k] :
    Valuation (PuiseuxSeries k) (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  (HahnSeries.addVal ℚ k).toValuation.comap (puiseuxSubfield k).subtype

theorem puiseuxUnit_coe_ne_zero (u : (PuiseuxSeries k)ˣ) :
    ((u : PuiseuxSeries k) : HahnSeries ℚ k) ≠ 0 :=
  fun h => u.ne_zero (Subtype.ext h)

/-- Record the exponent and coefficient of the actual leading term. -/
def puiseuxUnitLeadingTerm : (PuiseuxSeries k)ˣ →* (Multiplicative ℚ × kˣ) where
  toFun u := (Multiplicative.ofAdd ((u : PuiseuxSeries k) : HahnSeries ℚ k).order,
    Units.mk0 ((u : PuiseuxSeries k) : HahnSeries ℚ k).leadingCoeff
      (leadingCoeff_ne_zero.mpr (puiseuxUnit_coe_ne_zero u)))
  map_one' := by
    apply Prod.ext
    · change Multiplicative.ofAdd (1 : HahnSeries ℚ k).order = 1
      simp
    · apply Units.ext
      exact leadingCoeff_one
  map_mul' u w := by
    apply Prod.ext
    · change Multiplicative.ofAdd
        (((u : PuiseuxSeries k) : HahnSeries ℚ k) * ((w : PuiseuxSeries k) : HahnSeries ℚ k)).order = _
      rw [order_mul (puiseuxUnit_coe_ne_zero u) (puiseuxUnit_coe_ne_zero w)]
      rfl
    · apply Units.ext
      exact leadingCoeff_mul _ _

/-- The normal form loses exactly the principal units, not any extra arithmetic data. -/
theorem puiseuxUnitLeadingTerm_ker :
    (puiseuxUnitLeadingTerm (k := k)).ker = RVCalc.principalUnits (puiseuxValuation k) := by
  ext u
  rw [MonoidHom.mem_ker]
  change (Multiplicative.ofAdd ((u : PuiseuxSeries k) : HahnSeries ℚ k).order,
      Units.mk0 ((u : PuiseuxSeries k) : HahnSeries ℚ k).leadingCoeff (leadingCoeff_ne_zero.mpr (puiseuxUnit_coe_ne_zero u))) = (1, 1) ↔ _
  rw [Prod.ext_iff]
  change (((u : PuiseuxSeries k) : HahnSeries ℚ k).order = 0 ∧
    Units.mk0 ((u : PuiseuxSeries k) : HahnSeries ℚ k).leadingCoeff (leadingCoeff_ne_zero.mpr (puiseuxUnit_coe_ne_zero u)) = 1) ↔
    (0 : WithTop ℚ) < ((((u : PuiseuxSeries k) : HahnSeries ℚ k) - 1).orderTop)
  rw [Units.ext_iff, Units.val_mk0, Units.val_one, orderTop_self_sub_one_pos_iff]
  rw [← order_eq_orderTop_of_ne_zero (puiseuxUnit_coe_ne_zero u)]
  exact and_congr (by exact_mod_cast Iff.rfl) Iff.rfl

/-- Every rational monomial belongs to a finite Laurent level. -/
def puiseuxMonomial (q : ℚ) (c : k) : PuiseuxSeries k :=
  ⟨single q c, q.den, q.den_pos, single q.num c, by
    change embDomain _ (single q.num c : HahnSeries ℤ k) = single q c
    rw [embDomain_single]
    exact congrArg (fun a : ℚ => (single a c : HahnSeries ℚ k)) (Rat.num_div_den q)⟩

theorem puiseuxMonomial_coe (q : ℚ) (c : k) :
    (puiseuxMonomial q c : HahnSeries ℚ k) = single q c := rfl

def puiseuxMonomialUnit (q : ℚ) (c : kˣ) : (PuiseuxSeries k)ˣ :=
  Units.mk0 (puiseuxMonomial q (c : k)) (by
    intro h
    have h := congrArg (fun f : PuiseuxSeries k => (f : HahnSeries ℚ k)) h
    exact single_ne_zero c.ne_zero h)

theorem puiseuxUnitLeadingTerm_monomial (q : ℚ) (c : kˣ) :
    puiseuxUnitLeadingTerm (puiseuxMonomialUnit q c) = (Multiplicative.ofAdd q, c) := by
  apply Prod.ext
  · change Multiplicative.ofAdd (single q (c : k) : HahnSeries ℚ k).order = _
    rw [order_single c.ne_zero]
  · apply Units.ext
    exact leadingCoeff_of_single

theorem puiseuxUnitLeadingTerm_surjective : Function.Surjective (puiseuxUnitLeadingTerm (k := k)) := by
  rintro ⟨q, c⟩
  exact ⟨puiseuxMonomialUnit q.toAdd c, puiseuxUnitLeadingTerm_monomial q.toAdd c⟩

/-- Actual RV units, canonically expressed by exponent and leading coefficient. -/
def puiseuxRVUnitEquiv : RVCalc.RVUnit (puiseuxValuation k) ≃* (Multiplicative ℚ × kˣ) :=
  (QuotientGroup.quotientMulEquivOfEq puiseuxUnitLeadingTerm_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective puiseuxUnitLeadingTerm puiseuxUnitLeadingTerm_surjective)

end DiamondIntegral.Section5
