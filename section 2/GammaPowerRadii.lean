import «section 2».UnaryValueGerms
import Mathlib.Algebra.Order.Group.OrderIso

/-! Positive rational-affine radius laws as actual order isomorphisms
of Gamma. The multiplicative presentation represents the additive law
gamma ↦ (p/q) gamma + c from the manuscript. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def gammaPowerOrderIso (p : ℕ) (hp : p ≠ 0) : Gamma M ≃o Gamma M :=
  OrderIso.ofSurjective (OrderEmbedding.ofStrictMono (fun γ : Gamma M => γ^p) (pow_left_strictMono hp))
    (Values.gamma_pow_surjective p hp)

theorem gammaPowerOrderIso_apply (p : ℕ) (hp : p ≠ 0) (γ : Gamma M) :
    gammaPowerOrderIso p hp γ = γ^p := rfl

noncomputable def gammaAffineRadius (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (c : Gamma M) :
    Gamma M ≃o Gamma M :=
  ((gammaPowerOrderIso p hp).trans (OrderIso.mulLeft (c^q))).trans (gammaPowerOrderIso q hq).symm

theorem gammaAffineRadius_pow (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (c γ : Gamma M) :
    gammaAffineRadius p q hp hq c γ ^ q = c^q * γ^p := by
  exact (gammaPowerOrderIso q hq).apply_symm_apply _

theorem gammaPowerGerm_finite_value {f : VF M → VF M} {a : VF M} {p q : ℕ}
    {c r : Gamma M} (hp : p ≠ 0) (hq : q ≠ 0) (h : gammaPowerGerm f a p q c r)
    (x : VF M) (hxa : x ≠ a) (hx : r.val < vfValue (x-a)) :
    ∃ hfx : f x ≠ 0, finiteValue (f x) hfx =
      gammaAffineRadius p q hp hq c (finiteValue (x-a) (sub_ne_zero.mpr hxa)) := by
  obtain ⟨hfx,he⟩ := h x hxa hx
  refine ⟨hfx,?_⟩
  apply (pow_left_strictMono hq).injective
  change finiteValue (f x) hfx ^ q =
    gammaAffineRadius p q hp hq c (finiteValue (x-a) (sub_ne_zero.mpr hxa)) ^ q
  rw [gammaAffineRadius_pow]
  apply Subtype.ext
  change Values.gammaValHom (finiteValue (f x) hfx ^ q) =
    Values.gammaValHom (c^q * finiteValue (x-a) (sub_ne_zero.mpr hxa)^p)
  simp only [map_pow,map_mul]
  change Values.vfValueHom (f x)^q = c.val^q * Values.vfValueHom (x-a)^p
  exact he

def puncturedGammaDisc (a : VF M) (γ : Gamma M) : Set (VF M) :=
  {x | x ≠ a ∧ γ.val < vfValue (x-a)}

theorem puncturedGammaDisc_anti (a : VF M) {r s : Gamma M} (hrs : r ≤ s) :
    puncturedGammaDisc a s ⊆ puncturedGammaDisc a r :=
  fun _ hx => ⟨hx.1,lt_of_le_of_lt hrs hx.2⟩

theorem gammaPowerGerm_disc_iff {f : VF M → VF M} {a : VF M} {p q : ℕ}
    {c r : Gamma M} (hp : p ≠ 0) (hq : q ≠ 0) (h : gammaPowerGerm f a p q c r)
    (x : VF M) (hx : x ∈ puncturedGammaDisc a r) (γ : Gamma M) :
    x ∈ puncturedGammaDisc a γ ↔
      f x ∈ puncturedGammaDisc 0 (gammaAffineRadius p q hp hq c γ) := by
  obtain ⟨hfx,he⟩ := gammaPowerGerm_finite_value hp hq h x hx.1 hx.2
  change (x ≠ a ∧ γ.val < vfValue (x-a)) ↔
    (f x ≠ 0 ∧ (gammaAffineRadius p q hp hq c γ).val < vfValue (f x-0))
  rw [and_iff_right hx.1,and_iff_right hfx,sub_zero]
  change γ < finiteValue (x-a) (sub_ne_zero.mpr hx.1) ↔
    gammaAffineRadius p q hp hq c γ < finiteValue (f x) hfx
  rw [he]
  exact (gammaAffineRadius p q hp hq c).lt_iff_lt.symm

end DiamondIntegral.Section2
