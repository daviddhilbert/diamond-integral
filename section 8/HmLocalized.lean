import «section 8».HmRing
import Mathlib.RingTheory.Localization.Away.Basic
import FubiniTheorems.Fubini.InflatedFamilyFubiniVol

/-! The target `K^μ̂ Var_ℂ[[𝔸]⁻¹]` and `η ∘ h_m`.

The comparison `Θ` of the library lands in `EquivariantVariety.ModifiedRing` (the modified
Grothendieck ring `K^μ̂ Var_ℂ`, with `𝕃 = modifiedAffineLineClass` not inverted). The paper's
`η : T ↦ [𝔸]` needs `𝕃` invertible, so `η ∘ h_m` takes values in the localization
`Rloc = ModifiedRing[𝕃⁻¹]`:

* `hmLoc P m`: `h_m` followed by the coefficient map to `Rloc`;
* `etaHm P m`: `η ∘ h_m` on the natural subring `K^♮_m μRV^db[*] = h_m⁻¹(Rloc[T, T⁻¹])`. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues

/-- `K^μ̂ Var_ℂ[[𝔸]⁻¹]`. -/
abbrev Rloc := Localization.Away modifiedAffineLineClass

/-- `𝕃` as a unit of `Rloc`. -/
def Lunit : Rlocˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Rloc) modifiedAffineLineClass).unit

theorem Lunit_val : (Lunit : Rloc) = algebraMap EquivariantVariety.ModifiedRing Rloc modifiedAffineLineClass :=
  rfl

/-- The coefficient map `R[T^ℚ] → R[𝕃⁻¹][T^ℚ]`. -/
def toLoc : PuiseuxPolynomial EquivariantVariety.ModifiedRing →+* PuiseuxPolynomial Rloc :=
  AddMonoidAlgebra.mapRingHom ℚ (algebraMap EquivariantVariety.ModifiedRing Rloc)

theorem toLoc_single (q : ℚ) (r : EquivariantVariety.ModifiedRing) :
    toLoc (AddMonoidAlgebra.single q r) = AddMonoidAlgebra.single q (algebraMap _ Rloc r) := by
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

variable (P : PuiseuxAmbient)

/-- `h_m` with coefficients in `Rloc`. -/
def hmLoc (m : ℕ+) : RVBoundedRing.Ring (base P) →+* PuiseuxPolynomial Rloc :=
  toLoc.comp (hm P m)

/-- The natural subring `K^♮_m μRV^db[*]`. -/
abbrev naturalRing (m : ℕ+) : Subring (RVBoundedRing.Ring (base P)) :=
  PuiseuxPolynomial.natural (hmLoc P m)

/-- `η ∘ h_m : K^♮_m μRV^db[*] → K^μ̂ Var_ℂ[[𝔸]⁻¹]`. -/
def etaHm (m : ℕ+) : naturalRing P m →+* Rloc :=
  PuiseuxPolynomial.etaNatural (hmLoc P m) Lunit

end DiamondIntegral.Section8.Hm
