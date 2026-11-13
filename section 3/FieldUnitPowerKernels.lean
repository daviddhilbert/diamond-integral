import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Group.Int.Units
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]

/-- In characteristic zero, the roots of unity of an algebraically
closed field detect every nonunit integral power. -/
theorem fieldUnit_zpow_injective_isUnit (d : ℤ)
    (hinj : Function.Injective (fun u : Kˣ => u ^ d)) : IsUnit d := by
  by_cases hd : d = 0
  · subst d
    let u : Kˣ := Units.mk0 (2 : K) (by norm_num)
    have he : u = 1 := hinj (by simp)
    have hv : (2 : K) = 1 := congrArg Units.val he
    norm_num at hv
  have hn : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  letI : NeZero d.natAbs := ⟨hn⟩
  letI : NeZero (d.natAbs : K) := ⟨by exact_mod_cast hn⟩
  obtain ⟨ζ,hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K d.natAbs
  let u : Kˣ := (hζ.isUnit hn).unit
  have hu : (u : K) = ζ := (hζ.isUnit hn).unit_spec
  have hp : u ^ d.natAbs = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val,Units.val_one,hu] using hζ.pow_eq_one
  have hz : u ^ d = 1 := by
    cases d with
    | ofNat n =>
      change u ^ n = 1 at hp
      simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hp
    | negSucc n =>
      change u ^ (n+1) = 1 at hp
      rw [zpow_negSucc,hp,inv_one]
  have he : u = 1 := hinj (hz.trans (one_zpow d).symm)
  have hζone : ζ = 1 := hu.symm.trans (congrArg Units.val he)
  apply Int.isUnit_iff_natAbs_eq.mpr
  by_contra hnot
  have hgt : 1 < d.natAbs := by omega
  exact hζ.ne_one hgt hζone
end DiamondIntegral.Section3
