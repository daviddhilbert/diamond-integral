import «section 4».FieldGrowthFiltration

/-! Arbitrarily large finite-field characters separate the next affine
power from each growth piece, even after multiplying by any affine power. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldGrowthSeparation
open FieldDefinableRing FieldGrowthFiltration
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K]

theorem affine_power_separated {n : ℕ} {x : FieldDefinableRing.Ring K}
    (hx : x ∈ piece n) (m : ℕ) : affineClass K ^ m * (x - affineClass K ^ (n + 1)) ≠ 0 := by
  obtain ⟨c, hc⟩ := AddSubgroup.exists_finsupp_of_mem_closure_range
    (fun a : {a : Chart K // Good n a} => objectClass K a.val) x hx
  let I := c.support
  let A (i : I) : Chart K := i.val.val
  have hg (i : I) : Good n (A i) := i.val.property
  choose d hd select C hC using hg
  let p : FreeCommRing (Chart K) := ∑ i : I, c i.val • FreeCommRing.of (A i)
  have hp : Ideal.Quotient.mk (relationIdeal K) p = x := by
    rw [hc]
    simp only [p, map_sum, map_zsmul, objectClass, Finsupp.sum, I, A]
    exact Finset.sum_coe_sort c.support (fun a => c a •
      Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of a.val))
  let L : FreeCommRing (Chart K) := FreeCommRing.of (affine K)
  let r : FreeCommRing (Chart K) := L ^ m * (p - L ^ (n + 1))
  intro hzero
  have hr : r ∈ relationIdeal K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (relationIdeal K) r = 0
    simpa only [r, map_mul, map_sub, map_pow, hp, L, affineClass, objectClass] using hzero
  obtain ⟨s, hs, hmem⟩ := Submodule.mem_span_finite_of_mem_span hr
  let B : ℕ := ∑ i : I, (c i.val).natAbs * C i
  obtain ⟨q, hBq, hq, f, hL, hkill, hbound⟩ :=
    FieldBoundedCharacters.exists_large K A d C select hC s hs B
  have hle : Ideal.span (s : Set (FreeCommRing (Chart K))) ≤ RingHom.ker f :=
    Ideal.span_le.mpr (fun a ha => hkill a ha)
  have hfr : f r = 0 := hle hmem
  have hqpos : (0 : ℤ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hqone : (1 : ℤ) ≤ q := by exact_mod_cast hq.le
  have hpower : (q : ℤ) ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt hqpos)
  have hfp : f p = (q : ℤ) ^ (n + 1) := by
    have he : (q : ℤ) ^ m * (f p - (q : ℤ) ^ (n + 1)) = 0 := by
      simpa only [r, map_mul, map_sub, map_pow, L, hL] using hfr
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hpower)
  have hterm (i : I) : (c i.val) • f (FreeCommRing.of (A i)) ≤
      ((c i.val).natAbs : ℤ) * C i * (q : ℤ) ^ n := by
    have hpow : (q : ℤ) ^ d i ≤ (q : ℤ) ^ n := pow_le_pow_right₀ hqone (hd i)
    calc
      _ = c i.val * f (FreeCommRing.of (A i)) := by simp only [zsmul_eq_mul, Int.cast_id]
      _ ≤ ((c i.val).natAbs : ℤ) * f (FreeCommRing.of (A i)) :=
        mul_le_mul_of_nonneg_right Int.le_natAbs (hbound i).1
      _ ≤ ((c i.val).natAbs : ℤ) * ((C i : ℤ) * (q : ℤ) ^ d i) :=
        mul_le_mul_of_nonneg_left (hbound i).2 (Nat.cast_nonneg _)
      _ ≤ ((c i.val).natAbs : ℤ) * ((C i : ℤ) * (q : ℤ) ^ n) := by
        gcongr
      _ = _ := by ring
  have hfple : f p ≤ (B : ℤ) * (q : ℤ) ^ n := by
    calc
      f p = ∑ i : I, c i.val • f (FreeCommRing.of (A i)) := by simp only [p, map_sum, map_zsmul]
      _ ≤ ∑ i : I, ((c i.val).natAbs : ℤ) * C i * (q : ℤ) ^ n := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (B : ℤ) * (q : ℤ) ^ n := by simp only [B, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  have hBq' : (B : ℤ) < q := by exact_mod_cast hBq
  have hlt : (B : ℤ) * (q : ℤ) ^ n < (q : ℤ) ^ (n + 1) := by
    rw [pow_succ, mul_comm ((q : ℤ) ^ n)]
    exact mul_lt_mul_of_pos_right hBq' (pow_pos hqpos _)
  exact (not_lt_of_ge (hfp ▸ hfple)) hlt

end DiamondIntegral.Section4.FieldGrowthSeparation
