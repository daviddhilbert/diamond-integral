import Mathlib.RingTheory.Localization.Away.Basic

/-! Equality of degree-normalized values in affine localization has a
finite common-degree witness in the original ring. No injectivity or
non-zero-divisor condition on the affine class is used. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
variable {R : Type*} [CommRing R]

def geometricDegreeValue (L a : R) (k : ℕ) : Localization.Away L :=
  IsLocalization.mk' (Localization.Away L) a (⟨L^k,⟨k,rfl⟩⟩ : Submonoid.powers L)

theorem geometricDegreeValue_shift (L a : R) (k N : ℕ) (hk : k ≤ N) :
    geometricDegreeValue L a k = geometricDegreeValue L (L^(N-k)*a) N := by
  apply IsLocalization.mk'_eq_of_eq
  change L^k * (L^(N-k)*a) = L^N*a
  rw [← mul_assoc,← pow_add,Nat.add_sub_of_le hk]

theorem geometricDegreeValue_eq_iff (L a b : R) (k l : ℕ) :
    geometricDegreeValue L a k = geometricDegreeValue L b l ↔
      ∃ N : ℕ, k ≤ N ∧ l ≤ N ∧ L^(N-k)*a = L^(N-l)*b := by
  constructor
  · intro he
    obtain ⟨c,hc⟩ := (IsLocalization.eq (S := Localization.Away L)
      (a₂ := (⟨L^k,⟨k,rfl⟩⟩ : Submonoid.powers L))
      (b₂ := (⟨L^l,⟨l,rfl⟩⟩ : Submonoid.powers L))).mp he
    obtain ⟨m,hm⟩ := c.property
    have hm' : (c : R) = L^m := hm.symm
    change (c : R)*(L^l*a) = (c : R)*(L^k*b) at hc
    rw [hm',← mul_assoc,← mul_assoc,← pow_add,← pow_add] at hc
    refine ⟨m+k+l,by omega,by omega,?_⟩
    have h1 : m+k+l-k = m+l := by omega
    have h2 : m+k+l-l = m+k := by omega
    simpa only [h1,h2] using hc
  · rintro ⟨N,hk,hl,he⟩
    rw [geometricDegreeValue_shift L a k N hk,geometricDegreeValue_shift L b l N hl,he]

theorem geometricDegreeValue_affine_padding (L a : R) (k r : ℕ) :
    geometricDegreeValue L (L^r*a) (k+r) = geometricDegreeValue L a k := by
  have he := geometricDegreeValue_shift L a k (k+r) (by omega)
  simpa only [Nat.add_sub_cancel_left] using he.symm

end DiamondIntegral.Section5
