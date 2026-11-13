import «section 4».PointLocalizationNormalization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! For a full natural-number grading and any degree-one q, quotienting
by q-1 is the degree-zero localization at q. The inverse maps and their
homogeneous fraction formulas are constructed without regularity of q. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.PointLocalizationEquivalence
open PolynomialCoactionGrading PointLocalizationNormalization
variable {R : Type*} [CommRing R]
variable (c : Coaction R) (q : R)
local instance coactionGradedRing : GradedRing c.piece := c.grading

def pointIdeal : Ideal R := Ideal.span {q - 1}

def Quotient := R ⧸ pointIdeal q
  deriving CommRing

def quotientMap : R →+* Quotient q := Ideal.Quotient.mk (pointIdeal q)

theorem quotient_point : quotientMap q q = 1 := by
  have he : quotientMap q (q - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_sub, map_one] at he
  exact sub_eq_zero.mp he

def fromLocalization : Localization.Away q →+* Quotient q :=
  IsLocalization.Away.lift q (g := quotientMap q) (by rw [quotient_point]; exact isUnit_one)

theorem fromLocalization_algebraMap (x : R) :
    fromLocalization q (algebraMap R (Localization.Away q) x) = quotientMap q x :=
  IsLocalization.Away.lift_eq q _ x

theorem fromLocalization_fraction (n : ℕ) (x : R) :
    fromLocalization q (Localization.mk x (⟨q ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers q)) = quotientMap q x := by
  have he := congrArg (fromLocalization q) (IsLocalization.mk'_spec (Localization.Away q) x
    (⟨q ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers q))
  rw [map_mul, fromLocalization_algebraMap, fromLocalization_algebraMap] at he
  rw [← Localization.mk_eq_mk'_apply] at he
  simpa only [map_pow, quotient_point, one_pow, mul_one] using he

def fromSource : Source c q →+* Quotient q := (fromLocalization q).comp (embedding c q)

theorem fromSource_normalize (hq : q ∈ c.piece 1) (x : R) :
    fromSource c q (normalize c q hq x) = quotientMap q x := by
  rw [← c.sum_coefficients x]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [normalize_homogeneous c q hq (c.coefficient_mem x n)]
  exact fromLocalization_fraction q n ((c.map x).coeff n)

theorem pointIdeal_le_normalize_ker (hq : q ∈ c.piece 1) : pointIdeal q ≤ RingHom.ker (normalize c q hq) := by
  apply Ideal.span_le.mpr
  rintro x (rfl : x = q - 1)
  change normalize c q hq (q - 1) = 0
  rw [map_sub, normalize_point, map_one, sub_self]

def toSource (hq : q ∈ c.piece 1) : Quotient q →+* Source c q :=
  Ideal.Quotient.lift (pointIdeal q) (normalize c q hq) (fun _ hx => pointIdeal_le_normalize_ker c q hq hx)

theorem toSource_mk (hq : q ∈ c.piece 1) (x : R) : toSource c q hq (quotientMap q x) = normalize c q hq x := rfl

theorem fromSource_toSource (hq : q ∈ c.piece 1) (x : Quotient q) :
    fromSource c q (toSource c q hq x) = x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact fromSource_normalize c q hq r

theorem toSource_fromSource (hq : q ∈ c.piece 1) (x : Source c q) :
    toSource c q hq (fromSource c q x) = x := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective c.piece hq x
  change toSource c q hq (fromLocalization q
    (Localization.mk a (⟨q ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers q))) = _
  rw [fromLocalization_fraction, toSource_mk]
  exact normalize_homogeneous c q hq (by simpa only [smul_eq_mul, mul_one] using ha)

def equiv (hq : q ∈ c.piece 1) : Quotient q ≃+* Source c q :=
  RingEquiv.ofBijective (toSource c q hq) ⟨(by
    intro x y h
    exact (fromSource_toSource c q hq x).symm.trans
      ((congrArg (fromSource c q) h).trans (fromSource_toSource c q hq y))), (by
    intro x
    exact ⟨fromSource c q x, toSource_fromSource c q hq x⟩)⟩

theorem equiv_mk (hq : q ∈ c.piece 1) (x : R) : equiv c q hq (quotientMap q x) = normalize c q hq x := rfl

theorem normalize_kernel (hq : q ∈ c.piece 1) : RingHom.ker (normalize c q hq) = pointIdeal q := by
  apply le_antisymm
  · intro x hx
    have he : equiv c q hq (quotientMap q x) = equiv c q hq 0 := by
      change normalize c q hq x = _
      exact hx.trans (map_zero (equiv c q hq)).symm
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((equiv c q hq).injective he)
  · exact pointIdeal_le_normalize_ker c q hq

end DiamondIntegral.Section4.PointLocalizationEquivalence
