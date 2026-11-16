import «section 6».FiniteApertureProfiles
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! An ideal-level test for the proposed aperture repair. In the group
ring of values, relations supported on a subgroup do not imply a nonzero
point relation in another coset, even after arbitrary ring coefficients.
The pullback theorem makes its specialization premise explicit. This is
the algebraic separator, not a constructed specialization on the complete
native RV Grothendieck ring. No such native bridge is assumed as an axiom. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical

namespace DiamondIntegral.Section6.ApertureIdealTest

variable {W : Type*} [CommGroup W]

def relation (w : W) (k : ℤ) : MonoidAlgebra ℤ W :=
  MonoidAlgebra.single w k - MonoidAlgebra.single 1 k

def quotientMap (H : Subgroup W) : MonoidAlgebra ℤ W →+* MonoidAlgebra ℤ (W ⧸ H) :=
  MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' H)

def scalarIdeal (H : Subgroup W) : Ideal (MonoidAlgebra ℤ W) :=
  Ideal.span {x | ∃ w ∈ H, x = relation w 1}

theorem quotient_relation_zero (H : Subgroup W) (w : W) (hw : w ∈ H) (k : ℤ) :
    quotientMap H (relation w k) = 0 := by
  have he : (w : W ⧸ H) = ((1 : W) : W ⧸ H) :=
    QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_one] using hw)
  rw [relation,map_sub]
  change MonoidAlgebra.mapDomain (QuotientGroup.mk' H) (MonoidAlgebra.single w k) -
    MonoidAlgebra.mapDomain (QuotientGroup.mk' H) (MonoidAlgebra.single 1 k) = 0
  rw [MonoidAlgebra.mapDomain_single,MonoidAlgebra.mapDomain_single]
  change MonoidAlgebra.single (w : W ⧸ H) k - MonoidAlgebra.single ((1 : W) : W ⧸ H) k = 0
  rw [he,sub_self]

theorem scalarIdeal_le_kernel (H : Subgroup W) : scalarIdeal H ≤ RingHom.ker (quotientMap H) := by
  apply Ideal.span_le.mpr
  rintro x ⟨w,hw,rfl⟩
  exact quotient_relation_zero H w hw 1

theorem quotient_relation_ne_zero (H : Subgroup W) (w : W) (hw : w ∉ H)
    (k : ℤ) (hk : k ≠ 0) : quotientMap H (relation w k) ≠ 0 := by
  have he : (w : W ⧸ H) ≠ ((1 : W) : W ⧸ H) := by
    intro h
    exact hw (by simpa only [div_one] using QuotientGroup.eq_iff_div_mem.mp h)
  intro h
  rw [relation,map_sub] at h
  change MonoidAlgebra.mapDomain (QuotientGroup.mk' H) (MonoidAlgebra.single w k) -
    MonoidAlgebra.mapDomain (QuotientGroup.mk' H) (MonoidAlgebra.single 1 k) = 0 at h
  rw [MonoidAlgebra.mapDomain_single,MonoidAlgebra.mapDomain_single] at h
  have hc := congrArg (fun x : MonoidAlgebra ℤ (W ⧸ H) => x.coeff (w : W ⧸ H)) (sub_eq_zero.mp h)
  change (Finsupp.single (w : W ⧸ H) k) (w : W ⧸ H) =
    (Finsupp.single ((1 : W) : W ⧸ H) k) (w : W ⧸ H) at hc
  simp only [Finsupp.single_eq_same,Finsupp.single_eq_of_ne he] at hc
  exact hk hc

theorem relation_not_mem_scalarIdeal (H : Subgroup W) (w : W) (hw : w ∉ H)
    (k : ℤ) (hk : k ≠ 0) : relation w k ∉ scalarIdeal H := by
  intro h
  exact quotient_relation_ne_zero H w hw k hk (scalarIdeal_le_kernel H h)

theorem not_mem_span_of_specialization {R : Type*} [CommRing R]
    (H : Subgroup W) (φ : R →+* MonoidAlgebra ℤ W) (P : Set R)
    (hP : ∀ p ∈ P, φ p ∈ scalarIdeal H) (q : R) (w : W) (hw : w ∉ H)
    (k : ℤ) (hk : k ≠ 0) (hφ : φ q = relation w k) : q ∉ Ideal.span P := by
  have hSpan : Ideal.span P ≤ RingHom.ker ((quotientMap H).comp φ) := by
    apply Ideal.span_le.mpr
    intro p hp
    exact scalarIdeal_le_kernel H (hP p hp)
  intro h
  have hz : quotientMap H (φ q) = 0 := hSpan h
  rw [hφ] at hz
  exact quotient_relation_ne_zero H w hw k hk hz

end DiamondIntegral.Section6.ApertureIdealTest
