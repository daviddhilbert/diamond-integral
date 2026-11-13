import «section 4».GammaBoundedFunctions
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Remark 4.14's unary bounded-function quotient over the original base.
Only base-definable Gamma thresholds index its generators. The ideal is
proved equal to the Euler kernel before taking the quotient equivalence. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedQuotient
open GammaBoundedFunctions

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def baseEulerGenerators (B : Base (M := M)) (k : EulerKind) : Set (boundedBaseSubring B k) :=
  {x | ∃ a : Name B, x = basePoint B k a - 1} ∪
  {x | ∃ a : Name B, x = baseInterval B k a + 1}

def baseEulerIdeal (B : Base (M := M)) (k : EulerKind) : Ideal (boundedBaseSubring B k) :=
  Ideal.span (baseEulerGenerators B k)

abbrev BoundedBaseQuotient (B : Base (M := M)) (k : EulerKind) :=
  boundedBaseSubring B k ⧸ baseEulerIdeal B k

theorem baseEulerIdeal_le_kernel (B : Base (M := M)) (k : EulerKind) :
    baseEulerIdeal B k ≤ RingHom.ker (baseBoundedEuler B k) := by
  apply Ideal.span_le.mpr
  rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · apply RingHom.mem_ker.mpr
    rw [map_sub, baseBoundedEuler_point, map_one, sub_self]
  · apply RingHom.mem_ker.mpr
    rw [map_add, baseBoundedEuler_interval, map_one]
    exact neg_add_cancel 1

def baseQuotientMap (B : Base (M := M)) (k : EulerKind) :
    boundedBaseSubring B k →+* BoundedBaseQuotient B k := Ideal.Quotient.mk (baseEulerIdeal B k)

theorem baseQuotientMap_point (B : Base (M := M)) (k : EulerKind) (a : Name B) :
    baseQuotientMap B k (basePoint B k a) = 1 := by
  have hm : basePoint B k a - 1 ∈ baseEulerIdeal B k := Ideal.subset_span (Or.inl ⟨a, rfl⟩)
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  change baseQuotientMap B k (basePoint B k a - 1) = 0 at h
  rw [(baseQuotientMap B k).map_sub, (baseQuotientMap B k).map_one] at h
  exact sub_eq_zero.mp h

theorem baseQuotientMap_interval (B : Base (M := M)) (k : EulerKind) (a : Name B) :
    baseQuotientMap B k (baseInterval B k a) = -1 := by
  have hm : baseInterval B k a + 1 ∈ baseEulerIdeal B k := Ideal.subset_span (Or.inr ⟨a, rfl⟩)
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  change baseQuotientMap B k (baseInterval B k a + 1) = 0 at h
  rw [(baseQuotientMap B k).map_add, (baseQuotientMap B k).map_one] at h
  calc
    _ = (baseQuotientMap B k (baseInterval B k a) + 1) - 1 := by abel
    _ = -1 := by rw [h, zero_sub]

theorem baseQuotientMap_eq_intEuler (B : Base (M := M)) (k : EulerKind) :
    baseQuotientMap B k = (Int.castRingHom (BoundedBaseQuotient B k)).comp (baseBoundedEuler B k) := by
  have h : (baseQuotientMap B k).toAddMonoidHom =
      ((Int.castRingHom (BoundedBaseQuotient B k)).comp (baseBoundedEuler B k)).toAddMonoidHom := by
    apply base_bounded_additive_ext B k
    · intro a
      change baseQuotientMap B k (basePoint B k a) =
        (Int.castRingHom (BoundedBaseQuotient B k)) (baseBoundedEuler B k (basePoint B k a))
      rw [baseQuotientMap_point, baseBoundedEuler_point]
      exact (Int.castRingHom (BoundedBaseQuotient B k)).map_one.symm
    · intro a
      change baseQuotientMap B k (baseInterval B k a) =
        (Int.castRingHom (BoundedBaseQuotient B k)) (baseBoundedEuler B k (baseInterval B k a))
      rw [baseQuotientMap_interval, baseBoundedEuler_interval,
        (Int.castRingHom (BoundedBaseQuotient B k)).map_neg,
        (Int.castRingHom (BoundedBaseQuotient B k)).map_one]
  exact RingHom.ext (fun x => DFunLike.congr_fun h x)

theorem baseEulerIdeal_eq_kernel (B : Base (M := M)) (k : EulerKind) :
    baseEulerIdeal B k = RingHom.ker (baseBoundedEuler B k) := by
  apply le_antisymm (baseEulerIdeal_le_kernel B k)
  intro f hf
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change baseQuotientMap B k f = 0
  rw [DFunLike.congr_fun (baseQuotientMap_eq_intEuler B k) f]
  change (Int.castRingHom (BoundedBaseQuotient B k)) (baseBoundedEuler B k f) = 0
  rw [RingHom.mem_ker.mp hf, map_zero]

def boundedBaseQuotientEquiv (B : Base (M := M)) (k : EulerKind) :
    BoundedBaseQuotient B k ≃+* ℤ := by
  change (boundedBaseSubring B k ⧸ baseEulerIdeal B k) ≃+* ℤ
  rw [baseEulerIdeal_eq_kernel]
  apply RingHom.quotientKerEquivOfSurjective
  intro n
  refine ⟨n, ?_⟩
  simpa only [Int.cast_id] using map_intCast (baseBoundedEuler B k) n

end DiamondIntegral.Section4.GammaBoundedQuotient
