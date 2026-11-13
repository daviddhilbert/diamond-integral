import «section 4».GammaFunctionRing
import «section 4».EulerBoundedGenerators
import «section 4».EulerIntervalProducts

/-! Bounded functions over the original base and their actual point and
interval generators. Canonical coefficient provenance justifies generation
using only base-definable thresholds. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedFunctions
open GammaDefinableEuler GammaDefinableFunctions GammaGroupNames GammaDefinableConvolution EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def boundedBaseSubring (B : Base (M := M)) (k : EulerKind) :
    Subring (EulerFunction k (PaperGamma (M := M))) :=
  baseSubring B k ⊓ boundedSubring (Γ := PaperGamma (M := M)) k

abbrev Name (B : Base (M := M)) :=
  {a : PaperGamma (M := M) // GammaDefinableClosureAtBase B (toPaperGamma.symm a)}

def zeroName (B : Base (M := M)) : Name B := ⟨0, zero_definable_base B⟩

def basePoint (B : Base (M := M)) (k : EulerKind) (a : Name B) : boundedBaseSubring B k :=
  ⟨point k a.val, point_mem_base B k a.val a.property, isDoublyBounded_point k a.val⟩

def baseInterval (B : Base (M := M)) (k : EulerKind) (a : Name B) : boundedBaseSubring B k := by
  refine ⟨boundedInterval k a.val, ?_, isDoublyBounded_boundedInterval k a.val⟩
  by_cases ha : 0 ≤ a.val
  · rw [boundedInterval_nonneg_form k a.val ha]
    exact (baseSubring B k).sub_mem
      ((baseSubring B k).sub_mem (ray_mem_base B k 0 (zero_definable_base B))
        (ray_mem_base B k a.val a.property)) (point_mem_base B k a.val a.property)
  · rw [boundedInterval_nonpos_form k a.val (le_of_not_ge ha)]
    exact (baseSubring B k).sub_mem
      ((baseSubring B k).sub_mem (ray_mem_base B k a.val a.property)
        (ray_mem_base B k 0 (zero_definable_base B))) (point_mem_base B k 0 (zero_definable_base B))

def baseRayDifference (B : Base (M := M)) (k : EulerKind) (a : Name B) : boundedBaseSubring B k :=
  if 0 < a.val then -baseInterval B k a - basePoint B k a
  else baseInterval B k a + basePoint B k (zeroName B)

theorem basePoint_zero (B : Base (M := M)) (k : EulerKind) :
    basePoint B k (zeroName B) = 1 := Subtype.ext (point_zero k)

theorem baseRayDifference_coe (B : Base (M := M)) (k : EulerKind) (a : Name B) :
    (baseRayDifference B k a).val = ray k a.val - ray k 0 := by
  have h := boundedRayDifference_coe k a.val
  by_cases ha : 0 < a.val
  · rw [baseRayDifference, ite_eq_left ha]
    change -boundedInterval k a.val - point k a.val = _
    rw [boundedRayDifference, ite_eq_left ha] at h
    exact h
  · rw [baseRayDifference, ite_eq_right ha]
    change boundedInterval k a.val + point k 0 = _
    rw [boundedRayDifference, ite_eq_right ha] at h
    exact h

def pointDefault (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M)) : boundedBaseSubring B k :=
  if ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a) then basePoint B k ⟨a, ha⟩ else 0

def rayDefault (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M)) : boundedBaseSubring B k :=
  if ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a) then baseRayDifference B k ⟨a, ha⟩ else 0

theorem pointDefault_weighted (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M)) (n : ℤ)
    (hn : n ≠ 0 → GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    (n • pointDefault B k a).val = n • point k a := by
  by_cases ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)
  · rw [pointDefault, dite_eq_left ha]
    rfl
  · have hn0 : n = 0 := by by_contra h; exact ha (hn h)
    simp only [hn0, zero_zsmul, ZeroMemClass.coe_zero]

theorem rayDefault_weighted (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M)) (n : ℤ)
    (hn : n ≠ 0 → GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    (n • rayDefault B k a).val = n • (ray k a - ray k 0) := by
  by_cases ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)
  · rw [rayDefault, dite_eq_left ha]
    change n • (baseRayDifference B k ⟨a, ha⟩).val = _
    rw [baseRayDifference_coe]
  · have hn0 : n = 0 := by by_contra h; exact ha (hn h)
    simp only [hn0, zero_zsmul, ZeroMemClass.coe_zero]

def baseCombination (B : Base (M := M)) (k : EulerKind)
    (v : StepCoefficients (PaperGamma (M := M))) : boundedBaseSubring B k :=
  v.2.1.sum (fun a n => n • pointDefault B k a) +
    v.2.2.sum (fun a n => n • rayDefault B k a)

theorem baseCombination_coe (B : Base (M := M)) (k : EulerKind)
    (v : StepCoefficients (PaperGamma (M := M)))
    (hv : ∀ a, v.2.1 a ≠ 0 ∨ v.2.2 a ≠ 0 →
      GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    (baseCombination B k v).val = (boundedCombination k v).val := by
  rw [boundedCombination_coe]
  change (boundedBaseSubring B k).subtype (baseCombination B k v) = _
  simp only [baseCombination, Finsupp.sum, map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    exact pointDefault_weighted B k a (v.2.1 a) (fun h => hv a (Or.inl h))
  · apply Finset.sum_congr rfl
    intro a _
    exact rayDefault_weighted B k a (v.2.2 a) (fun h => hv a (Or.inr h))

theorem base_generator_expansion (B : Base (M := M)) (k : EulerKind)
    (f : boundedBaseSubring B k) : ∃ v, f = baseCombination B k v := by
  let v := (coefficientEquiv k).symm f.val
  have hv := (integerDefinable_iff_coefficients B k f.val).mp f.property.1
  obtain ⟨hc, hq⟩ := (isDoublyBounded_iff_coefficients k f.val).mp f.property.2
  refine ⟨v, ?_⟩
  apply Subtype.ext
  rw [baseCombination_coe B k v hv]
  apply eval_injective k
  funext x
  change f.val x = (boundedCombination k v).val x
  rw [boundedCombination_eval k v hq x, ← coefficients_eval k f.val x]
  simp only [stepEval, hc, zero_add]
  rfl

theorem base_bounded_additive_ext {A : Type*} [AddCommGroup A]
    (B : Base (M := M)) (k : EulerKind) (f g : boundedBaseSubring B k →+ A)
    (hp : ∀ a : Name B, f (basePoint B k a) = g (basePoint B k a))
    (ho : ∀ a : Name B, f (baseInterval B k a) = g (baseInterval B k a)) : f = g := by
  have hq (a : Name B) : f (baseRayDifference B k a) = g (baseRayDifference B k a) := by
    unfold baseRayDifference
    split_ifs <;> simp only [map_sub, map_neg, map_add, hp, ho]
  have hpd (a : PaperGamma (M := M)) : f (pointDefault B k a) = g (pointDefault B k a) := by
    unfold pointDefault
    split_ifs <;> simp only [hp, map_zero]
  have hqd (a : PaperGamma (M := M)) : f (rayDefault B k a) = g (rayDefault B k a) := by
    unfold rayDefault
    split_ifs <;> simp only [hq, map_zero]
  apply AddMonoidHom.ext
  intro h
  obtain ⟨v, rfl⟩ := base_generator_expansion B k h
  simp only [baseCombination, Finsupp.sum, map_add, map_sum, map_zsmul, hpd, hqd]

def baseBoundedEuler (B : Base (M := M)) (k : EulerKind) : boundedBaseSubring B k →+* ℤ :=
  (totalEuler k).comp (boundedBaseSubring B k).subtype

theorem baseBoundedEuler_point (B : Base (M := M)) (k : EulerKind) (a : Name B) :
    baseBoundedEuler B k (basePoint B k a) = 1 := totalEuler_point k a.val

theorem baseBoundedEuler_interval (B : Base (M := M)) (k : EulerKind) (a : Name B) :
    baseBoundedEuler B k (baseInterval B k a) = -1 := totalEuler_boundedInterval k a.val

end DiamondIntegral.Section4.GammaBoundedFunctions
