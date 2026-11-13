import «section 4».GammaGroupNames
import «section 4».EulerConvolution

/-! The manuscript's original-base unary definable functions form a ring
under the actual Euler convolution. Closure follows from the proved
coefficient classification and generator table, not an HK/Fubini premise. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaDefinableConvolution
open GammaDefinableEuler GammaDefinableFunctions GammaGroupNames EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def baseSubgroup (B : Base (M := M)) (k : EulerKind) :
    AddSubgroup (EulerFunction k (PaperGamma (M := M))) where
  carrier := {f | IntegerDefinable B (fun γ => f (toPaperGamma γ))}
  zero_mem' := by simpa only [Set.mem_ofPred_eq, eval_zero] using integerDefinable_const B 0
  add_mem' := fun hf hg => by simpa only [Set.mem_ofPred_eq, eval_add] using hf.add hg
  neg_mem' := fun hf => by simpa only [Set.mem_ofPred_eq, eval_neg] using hf.map (fun m => -m)

theorem line_mem_base (B : Base (M := M)) (k : EulerKind) :
    line (Γ := PaperGamma (M := M)) k ∈ baseSubgroup B k := by
  change IntegerDefinable B (fun γ => line k (toPaperGamma γ))
  simpa only [line_eval] using integerDefinable_const B 1

theorem point_mem_base (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M))
    (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    point k a ∈ baseSubgroup B k := point_integerDefinable B k a ha

theorem ray_mem_base (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M))
    (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a)) :
    ray k a ∈ baseSubgroup B k := ray_integerDefinable B k a ha

theorem base_generator_induction (B : Base (M := M)) (k : EulerKind)
    (H : AddSubgroup (EulerFunction k (PaperGamma (M := M))))
    (hl : line k ∈ H)
    (hp : ∀ a, GammaDefinableClosureAtBase B (toPaperGamma.symm a) → point k a ∈ H)
    (hq : ∀ a, GammaDefinableClosureAtBase B (toPaperGamma.symm a) → ray k a ∈ H)
    (f : EulerFunction k (PaperGamma (M := M))) (hf : f ∈ baseSubgroup B k) : f ∈ H := by
  let v := (coefficientEquiv k).symm f
  have hv := (integerDefinable_iff_coefficients B k f).mp hf
  have he : linearCombination k v = f := by
    rw [← ofCoefficients_eq_linearCombination]
    exact (coefficientEquiv k).apply_symm_apply f
  rw [← he]
  change v.1 • line k + (∑ a ∈ v.2.1.support, v.2.1 a • point k a) +
    (∑ a ∈ v.2.2.support, v.2.2 a • ray k a) ∈ H
  apply H.add_mem
  · apply H.add_mem (H.zsmul_mem hl v.1)
    exact H.sum_mem (fun a ha => H.zsmul_mem
      (hp a (hv a (Or.inl (Finsupp.mem_support_iff.mp ha)))) _)
  · exact H.sum_mem (fun a ha => H.zsmul_mem
      (hq a (hv a (Or.inr (Finsupp.mem_support_iff.mp ha)))) _)

def leftProduct (k : EulerKind) (f : EulerFunction k (PaperGamma (M := M))) :
    EulerFunction k (PaperGamma (M := M)) →+ EulerFunction k (PaperGamma (M := M)) where
  toFun g := f * g
  map_zero' := mul_zero f
  map_add' g h := mul_add f g h

def rightProduct (k : EulerKind) (g : EulerFunction k (PaperGamma (M := M))) :
    EulerFunction k (PaperGamma (M := M)) →+ EulerFunction k (PaperGamma (M := M)) where
  toFun f := f * g
  map_zero' := zero_mul g
  map_add' f h := add_mul f h g

theorem line_mul_mem_base (B : Base (M := M)) (k : EulerKind)
    (g : EulerFunction k (PaperGamma (M := M))) (hg : g ∈ baseSubgroup B k) :
    line k * g ∈ baseSubgroup B k := by
  refine base_generator_induction B k
    ((baseSubgroup B k).comap (leftProduct k (line k))) ?_ ?_ ?_ g hg
  · change line (Γ := PaperGamma (M := M)) k * line k ∈ baseSubgroup B k
    rw [line_mul]
    exact (baseSubgroup B k).zsmul_mem (line_mem_base B k) k.lineValue
  · intro a _
    change line k * point k a ∈ baseSubgroup B k
    rw [line_point]
    exact line_mem_base B k
  · intro a _
    change line k * ray k a ∈ baseSubgroup B k
    rw [line_ray]
    exact (baseSubgroup B k).zsmul_mem (line_mem_base B k) k.rayValue

theorem point_mul_mem_base (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M))
    (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a))
    (g : EulerFunction k (PaperGamma (M := M))) (hg : g ∈ baseSubgroup B k) :
    point k a * g ∈ baseSubgroup B k := by
  refine base_generator_induction B k
    ((baseSubgroup B k).comap (leftProduct k (point k a))) ?_ ?_ ?_ g hg
  · change point k a * line k ∈ baseSubgroup B k
    rw [mul_comm, line_point]
    exact line_mem_base B k
  · intro b hb
    change point k a * point k b ∈ baseSubgroup B k
    rw [point_mul]
    exact point_mem_base B k (a + b) (add_definable_base B a b ha hb)
  · intro b hb
    change point k a * ray k b ∈ baseSubgroup B k
    rw [point_ray]
    exact ray_mem_base B k (a + b) (add_definable_base B a b ha hb)

theorem ray_mul_mem_base (B : Base (M := M)) (k : EulerKind) (a : PaperGamma (M := M))
    (ha : GammaDefinableClosureAtBase B (toPaperGamma.symm a))
    (g : EulerFunction k (PaperGamma (M := M))) (hg : g ∈ baseSubgroup B k) :
    ray k a * g ∈ baseSubgroup B k := by
  refine base_generator_induction B k
    ((baseSubgroup B k).comap (leftProduct k (ray k a))) ?_ ?_ ?_ g hg
  · change ray k a * line k ∈ baseSubgroup B k
    rw [mul_comm, line_ray]
    exact (baseSubgroup B k).zsmul_mem (line_mem_base B k) k.rayValue
  · intro b hb
    change ray k a * point k b ∈ baseSubgroup B k
    rw [mul_comm, point_ray]
    exact ray_mem_base B k (b + a) (add_definable_base B b a hb ha)
  · intro b hb
    change ray k a * ray k b ∈ baseSubgroup B k
    rw [ray_mul]
    exact (baseSubgroup B k).neg_mem
      (ray_mem_base B k (a + b) (add_definable_base B a b ha hb))

theorem mul_mem_base (B : Base (M := M)) (k : EulerKind)
    (f g : EulerFunction k (PaperGamma (M := M)))
    (hf : f ∈ baseSubgroup B k) (hg : g ∈ baseSubgroup B k) : f * g ∈ baseSubgroup B k := by
  refine base_generator_induction B k
    ((baseSubgroup B k).comap (rightProduct k g)) ?_ ?_ ?_ f hf
  · exact line_mul_mem_base B k g hg
  · intro a ha
    exact point_mul_mem_base B k a ha g hg
  · intro a ha
    exact ray_mul_mem_base B k a ha g hg

def baseSubring (B : Base (M := M)) (k : EulerKind) :
    Subring (EulerFunction k (PaperGamma (M := M))) where
  __ := baseSubgroup B k
  one_mem' := by
    rw [← point_zero k]
    exact point_mem_base B k 0 (zero_definable_base B)
  mul_mem' := fun hf hg => mul_mem_base B k _ _ hf hg

theorem convolution_integerDefinable (B : Base (M := M)) (k : EulerKind)
    (f g : EulerFunction k (PaperGamma (M := M)))
    (hf : IntegerDefinable B (fun γ => f (toPaperGamma γ)))
    (hg : IntegerDefinable B (fun γ => g (toPaperGamma γ))) :
    IntegerDefinable B (fun γ => convolutionValue k f g (toPaperGamma γ)) := by
  have h : IntegerDefinable B (fun γ => (f * g) (toPaperGamma γ)) :=
    mul_mem_base B k f g hf hg
  simpa only [convolutionValue_eq_product] using h

end DiamondIntegral.Section4.GammaDefinableConvolution
