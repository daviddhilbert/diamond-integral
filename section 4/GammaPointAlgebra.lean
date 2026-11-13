import «section 4».GammaNamesSubgroup
import «section 4».GammaDefinableConvolution
import «section 4».EulerBoundedSupport

/-! The group ring of actual base-definable Gamma constants embeds as
the point-function convolution algebra. Coefficients are recovered by
evaluating at their own Gamma point, so injectivity is proved explicitly. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section4.GammaPointAlgebra
open GammaDefinableEuler GammaDefinableConvolution GammaNamesSubgroup EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pointMonoidHom (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    Multiplicative (additiveNames B) →* baseSubring B k where
  toFun a := ⟨point k (Multiplicative.toAdd a).val,
    point_mem_base B k _ (Multiplicative.toAdd a).property⟩
  map_one' := Subtype.ext (point_zero k)
  map_mul' a b := Subtype.ext
    (point_mul k (Multiplicative.toAdd a).val (Multiplicative.toAdd b).val).symm

def pointGroupRing (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    DefinableGammaGroupRing B →+* baseSubring B k :=
  ((AddMonoidAlgebra.lift ℤ (baseSubring B k) (additiveNames B)) (pointMonoidHom B k)).toRingHom

theorem pointGroupRing_single (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (a : additiveNames B) (n : ℤ) :
    pointGroupRing B k (AddMonoidAlgebra.single a n) = n • pointMonoidHom B k (Multiplicative.ofAdd a) :=
  AddMonoidAlgebra.lift_single (pointMonoidHom B k) a n

theorem pointGroupRing_eval (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (f : DefinableGammaGroupRing B) (a : additiveNames B) :
    (pointGroupRing B k f).val a.val = f.coeff a := by
  let ev : baseSubring B k →+ ℤ :=
    (evaluation k a.val).comp (baseSubring B k).subtype.toAddMonoidHom
  have hev (b : additiveNames B) : ev (pointMonoidHom B k (Multiplicative.ofAdd b)) =
      if b = a then 1 else 0 := by
    change point k b.val a.val = _
    by_cases h : b = a
    · subst b
      simp only [point_eval, ite_true]
    · have hv : a.val ≠ b.val := fun hh => h (Subtype.ext hh.symm)
      simp only [point_eval, hv, h, ite_false]
  change ev (pointGroupRing B k f) = _
  rw [show pointGroupRing B k f = f.coeff.sum
      (fun b n => n • pointMonoidHom B k (Multiplicative.ofAdd b)) from
    AddMonoidAlgebra.lift_apply (pointMonoidHom B k) f]
  simp only [Finsupp.sum, map_sum, map_zsmul, hev]
  simp only [zsmul_eq_mul, Int.cast_id, mul_ite, mul_one, mul_zero]
  change f.coeff.sum (fun b n => if b = a then n else 0) = f.coeff a
  simpa only [eq_comm] using Finsupp.sum_ite_self_eq f.coeff a

theorem pointGroupRing_injective (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    Function.Injective (pointGroupRing B k) := by
  intro f g h
  apply AddMonoidAlgebra.coeffAddEquiv.injective
  apply Finsupp.ext
  intro a
  change f.coeff a = g.coeff a
  have he := congrArg (fun v : baseSubring B k => v.val a.val) h
  simpa only [pointGroupRing_eval] using he

theorem pointGroupRing_coe (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (f : DefinableGammaGroupRing B) :
    (pointGroupRing B k f).val = f.coeff.sum (fun b n => n • point k b.val) := by
  rw [show pointGroupRing B k f = f.coeff.sum
      (fun b n => n • pointMonoidHom B k (Multiplicative.ofAdd b)) from
    AddMonoidAlgebra.lift_apply (pointMonoidHom B k) f]
  change (baseSubring B k).subtype (f.coeff.sum
    (fun b n => n • pointMonoidHom B k (Multiplicative.ofAdd b))) = _
  simp only [Finsupp.sum, map_sum, map_zsmul]
  rfl

theorem pointGroupRing_isDoublyBounded (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (f : DefinableGammaGroupRing B) : IsDoublyBounded (pointGroupRing B k f).val := by
  change (pointGroupRing B k f).val ∈ boundedSubring (Γ := PaperGamma (M := M)) k
  rw [pointGroupRing_coe]
  unfold Finsupp.sum
  exact (boundedSubring k).sum_mem (fun b _ =>
    (boundedSubring k).zsmul_mem (isDoublyBounded_point k b.val) _)

theorem totalEuler_pointGroupRing (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (f : DefinableGammaGroupRing B) :
    totalEuler k (pointGroupRing B k f).val = coefficientSum f.coeff := by
  let χ := (totalEuler k).comp (baseSubring B k).subtype
  have hp (b : additiveNames B) : χ (pointMonoidHom B k (Multiplicative.ofAdd b)) = 1 :=
    totalEuler_point k b.val
  change χ (pointGroupRing B k f) = f.coeff.sum (fun _ n => n)
  rw [show pointGroupRing B k f = f.coeff.sum
      (fun b n => n • pointMonoidHom B k (Multiplicative.ofAdd b)) from
    AddMonoidAlgebra.lift_apply (pointMonoidHom B k) f]
  simp only [Finsupp.sum, map_sum, map_zsmul, hp]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

def pointSubring (B : GammaParameters.Base (M := M)) (k : EulerKind) : Subring (baseSubring B k) :=
  (pointGroupRing B k).range

theorem ray_not_mem_pointSubring (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (a : additiveNames B) :
    (⟨ray k a.val, ray_mem_base B k a.val a.property⟩ : baseSubring B k) ∉ pointSubring B k := by
  rintro ⟨f, hf⟩
  have h := pointGroupRing_isDoublyBounded B k f
  rw [hf] at h
  exact ray_not_isDoublyBounded k a.val h

theorem line_not_mem_pointSubring (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    (⟨line k, line_mem_base B k⟩ : baseSubring B k) ∉ pointSubring B k := by
  rintro ⟨f, hf⟩
  have h := pointGroupRing_isDoublyBounded B k f
  rw [hf] at h
  exact line_not_isDoublyBounded k h

end DiamondIntegral.Section4.GammaPointAlgebra
