import «section 6».AffineTailDifferentiability
import Mathlib.Tactic.FieldSimp

/-! Full valued-field differentiation of the reciprocal away from zero,
in the actual value quotient and with no valuation-rank restriction. -/

noncomputable section
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

private theorem reciprocal_remainder {K : Type*} [Field K] (a h : K)
    (ha : a ≠ 0) (hs : a+h ≠ 0) :
    (a+h)⁻¹-a⁻¹-(-(a⁻¹ ^ 2)*h)=h^2/(a^2*(a+h)) := by
  field_simp
  <;> ring

set_option backward.isDefEq.respectTransparency false in
theorem hasVFDerivativeAt_reciprocal (a : Fin 1 → VF M) (ha : a 0 ≠ 0) :
    HasVFDerivativeAt (fun x (_ : Fin 1) => (x 0)⁻¹) a
      (-((a 0)⁻¹ ^ 2) • (LinearMap.id : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M))) := by
  let G := MonoidWithZeroHom.ValueGroup₀ (.ofClass (Values.presentationValuation (M := M)))
  let w : Valuation (VF M) G := Values.presentationValuation.restrict
  let φ : Values.GammaTop (M := M) ≃ OrderDual G := Values.paperValueEquiv
  let ψ (z : Values.GammaTop (M := M)) : G := OrderDual.ofDual (φ z)
  have hψ (z : VF M) : ψ (Values.vfValueHom z) = w z :=
    Values.valueEquiv_apply_vf Values.presentationValuation Values.presentation_compatible z
  have hψ0 : ψ 0 = 0 := Values.paperValue_zero
  have hψmul (x y : Values.GammaTop (M := M)) : ψ (x*y) = ψ x * ψ y := Values.paperValue_mul x y
  have ht (h : Fin 1 → VF M) : vfTupleValue h = Values.vfValueHom (h 0) := by
    obtain ⟨i,hi⟩ := vfTupleValue_eq_component h (by decide)
    fin_cases i
    exact hi
  have hwa : 0 < w (a 0) := pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr ha)
  apply hasVFDerivativeAt_of_components
  intro i ε
  fin_cases i
  let E := ψ ε.val
  have hE : 0 < E := pos_iff_ne_zero.mpr (fun h =>
    finiteValue_ne_zero ε (φ.injective (h.trans hψ0.symm)))
  let T := min (w (a 0)) (E * w (a 0)^3)
  have hT : 0 < T := lt_min hwa (mul_pos hE (pow_pos hwa 3))
  have hpre : ψ (φ.symm (OrderDual.toDual T)) = T := φ.apply_symm_apply _
  let δ : Gamma M := ⟨φ.symm (OrderDual.toDual T),fun h => hT.ne (by
    rw [← hψ0]
    exact (congrArg ψ (Values.infinity_eq_zero.symm.trans h.symm)).trans hpre)⟩
  refine ⟨δ,fun h hn hh => ?_⟩
  have hh0 : h 0 ≠ 0 := by
    intro he
    apply hn
    funext j
    fin_cases j
    exact he
  have hwh : 0 < w (h 0) := pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hh0)
  have hlt : w (h 0) < T := by
    rw [ht] at hh
    have h : ψ (Values.vfValueHom (h 0)) < ψ δ.val := hh
    rwa [hψ,hpre] at h
  have hsum : w (a 0 + h 0) = w (a 0) := w.map_add_eq_of_lt_left (hlt.trans_le (min_le_left _ _))
  have hsum0 : a 0 + h 0 ≠ 0 := w.ne_zero_iff.mp (hsum ▸ hwa.ne')
  have herr := reciprocal_remainder (a 0) (h 0) ha hsum0
  change ψ (Values.vfValueHom ((a 0 + h 0)⁻¹ - (a 0)⁻¹ - (-((a 0)⁻¹ ^ 2) * h 0))) <
    ψ (ε.val * vfTupleValue h)
  rw [herr,hψ,hψmul,ht,hψ,map_div₀,map_pow,map_mul,map_pow,hsum]
  have hsmall : w (h 0) / w (a 0)^3 < E :=
    (div_lt_iff₀ (pow_pos hwa 3)).mpr (hlt.trans_le (min_le_right _ _))
  calc
    w (h 0)^2 / (w (a 0)^2 * w (a 0)) = (w (h 0) / w (a 0)^3) * w (h 0) := by
      simp only [pow_succ,pow_zero,mul_one,one_mul,div_eq_mul_inv,mul_inv_rev,inv_one]
      ac_rfl
    _ < E * w (h 0) := mul_lt_mul_of_pos_right hsmall hwh

set_option backward.isDefEq.respectTransparency false in
theorem VFDifferentiableAt.reciprocal {f : (Fin n → VF M) → Fin 1 → VF M}
    {a : Fin n → VF M} (hf : VFDifferentiableAt f a) (ha : f a 0 ≠ 0) :
    VFDifferentiableAt (fun x (_ : Fin 1) => (f x 0)⁻¹) a := by
  obtain ⟨L,hL⟩ := hf
  exact ⟨_,(hasVFDerivativeAt_reciprocal (f a) ha).comp hL⟩

end DiamondIntegral.Section6
