import «section 4».RVNamedMultiplication
import «section 4».RVForgetScissors
import «section 4».RVRadiusGenerators
import «section 4».RVMeasuredSpecialClasses

/-! Named RV scaling identifies the full proper RV preimages of a ray
and its Gamma translate, as actual ordinary objects over the original
base. No volume-preserving claim is made. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVScaledRays
open RVMeasuredCharts RVNamedMultiplication RVSharpCharts GammaRVLifts
open GammaOrderLogic GammaDefinableMaps GammaGroupNames RVRadiusGenerators
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def unitOfCode (t : Code (M := M)) : (CanonicalRV.RVSort M)ˣ :=
  Units.mk0 t.val (by
    intro h
    exact t.property ((congrArg Subtype.val h).trans RVOperations.zero_val))

def inverseCode (t : Code (M := M)) : Code (M := M) :=
  ⟨(unitOfCode t)⁻¹.val, (unit_nonzero_code (unitOfCode t)⁻¹).2⟩

theorem scale_nonzero (t : Code (M := M)) {u : M} (hu : NonzeroRV u) :
    NonzeroRV (iRVMul (raw t) u) := by
  refine ⟨rv_mul_mem hM (raw_rv t) hu.1, ?_⟩
  intro h
  exact ((rv_mul_eq_zero_of_model hM (raw_rv t) hu.1).mp h).elim (raw_ne_zero t) hu.2

theorem inverseCode_value (t : Code (M := M)) :
    codeValue (raw (inverseCode t)) = (value t)⁻¹ := by
  change valueHom ((unitOfCode t)⁻¹) = (value t)⁻¹
  rw [map_inv]
  congr 1
  exact codeValue_raw t

theorem scale_inverse (t : Code (M := M)) (u : Fin 1 → M) (hu : iRV (u 0)) :
    scale (raw t) (scale (raw (inverseCode t)) u) = u := by
  have he : (unitOfCode t).val * ((unitOfCode t)⁻¹.val * (⟨u 0, hu⟩ : CanonicalRV.RVSort M)) =
      (⟨u 0, hu⟩ : CanonicalRV.RVSort M) := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hr := congrArg Subtype.val he
  funext i
  fin_cases i
  simp only [RVOperations.mul_val] at hr
  change iRVMul (raw t) (iRVMul (raw (inverseCode t)) (u 0)) = u 0
  exact hr

theorem scale_injective (t : Code (M := M)) :
    Set.InjOn (scale (raw t)) {u : Fin 1 → M | NonzeroRV (u 0)} := by
  intro u hu v hv he
  have he0 := congrFun he 0
  have hr : t.val * (⟨u 0, hu.1⟩ : CanonicalRV.RVSort M) =
      t.val * (⟨v 0, hv.1⟩ : CanonicalRV.RVSort M) := by
    apply Subtype.ext
    simpa only [RVOperations.mul_val, scale, raw, Matrix.cons_val_zero] using he0
  have ht0 : t.val ≠ (0 : CanonicalRV.RVSort M) := (unitOfCode t).ne_zero
  have huv := congrArg Subtype.val (mul_left_cancel₀ ht0 hr)
  funext i
  fin_cases i
  exact huv

def above (γ : Values.Gamma (M := M)) : Set (Fin 1 → Values.Gamma (M := M)) := {z | γ < z 0}

theorem above_definable (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : GammaDefinable B (above γ) :=
  GammaMapOrder.lt_maps_definable B _ _ (constant_definable B γ hγ) (projection_definable B 0)

def aboveChart (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : Chart B 1 :=
  sharpChart (GammaChartOperations.ofTotal B 1 (above γ) (above_definable B γ hγ) (fun _ => 1)
    (constant_definable B 1 (one_definable_base B)))

theorem scale_ray_bijective (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (t : RadiusLift B γ) :
    Set.BijOn (scale (raw t.point))
      (sharpChart (RVMeasuredSpecialClasses.rayChart B)).domain (aboveChart B γ hγ).domain := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    change Proper u ∧ 1 < codeValue (u 0) at hu
    change Proper (scale (raw t.point) u) ∧ γ < codeValue (iRVMul (raw t.point) (u 0))
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      exact scale_nonzero t.point (hu.1 0)
    · rw [codeValue_mul _ _ ⟨raw_rv t.point, raw_ne_zero t.point⟩ (hu.1 0),
        codeValue_raw, t.value_eq]
      simpa only [mul_one] using mul_lt_mul_right hu.2 γ
  · apply (scale_injective t.point).mono
    intro u hu
    exact hu.1 0
  · intro v hv
    change Proper v ∧ γ < codeValue (v 0) at hv
    let u := scale (raw (inverseCode t.point)) v
    have hu0 : NonzeroRV (u 0) := scale_nonzero (inverseCode t.point) (hv.1 0)
    refine ⟨u, ?_, scale_inverse t.point v (hv.1 0).1⟩
    change Proper u ∧ 1 < codeValue (u 0)
    refine ⟨(by intro i; fin_cases i; exact hu0), ?_⟩
    change 1 < codeValue (iRVMul (raw (inverseCode t.point)) (v 0))
    rw [codeValue_mul _ _ ⟨raw_rv _, raw_ne_zero _⟩ (hv.1 0), inverseCode_value, t.value_eq]
    have h := mul_lt_mul_right hv.2 γ⁻¹
    simpa only [inv_mul_cancel] using h

theorem annulus_union_above (γ : Values.Gamma (M := M)) (hγ : 1 ≤ γ) :
    GammaRadiusAnnulus.annulus γ ∪ above γ = GammaCounterweightedRay.positiveRay (M := M) := by
  ext z
  change ((1 < z 0 ∧ z 0 ≤ γ) ∨ γ < z 0) ↔ 1 < z 0
  constructor
  · rintro (hz | hz)
    · exact hz.1
    · exact hγ.trans_lt hz
  · intro hz
    by_cases hh : z 0 ≤ γ
    · exact Or.inl ⟨hz, hh⟩
    · exact Or.inr (lt_of_not_ge hh)

theorem annulus_inter_above (γ : Values.Gamma (M := M)) :
    GammaRadiusAnnulus.annulus γ ∩ above γ = ∅ := by
  ext z
  change ((1 < z 0 ∧ z 0 ≤ γ) ∧ γ < z 0) ↔ False
  exact ⟨fun hz => not_lt_of_ge hz.1.2 hz.2, fun hz => hz.elim⟩

def rayIso (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (t : RadiusLift B γ) :
    RVForgetScissors.UnderlyingIso (sharpChart (RVMeasuredSpecialClasses.rayChart B))
      (aboveChart B γ hγ) :=
  RVForgetScissors.ofMap _ _ (scale (raw t.point))
    (graphOn_definable B _ (raw_rv t.point) t.definable _
      (sharpChart (RVMeasuredSpecialClasses.rayChart B)).domain_definable)
    (scale_ray_bijective B γ hγ t)

end DiamondIntegral.Section4.RVScaledRays
