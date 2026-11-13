import «section 4».RVScaledRays
import «section 4».RVWeightScaling
import «section 4».RESOrdinaryPoints

/-! The measured form of named RV scaling. The degree-zero volume weight
is retained, so the resulting identities hold in the actual measured RV
chart ring before any RES or radius quotient. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredScaling
open RVMeasuredCharts RVChartRing RVScaledRays RVWeightScaling RVRadiusGenerators
open RVPointChoices GammaRVLifts GammaGroupNames RVSharpCharts RVNamedMultiplication
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem scaled_class {B : Base (M := M)} {n : ℕ} (a : Chart B n)
    (γ : Values.Gamma (M := M)) (hγ : GammaDefinableClosureAtBase B γ) :
    objectClass (scaled a γ hγ) = objectClass (RVMeasuredCharts.weightedUnit B γ hγ) * objectClass a :=
  (objectClass_iso (scaleProductIso a γ hγ)).symm.trans
    (objectClass_product (RVMeasuredCharts.weightedUnit B γ hγ) a)

def rayIso (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (t : RadiusLift B γ) :
    Iso (scaled (sharpChart (RVMeasuredSpecialClasses.rayChart B)) γ hγ) (aboveChart B γ hγ) where
  equiv := (RVScaledRays.rayIso B γ hγ t).equiv
  graph_definable := (RVScaledRays.rayIso B γ hγ t).graph_definable
  weight_eq := by
    intro u
    let v : Fin 1 → M := u.val
    change (1 * γ) * (∏ i : Fin 1, codeValue (u.val i)) =
      1 * (∏ i : Fin 1, codeValue (scale (raw t.point) u.val i))
    rw [Fin.prod_univ_one, Fin.prod_univ_one, one_mul, one_mul]
    change γ * codeValue (v 0) = codeValue (iRVMul (raw t.point) (v 0))
    rw [codeValue_mul _ _ ⟨raw_rv t.point, raw_ne_zero t.point⟩ ((show Proper v from u.property.1) 0),
      codeValue_raw, t.value_eq]

theorem above_class (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (t : RadiusLift B γ) :
    objectClass (aboveChart B γ hγ) =
      objectClass (RVMeasuredCharts.weightedUnit B γ hγ) *
        objectClass (sharpChart (RVMeasuredSpecialClasses.rayChart B)) :=
  (objectClass_iso (rayIso B γ hγ t)).symm.trans (scaled_class _ γ hγ)

def pointIso (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (t : RadiusLift B γ) :
    Iso (scaled (pointChart B oneCode (oneCode_definable B)) γ hγ)
      (pointChart B t.point t.definable) where
  equiv := (RESOrdinaryPoints.pointIso B oneCode t.point (oneCode_definable B) t.definable).equiv
  graph_definable := (RESOrdinaryPoints.pointIso B oneCode t.point (oneCode_definable B) t.definable).graph_definable
  weight_eq := by
    intro u
    let v : (pointChart B oneCode (oneCode_definable B)).domain := u
    let w := (RESOrdinaryPoints.pointIso B oneCode t.point (oneCode_definable B) t.definable).equiv v
    calc
      (scaled (pointChart B oneCode (oneCode_definable B)) γ hγ).correctedWeight u.val =
          (pointChart B oneCode (oneCode_definable B)).correctedWeight v.val * γ :=
        scaled_weight _ γ hγ v.val
      _ = 1 * γ := congrArg (fun x => x * γ)
        ((pointChart_weight B oneCode (oneCode_definable B) v).trans oneCode_value)
      _ = γ := one_mul γ
      _ = value t.point := t.value_eq.symm
      _ = (pointChart B t.point t.definable).correctedWeight w.val :=
        (pointChart_weight B t.point t.definable w).symm

theorem point_class (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (t : RadiusLift B γ) :
    objectClass (pointChart B t.point t.definable) =
      objectClass (RVMeasuredCharts.weightedUnit B γ hγ) *
        objectClass (pointChart B oneCode (oneCode_definable B)) :=
  (objectClass_iso (pointIso B γ hγ t)).symm.trans (scaled_class _ γ hγ)

end DiamondIntegral.Section4.RVMeasuredScaling
