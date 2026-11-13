import «section 4».RESChartRing
import «section 4».GammaNamesSubgroup

/-! Actual degree-zero weighted RES units realize the definable-Gamma
weight character in the concrete measured RES chart ring. No RV lift of
a volume weight is required and no finite RV set is split into points. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESWeightCharacter
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties
open FiniteTupleBlocks GammaNamesSubgroup GammaDefinableEuler

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def weightedUnitProductIso (B : Base (M := M)) (γ δ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (hδ : GammaDefinableClosureAtBase B δ) :
    Iso (product (weightedUnit B γ hγ) (weightedUnit B δ hδ))
      (weightedUnit B (γ * δ) (GammaGroupNames.mul_definable_base B γ δ hγ hδ)) where
  equiv :=
    { toFun := fun _ => ⟨Fin.elim0, Set.mem_univ _⟩
      invFun := fun _ => ⟨Fin.elim0, ⟨Set.mem_univ _, Set.mem_univ _⟩⟩
      left_inv := fun _ => Subtype.ext (@Subsingleton.elim (Fin 0 → M) inferInstance _ _)
      right_inv := fun _ => Subtype.ext (@Subsingleton.elim (Fin 0 → M) inferInstance _ _) }
  graph_definable := by
    change DefinableOverBase B (fun _ : Fin 0 => .rv)
      {w | ∃ u : (product (weightedUnit B γ hγ) (weightedUnit B δ hδ)).domain,
        w = join 0 0 u.val Fin.elim0}
    have h := zero_tuple_definable B
    convert h using 1
    ext w
    constructor
    · exact fun _ => Set.mem_univ w
    · intro _
      exact ⟨⟨Fin.elim0, ⟨Set.mem_univ _, Set.mem_univ _⟩⟩, Subsingleton.elim _ _⟩
  weight_eq := by
    intro u
    have hu : u.val = join 0 0 (Fin.elim0 : Fin 0 → M) Fin.elim0 :=
      @Subsingleton.elim (Fin 0 → M) inferInstance _ _
    calc
      (product (weightedUnit B γ hγ) (weightedUnit B δ hδ)).correctedWeight u.val =
          (product (weightedUnit B γ hγ) (weightedUnit B δ hδ)).correctedWeight
            (join 0 0 (Fin.elim0 : Fin 0 → M) Fin.elim0) := congrArg _ hu
      _ = γ * δ := (product_weight_join (weightedUnit B γ hγ) (weightedUnit B δ hδ) Fin.elim0 Fin.elim0).trans
        (congrArg₂ (· * ·) (weightedUnit_correctedWeight B γ hγ Fin.elim0)
          (weightedUnit_correctedWeight B δ hδ Fin.elim0))
      _ = (weightedUnit B (γ * δ) (GammaGroupNames.mul_definable_base B γ δ hγ hδ)).correctedWeight Fin.elim0 :=
        (weightedUnit_correctedWeight B (γ * δ) _ Fin.elim0).symm

theorem weightedUnitClass_product (B : Base (M := M)) (γ δ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (hδ : GammaDefinableClosureAtBase B δ) :
    RESChartRing.objectClass (weightedRESUnit B (γ * δ) (GammaGroupNames.mul_definable_base B γ δ hγ hδ)) =
      RESChartRing.objectClass (weightedRESUnit B γ hγ) * RESChartRing.objectClass (weightedRESUnit B δ hδ) :=
  (RESChartRing.objectClass_iso (weightedUnitProductIso B γ δ hγ hδ)).symm.trans
    (RESChartRing.objectClass_product (weightedRESUnit B γ hγ) (weightedRESUnit B δ hδ))

def weightCharacter (B : Base (M := M)) : Multiplicative (additiveNames B) →* RESChartRing.Ring B where
  toFun a := RESChartRing.objectClass
    (weightedRESUnit B (toPaperGamma.symm (Multiplicative.toAdd a).val) (Multiplicative.toAdd a).property)
  map_one' := RESChartRing.objectClass_unit B
  map_mul' a b := weightedUnitClass_product B
    (toPaperGamma.symm (Multiplicative.toAdd a).val) (toPaperGamma.symm (Multiplicative.toAdd b).val)
    (Multiplicative.toAdd a).property (Multiplicative.toAdd b).property

theorem weightCharacter_value (B : Base (M := M)) (a : additiveNames B) :
    weightCharacter B (Multiplicative.ofAdd a) =
      RESChartRing.objectClass (weightedRESUnit B (toPaperGamma.symm a.val) a.property) := rfl

end DiamondIntegral.Section4.RESWeightCharacter
