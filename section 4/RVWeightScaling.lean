import «section 4».RVCoordinateMaps
import «section 4».RESWeightCharacter

/-! Multiplication by an actual degree-zero weighted RES unit scales the
partial Gamma volume form on every actual RES object. The identification
is an original-base definable measured RV isomorphism. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVWeightScaling
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties RVVolumeMaps
open RVCoordinateMaps FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def scaled {B : Base (M := M)} {k : ℕ} (a : Chart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : Chart B k where
  arity := a.arity
  domain := a.domain
  domain_definable := a.domain_definable
  coordinate := a.coordinate
  coordinate_definable := a.coordinate_definable
  coordinate_proper := a.coordinate_proper
  finite_fibres := a.finite_fibres
  volume := fun u => a.volume u * γ
  volume_definable := multiply_definable B a.domain a.domain_definable a.volume (fun _ => γ)
    a.volume_definable (constant_volume_definable B a.domain a.domain_definable γ hγ)

theorem scaled_weight {B : Base (M := M)} {k : ℕ} (a : Chart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (u : Fin a.arity → M) :
    (scaled a γ hγ).correctedWeight u = a.correctedWeight u * γ := by
  change (a.volume u * γ) * (∏ i, codeValue (a.coordinate u i)) = (a.volume u * ∏ i, codeValue (a.coordinate u i)) * γ
  ac_rfl

def scaledRES {B : Base (M := M)} {k : ℕ} (a : RESChart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : RESChart B k := ⟨scaled a.toChart γ hγ, a.finite_values⟩

def scaleProductIso {B : Base (M := M)} {k : ℕ} (a : Chart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : Iso (product (weightedUnit B γ hγ) a) (scaled a γ hγ) := by
  apply coordinateIso (product (weightedUnit B γ hγ) a) (scaled a γ hγ) (id : Fin a.arity → Fin a.arity)
  · refine ⟨(fun u hu => hu.2), ?_, ?_⟩
    · intro x _ y _ he
      exact he
    · intro y hy
      exact ⟨y, ⟨Set.mem_univ _, hy⟩, rfl⟩
  · intro u _
    calc
      (product (weightedUnit B γ hγ) a).correctedWeight u = γ * a.correctedWeight u :=
        (product_weight_join (weightedUnit B γ hγ) a (Fin.elim0 : Fin 0 → M) u).trans
          (congrArg (fun w => w * a.correctedWeight u) (weightedUnit_correctedWeight B γ hγ Fin.elim0))
      _ = a.correctedWeight u * γ := mul_comm _ _
      _ = (scaled a γ hγ).correctedWeight (u ∘ id) := (scaled_weight a γ hγ u).symm

theorem scaledRES_class {B : Base (M := M)} {k : ℕ} (a : RESChart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) :
    RESChartRing.objectClass (scaledRES a γ hγ) =
      RESChartRing.objectClass (weightedRESUnit B γ hγ) * RESChartRing.objectClass a :=
  (RESChartRing.objectClass_iso (scaleProductIso a.toChart γ hγ)).symm.trans
    (RESChartRing.objectClass_product (weightedRESUnit B γ hγ) a)

end DiamondIntegral.Section4.RVWeightScaling
