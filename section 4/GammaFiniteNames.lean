import «section 4».GammaTupleMaps
import «section 4».GammaWeightedCharts

/-! Every coordinate and partial weight of a point in a finite definable
Gamma chart is definable over the original base. These are Gamma names;
no definable RV lift of any such value is asserted. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteNames
open GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem scalar_image_definable (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f) :
    GammaDefinableOverBase B (f '' I) := by
  apply (unary_definable_iff B (f '' I)).mp
  have h := GammaTupleMaps.image_definable B I hI (fun z => ![f z]) (by
    intro i
    fin_cases i
    exact hf)
  convert h using 1
  ext z
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, ?_⟩
    funext i
    fin_cases i
    exact he
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, congrFun he 0⟩

theorem finite_value_definable (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hi : I.Finite)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f)
    (z : Fin n → Values.Gamma (M := M)) (hz : z ∈ I) : GammaDefinableClosureAtBase B (f z) :=
  (gamma_algebraic_iff_definable_base B (f z)).mp
    ⟨f '' I, scalar_image_definable B I hI f hf, hi.image f, z, hz, rfl⟩

theorem finite_coordinate_definable (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hi : I.Finite)
    (z : Fin n → Values.Gamma (M := M)) (hz : z ∈ I) (i : Fin n) : GammaDefinableClosureAtBase B (z i) :=
  finite_value_definable B I hI hi (fun u => u i) (projection_definable B i) z hz

theorem finite_chart_weight_definable {B : Base (M := M)} {n : ℕ}
    (a : GammaWeightedCharts.Chart B n) (ha : a.support.Finite)
    (z : Fin n → Values.Gamma (M := M)) (hz : z ∈ a.support) : GammaDefinableClosureAtBase B (a.volume z) := by
  have h := finite_value_definable B a.support a.support_definable ha a.normalizedVolume a.normalizedVolume_definable z hz
  rwa [a.normalizedVolume_on z hz] at h

end DiamondIntegral.Section4.GammaFiniteNames
