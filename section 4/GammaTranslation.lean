import «section 4».GammaTupleMaps
import «section 4».GammaObjectRelations
import «section 4».GammaNamesSubgroup
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! Actual Gamma translation invariance for both Euler theories and for
corrected volume profiles, with compensated target volumes. The translation
constants are Gamma-definable over the original base; RV lifts are not
needed for these numerical/function-valued identities. This does not
assume or prove a tensor-kernel generation theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaTranslation
open GammaOrderLogic GammaDefinableMaps GammaTupleMaps GammaBijectiveRelations
open GammaIndicators GammaIteratedIntegral GammaWeightProfiles GammaMeasuredProfileInvariance

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def shift {n : ℕ} (a z : Fin n → Values.Gamma (M := M)) : Fin n → Values.Gamma (M := M) :=
  fun i => a i * z i

theorem shift_coordinates (B : Base (M := M)) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (i : Fin n) : MapDefinable B (fun z => shift a z i) :=
  mul_definable B _ _ (constant_definable B (a i) (ha i)) (projection_definable B i)

def translated {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (I : Set (Fin n → Values.Gamma (M := M))) : Set (Fin n → Values.Gamma (M := M)) := shift a '' I

theorem translated_definable (B : Base (M := M)) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) :
    GammaDefinable B (translated a I) := image_definable B I hI (shift a) (shift_coordinates B a ha)

theorem shift_bijOn {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (I : Set (Fin n → Values.Gamma (M := M))) : Set.BijOn (shift a) I (translated a I) := by
  refine ⟨fun x hx => ⟨x, hx, rfl⟩, ?_, ?_⟩
  · intro x _ y _ he
    exact funext (fun i => mul_left_cancel (congrFun he i))
  · rintro y ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩

theorem integral_translated (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) :
    integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B I hI) =
      integrateAll h00 hκ hs B hr hγ k n
        (indicatorFamily B (translated a I) (translated_definable B a ha I hI)) :=
  integrateAll_bijOn h00 linear hκ hs B hr hγ hΓ k n n I hI (translated a I)
    (translated_definable B a ha I hI) (shift a)
    (graph_definable B I hI (shift a) (shift_coordinates B a ha)) (shift_bijOn a I)

def compensatedVolume {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (z : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  μ (shift (fun i => (a i)⁻¹) z) / ∏ i, a i

theorem compensatedVolume_definable (B : Base (M := M)) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    MapDefinable B (compensatedVolume a μ) := by
  have hai (i : Fin n) : GammaDefinableClosureAtBase B ((a i)⁻¹) :=
    GammaNamesSubgroup.inverse_definable_base B (a i) (ha i)
  have hm : MapDefinable B (fun z : Fin n → Values.Gamma (M := M) =>
      μ (shift (fun i => (a i)⁻¹) z)) :=
    compose_definable B μ hμ (shift (fun i => (a i)⁻¹))
      (shift_coordinates B (fun i => (a i)⁻¹) hai)
  have hpname : (∏ i, a i) ∈ GammaNamesSubgroup.namesSubgroup B :=
    (GammaNamesSubgroup.namesSubgroup B).toSubmonoid.prod_mem (fun i _ => ha i)
  have hp : MapDefinable B (fun _ : Fin n → Values.Gamma (M := M) => ∏ i, a i) :=
    constant_definable B (∏ i, a i) hpname
  have hprod : MapDefinable B (fun z : Fin n → Values.Gamma (M := M) =>
      μ (shift (fun i => (a i)⁻¹) z) * (∏ i, a i)⁻¹) :=
    mul_definable B (fun z => μ (shift (fun i => (a i)⁻¹) z)) (fun _ => (∏ i, a i)⁻¹)
      hm (inverse_definable B (fun _ : Fin n → Values.Gamma (M := M) => ∏ i, a i) hp)
  have he : compensatedVolume a μ = (fun z : Fin n → Values.Gamma (M := M) =>
      μ (shift (fun i => (a i)⁻¹) z) * (∏ i, a i)⁻¹) := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he]
  exact hprod

theorem compensated_volume_eq {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (z : Fin n → Values.Gamma (M := M)) :
    μ z = compensatedVolume a μ (shift a z) * (∏ i, shift a z i) / (∏ i, z i) := by
  have hi : shift (fun i => (a i)⁻¹) (shift a z) = z := by
    funext i
    simp [shift]
  have hp : (∏ i, shift a z i) = (∏ i, a i) * ∏ i, z i := Finset.prod_mul_distrib
  rw [compensatedVolume, hi, hp]
  simp [div_eq_mul_inv, mul_assoc]

theorem profile_translated (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    profile h00 hκ hs B hr hγ k I hI μ hμ =
      profile h00 hκ hs B hr hγ k (translated a I) (translated_definable B a ha I hI)
        (compensatedVolume a μ) (compensatedVolume_definable B a ha μ hμ) :=
  profile_volume_bijOn h00 linear hκ hs B hr hγ hΓ k n n I hI
    (translated a I) (translated_definable B a ha I hI)
    μ hμ (compensatedVolume a μ) (compensatedVolume_definable B a ha μ hμ)
    (shift a) (graph_definable B I hI (shift a) (shift_coordinates B a ha)) (shift_bijOn a I)
    (fun u _ => compensated_volume_eq a μ u)

end DiamondIntegral.Section4.GammaTranslation
