import «section 5».GammaCylindricalFamilyEuler
import «section 5».GammaSingletonGraphEuler

/-! Cylindrical fibre integration with the fibre in the last coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open GammaOrderLogic GammaIntegerFamilies GammaIteratedIntegral GammaIndicators GammaCoordinatePullback
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gamma_last_cylinder_euler
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind) (shape : CylinderFibreKind)
    (I : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hproj : ∀ η γ, Fin.snoc η γ ∈ K.carrier → η ∈ I.carrier)
    (hrow : ∀ η ∈ I.carrier, shape.Describes (fun γ : Values.Gamma (M := M) => Fin.snoc η γ ∈ K.carrier)) :
    integrateAll h00 hκ hs B hr hγ kind (n+1)
      (indicatorFamily B K.carrier (Section3GammaChartBridge.chart K).support_definable) =
    shape.eulerFactor kind * integrateAll h00 hκ hs B hr hγ kind n
      (indicatorFamily B I.carrier (Section3GammaChartBridge.chart I).support_definable) := by
  let hI := (Section3GammaChartBridge.chart I).support_definable
  let hK := (Section3GammaChartBridge.chart K).support_definable
  let R : Set (Fin (n+1) → Values.Gamma (M := M)) := {z | z ∘ finRotate (n+1) ∈ K.carrier}
  have hR : GammaDefinable B R := by
    have hh := ((gammaGroundGammaPower_definable_iff K.carrier).mp K.definable).reindex (finRotate (n+1))
    exact (Section3GammaChartBridge.chart
      (⟨R, gammaGroundGammaPower_predicate_definable _ hh⟩ :
        GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))).support_definable
  have hrot (η : Fin n → Values.Gamma (M := M)) (γ : Values.Gamma (M := M)) :
      Fin.cons γ η ∘ finRotate (n+1) = Fin.snoc η γ := (Fin.snoc_eq_cons_rotate η γ).symm
  have hp : ∀ z ∈ R, Fin.tail z ∈ I.carrier := by
    intro z hz
    apply hproj (Fin.tail z) (z 0)
    change z ∘ finRotate (n+1) ∈ K.carrier at hz
    simpa only [← hrot, Fin.cons_self_tail] using hz
  have hf : ∀ η ∈ I.carrier, shape.Describes (fun γ => Fin.cons γ η ∈ R) := by
    intro η hη
    simpa only [R, Set.mem_ofPred_eq, hrot] using hrow η hη
  let f := indicatorFamily B K.carrier hK
  have he : pullback B (finRotate (n+1)) f = indicatorFamily B R hR := rfl
  have hperm := GammaFubiniPermutation.integrateAll_permutation h00 hκ hs B hr hγ kind
    linear hΓ (n+1) (finRotate (n+1)) f
  calc
    integrateAll h00 hκ hs B hr hγ kind (n+1) f =
        integrateAll h00 hκ hs B hr hγ kind (n+1) (indicatorFamily B R hR) := by
          rw [← he]; exact hperm.symm
    _ = _ := gamma_cylinder_integrateAll h00 hκ hs B hr hγ kind shape I.carrier hI R hR hp hf

end DiamondIntegral.Section5
