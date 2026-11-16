import «section 6».UnaryRelativeApertureRVGraphs
import «section 6».RVPositiveGammaMapBounds
import «section 6».UnaryRVGammaVolumes
import «section 6».RVCoordinateArithmeticBounds

/-! The actual relative aperture graph has nonzero values and one
original-base named bound. Its Gamma value is exactly the endpoint
value divided by the focus value. This connects the auxiliary unary
primitive to the bounded variable-aperture data proposed for 6.11. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def apertureGammaLabelMap (D : UnaryRelativeApertureData A) :=
  (scalarRVGammaMap S).comp D.apertureRVLabelMap

theorem apertureRVLabelMap_nonzero (D : UnaryRelativeApertureData A)
    (q : rvTagQuotient (focusActive A D.focusData.activeTags)) : (D.apertureRVLabelMap q).val 0≠0 := by
  obtain ⟨p,rfl⟩ := rvTagQuotientMap_surjective (focusActive A D.focusData.activeTags) q
  rw [D.apertureRVLabelMap_at]
  exact D.apertureRVPointMap_nonzero p

theorem apertureGammaLabelMap_value (D : UnaryRelativeApertureData A)
    (q : rvTagQuotient (focusActive A D.focusData.activeTags)) :
    (gammaMapValue D.apertureGammaLabelMap q).val=Values.vrv ((D.apertureRVLabelMap q).val 0) :=
  scalarRVGammaMap_nonzero S (D.apertureRVLabelMap q)
    ((rv_nonzero_code_iff _).mpr (D.apertureRVLabelMap_nonzero q))

theorem apertureGammaLabelMap_at (D : UnaryRelativeApertureData A) (p : focusActive A D.focusData.activeTags) :
    gammaMapValue D.apertureGammaLabelMap (rvTagQuotientMap (focusActive A D.focusData.activeTags) p)=
      finiteValue (D.endpoint p.val.2) (D.endpoint_nonzero p)/
        finiteValue (D.focusData.focus p.val.2) (D.focus_nonzero p) := by
  let b := D.endpoint p.val.2
  let a := D.focusData.focus p.val.2
  have hb := D.endpoint_nonzero p
  have ha := D.focus_nonzero p
  have hx : (rv M b).val≠iRVZero := (rv_nonzero_code_iff _).mpr ((RVOperations.rv_ne_zero _).mpr hb)
  have hy : (rv M a).val≠iRVZero := (rv_nonzero_code_iff _).mpr ((RVOperations.rv_ne_zero _).mpr ha)
  have hB : Values.gammaOf (rv M b) hx=finiteValue b hb := Subtype.ext rfl
  have hA : Values.gammaOf (rv M a) hy=finiteValue a ha := Subtype.ext rfl
  apply Subtype.ext
  rw [D.apertureGammaLabelMap_value,D.apertureRVLabelMap_at,D.apertureRVPointMap_value]
  have h := RVCoordinateOperation.value_gamma .divide (rv M b) (rv M a) hx hy
  simpa only [RVCoordinateOperation.value,RVCoordinateOperation.gammaValue,hB,hA] using h

theorem apertureGammaLabelMap_nonnegative (D : UnaryRelativeApertureData A)
    (q : rvTagQuotient (focusActive A D.focusData.activeTags)) : 1≤gammaMapValue D.apertureGammaLabelMap q := by
  obtain ⟨p,rfl⟩ := rvTagQuotientMap_surjective (focusActive A D.focusData.activeTags) q
  rw [D.apertureGammaLabelMap_at]
  apply one_le_div'.mpr
  exact D.endpoint_nonnegative p

theorem apertureLabelDomain_bounded (D : UnaryRelativeApertureData A) :
    RVSupportDoublyBounded (rvTagQuotient (focusActive A D.focusData.activeTags)).carrier :=
  rvTagQuotient_rvBounded _ (focusActive_properInvariant A D.focusData.sourceProper D.focusData.activeTags).rvBounded

theorem exists_named_aperture_bound (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    ∃ Δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}} ∧ 1≤Δ ∧
      ∀ q : rvTagQuotient (focusActive A D.focusData.activeTags),
        (D.apertureRVLabelMap q).val 0≠0 ∧
        (1 : GammaInfinity M)≤Values.vrv ((D.apertureRVLabelMap q).val 0) ∧
        Values.vrv ((D.apertureRVLabelMap q).val 0)≤Δ.val := by
  obtain ⟨Δ,hΔ,hΔ1,hBound⟩ := rv_positive_gamma_map_named_bound hc h00 linear hκ hs hsmall hΓ
    (rvTagQuotient (focusActive A D.focusData.activeTags)) D.apertureLabelDomain_bounded
    D.apertureGammaLabelMap D.apertureGammaLabelMap_nonnegative
  refine ⟨Δ,hΔ,hΔ1,fun q => ⟨D.apertureRVLabelMap_nonzero q,?_,?_⟩⟩
  · rw [← D.apertureGammaLabelMap_value q]
    exact D.apertureGammaLabelMap_nonnegative q
  · rw [← D.apertureGammaLabelMap_value q]
    exact hBound q

end DiamondIntegral.Section6.UnaryRelativeApertureData
