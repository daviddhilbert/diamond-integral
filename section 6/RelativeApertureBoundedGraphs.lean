import «section 6».RelativeApertureRVGraphs
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
namespace DiamondIntegral.Section6.RelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def apertureGammaLabelMap (D : RelativeApertureData (G := G) A) :=
  (scalarRVGammaMap S).comp D.apertureRVLabelMap

theorem apertureRVLabelMap_nonzero (D : RelativeApertureData (G := G) A)
    (q : rvTagQuotient (focusActive A D.activeTags)) : (D.apertureRVLabelMap q).val 0≠0 := by
  obtain ⟨p,rfl⟩ := rvTagQuotientMap_surjective (focusActive A D.activeTags) q
  rw [D.apertureRVLabelMap_at]
  exact D.apertureRVPointMap_nonzero p

theorem apertureGammaLabelMap_value (D : RelativeApertureData (G := G) A)
    (q : rvTagQuotient (focusActive A D.activeTags)) :
    (gammaMapValue D.apertureGammaLabelMap q).val=Values.vrv ((D.apertureRVLabelMap q).val 0) :=
  scalarRVGammaMap_nonzero S (D.apertureRVLabelMap q)
    ((rv_nonzero_code_iff _).mpr (D.apertureRVLabelMap_nonzero q))

theorem apertureGammaLabelMap_at (D : RelativeApertureData (G := G) A) (p : focusActive A D.activeTags) :
    gammaMapValue D.apertureGammaLabelMap (rvTagQuotientMap (focusActive A D.activeTags) p)=
      finiteValue (((D.endpointMap p).val 0)) (D.endpointMap_nonzero p)/
        finiteValue (((D.focusMap p).val 0)) (D.focusMap_nonzero p) := by
  let b := ((D.endpointMap p).val 0)
  let a := ((D.focusMap p).val 0)
  have hb := D.endpointMap_nonzero p
  have ha := D.focusMap_nonzero p
  have hx : (rv M b).val≠iRVZero := (rv_nonzero_code_iff _).mpr ((RVOperations.rv_ne_zero _).mpr hb)
  have hy : (rv M a).val≠iRVZero := (rv_nonzero_code_iff _).mpr ((RVOperations.rv_ne_zero _).mpr ha)
  have hB : Values.gammaOf (rv M b) hx=finiteValue b hb := Subtype.ext rfl
  have hA : Values.gammaOf (rv M a) hy=finiteValue a ha := Subtype.ext rfl
  apply Subtype.ext
  rw [D.apertureGammaLabelMap_value,D.apertureRVLabelMap_at,D.apertureRVPointMap_value]
  have h := RVCoordinateOperation.value_gamma .divide (rv M b) (rv M a) hx hy
  simpa only [RVCoordinateOperation.value,RVCoordinateOperation.gammaValue,hB,hA] using h

theorem apertureGammaLabelMap_nonnegative (D : RelativeApertureData (G := G) A)
    (q : rvTagQuotient (focusActive A D.activeTags)) : 1≤gammaMapValue D.apertureGammaLabelMap q := by
  obtain ⟨p,rfl⟩ := rvTagQuotientMap_surjective (focusActive A D.activeTags) q
  rw [D.apertureGammaLabelMap_at]
  apply one_le_div'.mpr
  have h := D.endpoint_nonnegative p
  rw [← D.endpointMap_eq p,← D.focusMap_eq p] at h
  exact h

theorem apertureLabelDomain_bounded (D : RelativeApertureData (G := G) A) :
    RVSupportDoublyBounded (rvTagQuotient (focusActive A D.activeTags)).carrier :=
  rvTagQuotient_rvBounded _ (focusActive_properInvariant A D.sourceProper D.activeTags).rvBounded

theorem apertureGammaLabelMap_upper_bound (D : RelativeApertureData (G := G) A)
    (q : rvTagQuotient (focusActive A D.activeTags)) :
    gammaMapValue D.apertureGammaLabelMap q≤D.apertureBound := by
  obtain ⟨p,rfl⟩ := rvTagQuotientMap_surjective (focusActive A D.activeTags) q
  rw [D.apertureGammaLabelMap_at]
  apply div_le_iff_le_mul.mpr
  have h := D.endpoint_upper_bound p
  have hF : vfValue ((D.focusMap p).val 0)=vfValue (p.val.1 D.coordinate) := by
    rw [D.focusMap_eq]
    exact congrArg Values.vrv (D.focusRV p.val p.property.1 p.property.2)
  rw [← hF] at h
  change (finiteValue ((D.endpointMap p).val 0) (D.endpointMap_nonzero p)).val≤
    (D.apertureBound*finiteValue ((D.focusMap p).val 0) (D.focusMap_nonzero p)).val
  rw [Values.gamma_val_mul]
  exact h

theorem named_aperture_bounds (D : RelativeApertureData (G := G) A) :
    S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {D.apertureBound}} ∧
      ∀ q : rvTagQuotient (focusActive A D.activeTags),
        (D.apertureRVLabelMap q).val 0≠0 ∧
        (1 : GammaInfinity M)≤Values.vrv ((D.apertureRVLabelMap q).val 0) ∧
        Values.vrv ((D.apertureRVLabelMap q).val 0)≤D.apertureBound.val := by
  refine ⟨D.apertureBound_named,fun q => ⟨D.apertureRVLabelMap_nonzero q,?_,?_⟩⟩
  · rw [← D.apertureGammaLabelMap_value q]
    exact D.apertureGammaLabelMap_nonnegative q
  · rw [← D.apertureGammaLabelMap_value q]
    exact D.apertureGammaLabelMap_upper_bound q

end DiamondIntegral.Section6.RelativeApertureData
