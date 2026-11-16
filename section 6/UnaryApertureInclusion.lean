import «section 6».RelativeApertureBoundedGraphs
import «section 6».UnaryRelativeApertureBoundedGraphs
import «section 6».RelativeApertureChains
import «section 6».UnaryRelativeApertureChains

/-! The proved unary variable class embeds in the precise arbitrary-arity
bounded variable class. Named bounds come from its constructed RV graph;
no extra coefficient or domain is adjoined. Whole point maps agree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
namespace UnaryRelativeApertureData

def relativeDataWithBound (D : UnaryRelativeApertureData A) (Δ : Gamma M)
    (hΔ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}}) (hΔ1 : 1≤Δ)
    (hUpper : ∀ p : focusActive A D.focusData.activeTags,
      vfValue ((D.endpointMap p).val 0)≤Δ.val*vfValue (p.val.1 0)) : RelativeApertureData (G := G) A where
  coordinate := 0
  activeTags := D.focusData.activeTags
  focus := fun _ u => D.focusData.focus u
  focusMap := D.focusMap
  focusMap_eq := D.focusData.focusMap_eq
  sourceProper := D.focusData.sourceProper
  sourceDoublyBounded := D.focusData.sourceDoublyBounded
  tagged := D.focusData.tagged
  continuous _ _ := continuous_const.continuousOn
  focusRV := D.focusData.focusRV
  endpoint := fun _ u => D.endpoint u
  endpointMap := D.endpointMap
  endpointMap_eq := D.endpointMap_eq
  endpoint_continuous _ _ := continuous_const.continuousOn
  endpoint_nonzero := D.endpoint_nonzero
  endpoint_nonnegative := D.endpoint_nonnegative
  endpoint_RV_constant p q he := by rw [D.endpointMap_eq,D.endpointMap_eq,he]
  apertureBound := Δ
  apertureBound_nonnegative := hΔ1
  apertureBound_named := hΔ
  endpoint_upper_bound := hUpper
  covariance u hu := by
    refine ⟨D.radius u,(fun _ => D.radius u),D.radius_definable u,(fun _ => D.radius_definable u),?_,?_,?_⟩
    · simpa only [ite_self] using D.invariant u
    · intro a ha b hb hab
      simpa only [sub_self,valueHom_eq_value] using gamma_lt_value_zero (D.radius u)
    · intro a ha
      exact D.radius_le_endpoint ⟨(a,u),ha,hu⟩

theorem relativeDataWithBound_point (D : UnaryRelativeApertureData A) (Δ : Gamma M)
    (hΔ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}}) (hΔ1 : 1≤Δ)
    (hUpper : ∀ p : focusActive A D.focusData.activeTags,
      vfValue ((D.endpointMap p).val 0)≤Δ.val*vfValue (p.val.1 0)) (p : Mixed M 1 r) :
    (D.relativeDataWithBound (G := G) Δ hΔ hΔ1 hUpper).point p=D.point p := rfl

theorem exists_relativeData (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    ∃ E : RelativeApertureData (G := G) A,∀ p : Mixed M 1 r,E.point p=D.point p := by
  obtain ⟨Δ,hΔ,hΔ1,hBound⟩ := rv_positive_gamma_map_named_bound hc h00 linear hκ hs hsmall hΓ
    (rvTagQuotient (focusActive A D.focusData.activeTags)) D.apertureLabelDomain_bounded
    D.apertureGammaLabelMap D.apertureGammaLabelMap_nonnegative
  have hUpper (p : focusActive A D.focusData.activeTags) :
      vfValue ((D.endpointMap p).val 0)≤Δ.val*vfValue (p.val.1 0) := by
    have h := hBound (rvTagQuotientMap (focusActive A D.focusData.activeTags) p)
    rw [D.apertureGammaLabelMap_at] at h
    have hMul : finiteValue (D.endpoint p.val.2) (D.endpoint_nonzero p)≤
        Δ*finiteValue (D.focusData.focus p.val.2) (D.focus_nonzero p) := div_le_iff_le_mul.mp h
    have hValue : (finiteValue (D.endpoint p.val.2) (D.endpoint_nonzero p)).val≤
        (Δ*finiteValue (D.focusData.focus p.val.2) (D.focus_nonzero p)).val := hMul
    rw [Values.gamma_val_mul] at hValue
    have hFocus : vfValue (D.focusData.focus p.val.2)=vfValue (p.val.1 0) :=
      congrArg Values.vrv (D.focusData.focusRV p.val p.property.1 p.property.2)
    rw [D.endpointMap_eq,← hFocus]
    exact hValue
  exact ⟨D.relativeDataWithBound Δ hΔ hΔ1 hUpper,D.relativeDataWithBound_point Δ hΔ hΔ1 hUpper⟩

end UnaryRelativeApertureData

include G in
 theorem UnaryRelativeApertureChain.toRelativeChain
    {B : DefSet (rawMixedSpace (M := M) 1 s) S} {f : Map A B}
    (h : UnaryRelativeApertureChain (G := G) A B f)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    RelativeApertureChain (G := G) A B f := by
  induction h with
  | original h => exact .original h
  | relative A D =>
      obtain ⟨E,hPoint⟩ := D.exists_relativeData (G := G) hc h00 linear hκ hs hsmall hΓ
      have hImage : E.map.image=D.map.image := by
        apply defSet_eq_of_carrier_eq
        rw [E.image_carrier,D.image_carrier]
        ext z
        constructor
        · rintro ⟨p,hp,he⟩
          exact ⟨p,hp,(hPoint p).symm.trans he⟩
        · rintro ⟨p,hp,he⟩
          exact ⟨p,hp,(hPoint p).trans he⟩
      exact RelativeApertureChain.changeTarget hImage (fun p => hPoint p.val) (.relative A E)
  | comp hf hg ihf ihg => exact .comp ihf ihg

end DiamondIntegral.Section6
