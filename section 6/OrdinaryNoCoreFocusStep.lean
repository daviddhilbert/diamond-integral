import «section 6».OrdinaryUnaryFocusPort
import «section 6».OrdinaryFocusExceptions
import «section 6».AbsentFocusCentripetal

/-! The ordinary chain's actual exceptional set discharges the
focus-absence premise on every current proper source, including those
with extra retained labels. Thus a permitted finite-aperture component
is constructed on the entire unexceptional source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q t : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : OrdinaryUnaryFocusFrame hc A hA q) {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 t}
variable (T : SpecialTransformations.Section5.Chain R 1 D.etaImage B)

theorem focus_absent_of_no_zero_sources
    (hNo : ∀ p : X.source,(X.oldMap p).val ∉
      ordinaryChainZeroSources (.cons (.centripetal D) T)) :
    ∀ p ∈ X.source.carrier,p.2 ∈ (X.activeTags D hD).carrier →
      ((fun _ : Fin 1 => (X.focusData D hD).focus p.2),p.2) ∉ X.source.carrier := by
  intro p hp hu hFocus
  let z : X.source := ⟨((fun _ : Fin 1 => (X.focusData D hD).focus p.2),p.2),hFocus⟩
  let a : X.source := ⟨p,hp⟩
  have hLocusA := (X.activeTags_at D hD a).mp hu
  have hLocusZ := (X.activeTags_at D hD z).mp hu
  have hCenter : D.center (X.oldMap z).val=D.center (X.oldMap a).val := by
    apply OriginalBaseOrdinaryFocus.center_same_labels D _ _
      ⟨(X.oldMap z).property,hLocusZ⟩ ⟨(X.oldMap a).property,hLocusA⟩
    rw [X.point z,X.point a]
  have hFocusZ : (X.oldMap z).val.1 0=D.center (X.oldMap z).val := by
    calc
      (X.oldMap z).val.1 0=(X.focusData D hD).focus p.2 := by rw [X.point z]
      _=D.center (X.oldMap a).val := X.focusData_value D hD a hu
      _=D.center (X.oldMap z).val := hCenter.symm
  exact hNo z (ordinary_focus_event_mem_zeroSources D T (X.oldMap z) hLocusZ hFocusZ)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_component_of_no_zero_sources
    (h00 : M ⊨ Axioms.ACVF00) (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hNo : ∀ p : X.source,(X.oldMap p).val ∉
      ordinaryChainZeroSources (.cons (.centripetal D) T)) :
    ∃ E : CentripetalData (G := G) X.source,E.coordinate=0 ∧ E.activeTags=X.activeTags D hD ∧
      (∀ x u,E.focus x u=(X.focusData D hD).focus u) ∧
      ∀ p ∈ X.source.carrier,E.core p=false :=
  (X.focusData D hD).exists_centripetal_without_core h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    (X.focus_absent_of_no_zero_sources D hD T hNo)

end DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
