import «section 6».CanonicalProtectedFocusGraphs
import «section 6».PointwiseFocusCovariance

/-! Every actual synchronized component on a pullback ambient has
the finite-metadata pointwise form used in first-order templates. Its
actual map and all protected component restrictions are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem CentripetalData.exists_pointwise_protected_focus_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hCompat : ∀ i,ApertureRestrictionData D (E i)) :
    ∃ W : PointwiseFocusCovariance D.fullFocusGraph,W.coefficient=D.coefficient ∧
      (∀ p : Mixed M n r,(W.fullData hc).component.point p=D.point p) ∧
      ∀ i,∃ F : CentripetalData (G := G) (P i),ApertureRestrictionData (W.fullData hc).component F ∧
        ∀ p ∈ (P i).carrier,F.point p=(E i).point p := by
  obtain ⟨C,hCoeff,hRadius,hPoint,hPieces⟩ := D.exists_canonical_protected_focus_graphs
    h00 hc linear hκ hs hv hsmall hΓ hARV P E hCompat
  have hCut (p : focusActive A D.activeTags) :
      (C.activeRadius p.val.2).val=vfValue (C.coefficient*(D.focusMap p).val 0) := by
    rw [hRadius,hCoeff,D.canonical_aperture_value p.val p.property.1 p.property.2,
      D.extendedFocus_active p.property.1 p.property.2,D.focusMap_eq p]
  let W := C.toPointwise hCut
  refine ⟨W,hCoeff,hPoint,?_⟩
  intro i
  obtain ⟨F,hF,hMap⟩ := hPieces i
  exact ⟨F,⟨hF.subset,hF.coordinate,hF.coefficient,hF.focus⟩,hMap⟩

end DiamondIntegral.Section6
