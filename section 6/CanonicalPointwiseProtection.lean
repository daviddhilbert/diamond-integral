import «section 6».CanonicalPointwiseFocusData

/-! Canonical finite metadata retain the pointwise source-invariance
test of every protected piece with the same complementary radius.
These are the exact conditions included in component-template promotion. -/

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

theorem CentripetalData.exists_pointwise_protected_source_data
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
      ∀ i,∀ p : focusActive (P i) D.activeTags,∀ b : Fin n → VF M,
        (∀ j,(if j=D.coordinate then vfValue
          (W.coefficient*(D.focusMap ⟨p.val,(hCompat i).subset p.property.1,p.property.2⟩).val 0)
            else W.radius.val)<vfValue (p.val.1 j-b j)) → (b,p.val.2) ∈ (P i).carrier := by
  obtain ⟨C,hCoeff,hRadius,hPoint,hInvariant,hPieces⟩ := D.exists_canonical_protected_focus_graphs_with_invariants
    h00 hc linear hκ hs hv hsmall hΓ hARV P E hCompat
  have hCut (p : focusActive A D.activeTags) :
      (C.activeRadius p.val.2).val=vfValue (C.coefficient*(D.focusMap p).val 0) := by
    rw [hRadius,hCoeff,D.canonical_aperture_value p.val p.property.1 p.property.2,
      D.extendedFocus_active p.property.1 p.property.2,D.focusMap_eq p]
  let W := C.toPointwise hCut
  refine ⟨W,hCoeff,hPoint,?_⟩
  intro i p b hab
  change (∀ j,(if j=D.coordinate then vfValue
    (C.coefficient*(D.focusMap ⟨p.val,(hCompat i).subset p.property.1,p.property.2⟩).val 0)
      else C.complementaryRadius.val)<vfValue (p.val.1 j-b j)) at hab
  apply (hInvariant i p.val.2 p.property.2 p.val.1 b ?_).mp p.property.1
  intro j
  have hRate := hCut ⟨p.val,(hCompat i).subset p.property.1,p.property.2⟩
  by_cases hj : j=D.coordinate
  · simpa only [if_pos hj,hRate] using hab j
  · simpa only [if_neg hj] using hab j

end DiamondIntegral.Section6
