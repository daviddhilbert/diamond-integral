import «section 6».PairedRVFocusComponents

/-! The full carried unary focus has the same actual original-base
finite image as a subset of the old focus image. Its active labels are
the selected old labels; the extra VF coordinate is never a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def UnaryFocusData.carriedFocusData (D : UnaryFocusData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : CarriedRefinementFrame A) : RVFocusData X.bundle where
  coordinate := (0 : Fin 1).castSucc
  activeTags := selectedRVTagSet D.activeTags X.labels
  focus u := D.focus (u ∘ X.labels)
  focusMap := D.focusMap.comp
    ((refinedFocusProjection D.activeTags X.labels X.source_subset).comp
      (bundleFocusProjection X.base X.freeLabel (selectedRVTagSet D.activeTags X.labels)))
  focusMap_eq := fun p => D.focusMap_eq
    ⟨(Fin.init p.val.1,p.val.2 ∘ X.labels),X.source_subset _ p.property.1.1,p.property.2⟩
  sourceProper := rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper
  sourceDoublyBounded := rvCoordinateBundle_doublyBounded X.base X.freeLabel X.doublyBounded X.proper.rvBounded
  tagged := rvCoordinateBundle_tagged X.base X.freeLabel
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged)
  focusRV := fun p hp hu => D.focusRV (Fin.init p.1,p.2 ∘ X.labels) (X.source_subset _ hp.1) hu

theorem UnaryFocusData.carried_focusImage_subset (D : UnaryFocusData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : CarriedRefinementFrame A) :
    scalarFocusImage (D.carriedFocusData h00 hc hκ hs hv X).focusMap ⊆ scalarFocusImage D.focusMap := by
  rintro _ ⟨p,rfl⟩
  exact ⟨⟨(Fin.init p.val.1,p.val.2 ∘ X.labels),X.source_subset _ p.property.1.1,p.property.2⟩,rfl⟩

theorem RVFocusRealization.carried_point
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : UnaryFocusData A) (X : CarriedRefinementFrame A)
    (F : RVFocusRealization (G := G) D.toRVFocusData)
    (H : RVFocusRealization (G := G) (D.carriedFocusData h00 hc hκ hs hv X))
    (hCoeff : H.component.coefficient = F.component.coefficient)
    (p : Mixed M 2 X.arity) (hp : p ∈ X.bundle.carrier) :
    H.component.point p = (X.carriedComponent h00 hc hκ hs hv F.component).point p := by
  let E := X.carriedComponent h00 hc hκ hs hv F.component
  have hCoord : H.component.coordinate = E.coordinate := by
    change H.component.coordinate = F.component.coordinate.castSucc
    rw [F.coordinate]
    exact H.coordinate
  have hActive : H.component.activeTags = E.activeTags := by
    change H.component.activeTags = selectedRVTagSet F.component.activeTags X.labels
    rw [F.activeTags]
    exact H.activeTags
  have hFocus (x u) : H.component.focus x u = E.focus x u := by
    rw [H.focus]
    exact (F.focus (Fin.init x) (u ∘ X.labels)).symm
  have hExt : H.component.extendedFocus p = E.extendedFocus p := by
    by_cases hu : p.2 ∈ E.activeTags.carrier
    · rw [H.component.extendedFocus_active hp (hActive.symm ▸ hu),E.extendedFocus_active hp hu]
      rw [hFocus,hCoord]
    · rw [H.component.extendedFocus_inactive (hActive.symm ▸ hu),E.extendedFocus_inactive hu]
  have hCore : H.component.core p = E.core p := by
    simp only [CentripetalData.core,hCoord,hCoeff,hExt]
    rfl
  simp only [CentripetalData.point,hCoord,hCoeff,hExt,hCore]
  rfl

end DiamondIntegral.Section6
