import «section 6».UnaryFocusRadiusFloor
import «section 6».UnaryOffsetCoreFibres
import «section 6».NamedFiniteVFBounds

/-! Boundary translations can be performed on the whole ambient source.
Their own permitted apertures can be chosen small enough to miss every
selected core, while the full ambient RV-pullback is preserved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_ambient_boundary_component (F : UnaryFocusData A)
    (d : (Fin r → RVInfinity M) → VF M)
    (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hSmall : ∀ p ∈ A.carrier,p.2 ∈ F.activeTags.carrier → vfValue (F.focus p.2) < vfValue (d p.2))
    (hRV : IsRVPullback A.carrier)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    ∃ E : CentripetalData (G := G) A,E.coordinate=0 ∧ E.activeTags=F.activeTags ∧
      (∀ x u,E.focus x u=F.focus u-d u) ∧
      (∀ p ∈ (F.offsetCoreDomain dMap).carrier,E.core p=false) ∧ IsRVPullback E.map.image.carrier := by
  have hFinite := scalarFocusImage_finite hc hs hsmall dMap (fun p q he =>
    (hdMap p).trans ((congrArg d he).trans (hdMap q).symm))
  have hNZ : ∀ a ∈ scalarFocusImage dMap,a ≠ 0 := by
    rintro a ⟨p,rfl⟩
    change (dMap p).val 0 ≠ 0
    rw [hdMap]
    exact hd p.val.2 p.property.2
  obtain ⟨t,ht0,htDef,htPos,htAbove⟩ := exists_named_vf_above_finite_family h00 hc hv V hV hVS hSV hnt
    (scalarFocusImage dMap) (scalarFocusImage_definable dMap) hFinite hNZ
  let D := F.boundaryFocusData d dMap hdMap hSmall
  obtain ⟨E,hCoord,hActive,hFocus,hMap,hAperture⟩ := D.exists_centripetal_data_above_radius
    (finiteValue t ht0) (finiteValue_named t ht0 htDef) h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
  have hActive' : E.activeTags=F.activeTags := hActive
  have hFocus' : ∀ x u,E.focus x u=F.focus u-d u := hFocus
  refine ⟨E,hCoord,hActive',hFocus',?_,E.unary_image_rvPullback hRV⟩
  intro p hp
  obtain ⟨hpA,hu,hClose⟩ := (F.mem_offsetCoreDomain dMap d hdMap p).mp hp
  have hExt : E.extendedFocus p=F.focus p.2-d p.2 := by
    rw [E.extendedFocus_active hpA (hActive'.symm ▸ hu),hFocus']
  have hBound : vfValue (d p.2) < vfValue (E.coefficient*(F.focus p.2-d p.2)) := by
    have hdImg : d p.2 ∈ scalarFocusImage dMap := ⟨⟨p,hpA,hu⟩,hdMap _⟩
    have hFocusImg : F.focus p.2-d p.2 ∈ scalarFocusImage D.focusMap :=
      ⟨⟨p,hpA,hu⟩,D.focusMap_eq _⟩
    exact (htAbove _ hdImg).trans (hAperture _ hFocusImg)
  have hDisc : p.1 0 ∈ centeredGammaDisc (F.focus p.2) (finiteValue (d p.2) (hd p.2 hu)) :=
    (mem_centeredGammaDisc _ _ _).mpr hClose
  have hLead : rv M (p.1 0-(F.focus p.2-d p.2))=rv M (d p.2) := by
    have hImage := Set.mem_image_of_mem (fun x : VF M => x-(F.focus p.2-d p.2)) hDisc
    rwa [centered_disc_boundary_translation_image] at hImage
  have hVal : vfValue (p.1 0-(F.focus p.2-d p.2))=vfValue (d p.2) := congrArg Values.vrv hLead
  change decide (vfValue (E.coefficient*E.extendedFocus p) < vfValue (p.1 E.coordinate-E.extendedFocus p))=false
  rw [hCoord,hExt,hVal]
  exact decide_eq_false (not_lt_of_gt hBound)

end DiamondIntegral.Section6.UnaryFocusData
