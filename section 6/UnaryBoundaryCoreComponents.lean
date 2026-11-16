import «section 6».UnaryBoundaryCoreImages

/-! If the actual focus graph misses the current source, a permitted
finite-aperture component has no contracted core there. It agrees with
the ordinary translation at every point, with one retained false tag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem UnaryFocusData.exists_boundary_core_component
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (D : UnaryFocusData A)
    (d : (Fin r → RVInfinity M) → VF M)
    (dMap : Map (focusActive A D.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hdMap : ∀ p : focusActive A D.activeTags,(dMap p).val 0=d p.val.2)
    (hd : ∀ u ∈ D.activeTags.carrier,d u ≠ 0)
    (hAll : ∀ p ∈ A.carrier,p.2 ∈ D.activeTags.carrier)
    (hSmall : ∀ p ∈ A.carrier,p.2 ∈ D.activeTags.carrier → vfValue (D.focus p.2) < vfValue (d p.2))
    (hDiscs : ∀ u (hu : u ∈ D.activeTags.carrier) (x : VF M),
      ((fun _ : Fin 1 => x),u) ∈ A.carrier ↔ x ∈ centeredGammaDisc (D.focus u) (finiteValue (d u) (hd u hu)))
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    ∃ E : CentripetalData (G := G) A,E.coordinate=0 ∧ E.activeTags=D.activeTags ∧
      (∀ x u,E.focus x u=D.focus u-d u) ∧
      (∀ p ∈ A.carrier,E.core p=false) ∧ IsRVPullback E.map.image.carrier := by
  let F := D.boundaryFocusData d dMap hdMap hSmall
  have hAbsent (p : Mixed M 1 r) (hp : p ∈ A.carrier) (hu : p.2 ∈ F.activeTags.carrier) :
      ((fun _ : Fin 1 => F.focus p.2),p.2) ∉ A.carrier := by
    intro hmem
    have hDisc := (hDiscs p.2 hu (D.focus p.2-d p.2)).mp hmem
    exact centered_disc_boundary_focus_absent (D.focus p.2) (d p.2) (hd p.2 hu) hDisc
  obtain ⟨E,hCoord,hActive,hFocus,hCore⟩ := F.exists_centripetal_without_core
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hAbsent
  have hActive' : E.activeTags=D.activeTags := hActive
  have hFocus' : ∀ x u,E.focus x u=D.focus u-d u := hFocus
  exact ⟨E,hCoord,hActive',hFocus',hCore,
    unary_boundary_component_image_rvPullback D d E hCoord hActive' hFocus' hCore hAll hd hDiscs⟩

end DiamondIntegral.Section6
