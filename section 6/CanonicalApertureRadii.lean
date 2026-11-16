import «section 6».FocusCutoffValueMaps

/-! Canonical active radii for arbitrary tagged components. The actual
cutoff is constant on each inhabited old-label fibre and has a complete
definable Gamma graph; no designated label coordinate is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def CentripetalData.canonicalActiveRadius (D : CentripetalData (G := G) A)
    (u : Fin r → RVInfinity M) : Gamma M :=
  if h : ∃ p : focusActive A D.activeTags,p.val.2=u then (D.cutoffGammaMap h.choose).val else 1

theorem CentripetalData.canonical_aperture_value (D : CentripetalData (G := G) A)
    (p : Mixed M n r) (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    (D.canonicalActiveRadius p.2).val=vfValue (D.coefficient*D.extendedFocus p) := by
  have h : ∃ q : focusActive A D.activeTags,q.val.2=p.2 := ⟨⟨p,hp,hu⟩,rfl⟩
  rw [canonicalActiveRadius,dite_eq_left h,D.cutoffGammaMap_value]
  have hEq : h.choose.val=(h.choose.val.1,p.2) := Prod.ext rfl h.choose_spec
  have hSource : (h.choose.val.1,p.2) ∈ A.carrier := hEq ▸ h.choose.property.1
  rw [hEq]
  exact D.cutoff_value_eq hu hSource hp

theorem CentripetalData.canonical_aperture_named
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : CentripetalData (G := G) A)
    (u : Fin r → RVInfinity M) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {D.canonicalActiveRadius u}} := by
  by_cases h : ∃ p : focusActive A D.activeTags,p.val.2=u
  · apply gamma_value_named_on_rv_fibre (focusActive A D.activeTags).carrier
      (gammaFormExtension D.cutoffGammaMap) (gammaFormExtension_graph_definable D.cutoffGammaMap)
      u (D.canonicalActiveRadius u) ⟨h.choose.val,h.choose.property,h.choose_spec⟩
    intro p hp hpu
    rw [gammaFormExtension_at D.cutoffGammaMap ⟨p,hp⟩]
    apply Subtype.ext
    rw [D.cutoffGammaMap_value,← D.canonical_aperture_value p hp.1 hp.2,hpu]
  · rw [canonicalActiveRadius,dite_eq_right h]
    exact gamma_one_named hc

theorem CentripetalData.source_invariant_at_canonical_aperture
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) :
    ∃ η : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {η}} ∧ 1 ≤ η ∧
      ∀ β : Gamma M,η ≤ β → ∀ u ∈ D.activeTags.carrier,
        AlphaInvariant (fun i => if i=D.coordinate then D.canonicalActiveRadius u else β)
          (vfFibre A.carrier u) := by
  obtain ⟨η,hη,hη1,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ D.sourceProper
  refine ⟨η,hη,hη1,?_⟩
  intro β hηβ u hu
  apply AlphaInvariant.combine_coordinate_radius η β _ D.coordinate (hInv u) hηβ
  intro a ha x hClose
  apply D.coordinate_cutoff_stable (a,u) ha hu x
  rw [← D.canonical_aperture_value (a,u) ha hu]
  exact hClose

end DiamondIntegral.Section6
