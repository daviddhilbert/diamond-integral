import «section 6».FullFocusErasedCovariance
import «section 6».FullFocusRestrictions
import «section 6».ContinuousFocusRealization

/-! Every complete continuous focus graph on a pullback ambient
constructs an actual permitted component in its specified coordinate,
with a common named coefficient protecting every finite proper subfamily. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem FullFocusGraphData.exists_protected_component
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (F : FullFocusGraphData (G := G) A) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier) :
    ∃ D : CentripetalData (G := G) A,D.coordinate=F.coordinate ∧ D.activeTags=F.activeTags ∧
      (∀ x : focusActive A F.activeTags,D.extendedFocus x.val=(F.map x).val 0) ∧
        ∀ i,∃ E : CentripetalData (G := G) (P i),ApertureRestrictionData D E := by
  let H : Fin (k+1) → Set (Mixed M n r) := Fin.cons A.carrier (fun i => (P i).carrier)
  have hH : ∀ i,ProperInvariant S (H i) := Fin.cases F.proper hP
  obtain ⟨γ,hγ,hγ1,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  obtain ⟨β₀,hβ₀,hCov⟩ := F.uniform_named_erased_covariance h00 hc linear hκ hs hv hsmall hΓ hARV γ hγ
  let β := max γ β₀
  have hβ := gamma_max_named γ β₀ hγ hβ₀
  have hInvAll (i) (u) : AlphaInvariant
      (fun j => if j=F.coordinate then γ else β) (vfFibre (H i) u) := by
    apply (hInv i u).larger_radius
    intro j
    split
    · exact le_rfl
    · exact le_max_left _ _
  obtain ⟨η,hLower⟩ := F.image_lowerBound
  obtain ⟨c,hc0,hcpos,hcdef,hcdom⟩ := exists_named_aperture_coefficient_of_lowerBound Valued.v hv hc h00
    V S hV hVS hSV hnt _ (scalarFocusImage_definable F.map) η hLower γ hγ
  let C : FullFocusCovarianceData F := {
    coefficient := c
    coefficient_nonzero := hc0
    coefficient_nonnegative := hcpos
    coefficient_definable := hcdef
    activeRadius := fun _ => γ
    activeNamed := fun _ _ => hγ.mono Set.subset_union_left
    complementaryRadius := β
    complementaryNamed := hβ
    invariant := fun u _ => hInvAll 0 u
    covariance := fun u hu a ha b hb hClose => hCov u hu a ha b hb
      (hClose.of_larger_radius (fun _ => le_max_right _ _))
    aperture := fun u hu a ha => (hcdom _ ⟨⟨(a,u),ha,hu⟩,rfl⟩).le }
  let D := C.component
  refine ⟨D,rfl,rfl,?_,fun i => ?_⟩
  · intro x
    exact (D.extendedFocus_active x.property.1 x.property.2).trans (F.focus_at x)
  · exact ⟨(C.restrict (hPA i) (hP i) (fun u _ => hInvAll i.succ u)).component,
      C.restrict_compatible (hPA i) (hP i) (fun u _ => hInvAll i.succ u)⟩

end DiamondIntegral.Section6
