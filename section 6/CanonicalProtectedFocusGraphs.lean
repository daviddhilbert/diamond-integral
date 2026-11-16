import «section 6».CanonicalApertureRadii
import «section 6».FullFocusRestrictions

/-! Canonical complete focus data for every actual synchronized
component on a pullback ambient. The active cutoff is recovered from
the complete graph; one named complementary radius protects all pieces.
No extra RV tag or real parameter is introduced. -/

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

theorem CentripetalData.exists_canonical_protected_focus_graphs_with_invariants
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hCompat : ∀ i,ApertureRestrictionData D (E i)) :
    ∃ C : FullFocusCovarianceData D.fullFocusGraph,
      C.coefficient=D.coefficient ∧ C.activeRadius=D.canonicalActiveRadius ∧
      (∀ p : Mixed M n r,C.component.point p=D.point p) ∧
      (∀ i,∀ u ∈ D.activeTags.carrier,
        AlphaInvariant (fun j => if j=D.coordinate then C.activeRadius u else C.complementaryRadius)
          (vfFibre (P i).carrier u)) ∧
      ∀ i,∃ F : CentripetalData (G := G) (P i),ApertureRestrictionData C.component F ∧
        ∀ p ∈ (P i).carrier,F.point p=(E i).point p := by
  obtain ⟨ρ,hρ,hBound⟩ := D.aperture_values_named_upper_bound h00 hc linear hκ hs hv hsmall hΓ
  obtain ⟨η,hη,hη1,hAmbient⟩ := D.source_invariant_at_canonical_aperture h00 hc linear hκ hs hv hsmall hΓ
  obtain ⟨ξ,hξ,hξ1,hCov⟩ := D.uniform_named_erased_covariance h00 hc linear hκ hs hv hsmall hΓ hARV ρ hρ
  obtain ⟨ε,hε,hε1,hPiece⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    (fun i => (P i).carrier) (fun i => (E i).sourceProper)
  let β := max η (max ξ ε)
  have hβ := gamma_max_named η (max ξ ε) hη (gamma_max_named ξ ε hξ hε)
  have hηβ : η ≤ β := le_max_left _ _
  have hξβ : ξ ≤ β := (le_max_left _ _).trans (le_max_right _ _)
  have hεβ : ε ≤ β := (le_max_right _ _).trans (le_max_right _ _)
  have hPieceInv (i) (u) (hu : u ∈ D.activeTags.carrier) :
      AlphaInvariant (fun j => if j=D.coordinate then D.canonicalActiveRadius u else β)
        (vfFibre (P i).carrier u) := by
    apply AlphaInvariant.combine_coordinate_radius ε β _ D.coordinate (hPiece i u) hεβ
    intro a ha x hClose
    apply (hCompat i).coordinate_cutoff_stable (a,u) ha hu x
    rw [← D.canonical_aperture_value (a,u) ((hCompat i).subset ha) hu]
    exact hClose
  let C : FullFocusCovarianceData D.fullFocusGraph := {
    coefficient := D.coefficient
    coefficient_nonzero := D.coefficient_nonzero
    coefficient_nonnegative := D.coefficient_nonnegative
    coefficient_definable := D.coefficient_definable
    activeRadius := D.canonicalActiveRadius
    activeNamed := fun u _ => D.canonical_aperture_named hc u
    complementaryRadius := β
    complementaryNamed := hβ
    invariant := hAmbient β hηβ
    covariance := ?_
    aperture := ?_ }
  · refine ⟨C,rfl,rfl,(fun _ => rfl),hPieceInv,?_⟩
    intro i
    let F := (C.restrict (hCompat i).subset (E i).sourceProper (hPieceInv i)).component
    have hF : ApertureRestrictionData C.component F :=
      C.restrict_compatible (hCompat i).subset (E i).sourceProper (hPieceInv i)
    exact ⟨F,hF,fun p hp => (hF.point p hp).trans ((hCompat i).point p hp).symm⟩
  · intro u hu a ha b hb hab
    change (D.canonicalActiveRadius u).val <
      vfValue ((D.focusMap ⟨(a,u),ha,hu⟩).val 0-(D.focusMap ⟨(b,u),hb,hu⟩).val 0)
    rw [D.focusMap_eq ⟨(a,u),ha,hu⟩,D.focusMap_eq ⟨(b,u),hb,hu⟩]
    have hCut : (D.canonicalActiveRadius u).val ≤ ρ.val := by
      rw [D.canonical_aperture_value (a,u) ha hu]
      exact hBound (a,u) ha hu
    exact hCut.trans_lt (hCov u hu a ha b hb (hab.of_larger_radius (fun _ => hξβ)))
  · intro u hu a ha
    change (D.canonicalActiveRadius u).val ≤ vfValue (D.coefficient*(D.focusMap ⟨(a,u),ha,hu⟩).val 0)
    rw [D.canonical_aperture_value (a,u) ha hu,D.focusMap_eq ⟨(a,u),ha,hu⟩,
      D.extendedFocus_active ha hu]

theorem CentripetalData.exists_canonical_protected_focus_graphs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hCompat : ∀ i,ApertureRestrictionData D (E i)) :
    ∃ C : FullFocusCovarianceData D.fullFocusGraph,
      C.coefficient=D.coefficient ∧ C.activeRadius=D.canonicalActiveRadius ∧
      (∀ p : Mixed M n r,C.component.point p=D.point p) ∧
      ∀ i,∃ F : CentripetalData (G := G) (P i),ApertureRestrictionData C.component F ∧
        ∀ p ∈ (P i).carrier,F.point p=(E i).point p := by
  obtain ⟨C,hCoeff,hRadius,hPoint,hInvariant,hPieces⟩ := D.exists_canonical_protected_focus_graphs_with_invariants
    h00 hc linear hκ hs hv hsmall hΓ hARV P E hCompat
  exact ⟨C,hCoeff,hRadius,hPoint,hPieces⟩

end DiamondIntegral.Section6
