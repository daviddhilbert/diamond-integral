import «section 6».FullFocusRestrictions

/-! A single complete focus graph and one complementary radius encode
an ambient component and all its permitted protected restrictions. -/

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

theorem CentripetalData.exists_normalized_protected_focus_graphs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier) (j : Fin r)
    (hTag : ∀ p ∈ A.carrier,rv M (p.1 D.coordinate)=p.2 j)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hCompat : ∀ i,ApertureRestrictionData D (E i)) :
    ∃ C : FullFocusCovarianceData D.fullFocusGraph,
      C.coefficient=D.coefficient ∧
      (∀ p : Mixed M n r,C.component.point p=D.point p) ∧
      ∀ i,∃ F : CentripetalData (G := G) (P i),ApertureRestrictionData C.component F ∧
        ∀ p ∈ (P i).carrier,F.point p=(E i).point p := by
  obtain ⟨W⟩ := exists_uniform_protected_covariance_data h00 hc linear hκ hs hv hsmall hΓ
    D hARV j hTag P E hCompat
  let C : FullFocusCovarianceData D.fullFocusGraph := {
    coefficient := D.coefficient
    coefficient_nonzero := D.coefficient_nonzero
    coefficient_nonnegative := D.coefficient_nonnegative
    coefficient_definable := D.coefficient_definable
    activeRadius := fun u => taggedApertureRadius D.coefficient D.coefficient_nonzero u j
    activeNamed := fun u hu => taggedApertureRadius_named hc D.coefficient D.coefficient_nonzero
      D.coefficient_definable u j
    complementaryRadius := W.radius
    complementaryNamed := W.named
    invariant := W.ambient
    covariance := ?_
    aperture := ?_ }
  · refine ⟨C,rfl,(fun _ => rfl),?_⟩
    intro i
    let F := (C.restrict (hCompat i).subset (E i).sourceProper (W.pieces i)).component
    have hF : ApertureRestrictionData C.component F :=
      C.restrict_compatible (hCompat i).subset (E i).sourceProper (W.pieces i)
    refine ⟨F,hF,fun p hp => ?_⟩
    exact (hF.point p hp).trans ((hCompat i).point p hp).symm
  · intro u hu a ha b hb hab
    change _ < vfValue ((D.focusMap ⟨(a,u),ha,hu⟩).val 0-(D.focusMap ⟨(b,u),hb,hu⟩).val 0)
    rw [D.focusMap_eq ⟨(a,u),ha,hu⟩,D.focusMap_eq ⟨(b,u),hb,hu⟩]
    exact W.focus u hu a ha b hb hab
  · intro u hu a ha
    change _ ≤ vfValue (D.coefficient*(D.focusMap ⟨(a,u),ha,hu⟩).val 0)
    rw [D.focusMap_eq ⟨(a,u),ha,hu⟩]
    exact W.aperture u hu a ha

end DiamondIntegral.Section6
