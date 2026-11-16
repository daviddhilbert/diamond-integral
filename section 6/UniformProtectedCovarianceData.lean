import «section 6».ProtectedTaggedApertureRadii

/-! One actual canonical covariance witness for a component and its
entire protected family. The sole complementary radius is named over
the original base and works for all existing RV labels. -/

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

structure UniformProtectedCovarianceData (D : CentripetalData (G := G) A) (j : Fin r)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S) where
  radius : Gamma M
  named : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {radius}}
  positive : 1 ≤ radius
  ambient : ∀ u ∈ D.activeTags.carrier,
    AlphaInvariant (fun t => if t=D.coordinate then taggedApertureRadius D.coefficient D.coefficient_nonzero u j else radius)
      (vfFibre A.carrier u)
  pieces : ∀ i,∀ u ∈ D.activeTags.carrier,
    AlphaInvariant (fun t => if t=D.coordinate then taggedApertureRadius D.coefficient D.coefficient_nonzero u j else radius)
      (vfFibre (P i).carrier u)
  focus : ∀ u ∈ D.activeTags.carrier,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
    Congruent (fun _ => radius) (Function.update a D.coordinate 0) (Function.update b D.coordinate 0) →
      (taggedApertureRadius D.coefficient D.coefficient_nonzero u j).val <
        vfValue (D.focus (Function.update a D.coordinate 0) u-D.focus (Function.update b D.coordinate 0) u)
  aperture : ∀ u ∈ D.activeTags.carrier,∀ a ∈ vfFibre A.carrier u,
    (taggedApertureRadius D.coefficient D.coefficient_nonzero u j).val ≤
      vfValue (D.coefficient*D.focus (Function.update a D.coordinate 0) u)

theorem exists_uniform_protected_covariance_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier) (j : Fin r)
    (hTag : ∀ p ∈ A.carrier,rv M (p.1 D.coordinate)=p.2 j)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hCompat : ∀ i,ApertureRestrictionData D (E i)) :
    Nonempty (UniformProtectedCovarianceData D j P) := by
  obtain ⟨β₀,hβ₀,hβ₀1,hCov⟩ := D.exists_uniform_tagged_covariance h00 hc linear hκ hs hv hsmall hΓ hARV j hTag
  obtain ⟨η,hη,hη1,hPInv⟩ := protected_source_invariant_at_tagged_aperture h00 hc linear hκ hs hv hsmall hΓ
    D j hTag P E hCompat
  let β := max β₀ η
  refine ⟨{
    radius := β
    named := gamma_max_named β₀ η hβ₀ hη
    positive := hβ₀1.trans (le_max_left _ _)
    ambient := ?_
    pieces := hPInv β (le_max_right _ _)
    focus := ?_
    aperture := ?_ }⟩
  · intro u hu
    obtain ⟨hα,hTuple,hInv,hFocus,hDom⟩ := hCov u hu
    apply hInv.larger_radius
    intro i
    by_cases hi : i=D.coordinate
    · simp only [if_pos hi]
      exact le_rfl
    · simp only [if_neg hi]
      exact le_max_left _ _
  · intro u hu a ha b hb hab
    obtain ⟨hα,hTuple,hInv,hFocus,hDom⟩ := hCov u hu
    exact hFocus a ha b hb (hab.of_larger_radius (fun _ => le_max_left _ _))
  · intro u hu
    exact (hCov u hu).2.2.2.2

end DiamondIntegral.Section6
