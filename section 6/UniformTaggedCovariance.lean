import «section 6».TaggedApertureRadii

/-! Actual covariance witnesses in a canonical form: the active radius
comes from its retained RV tag and coefficient, and one original-base
named complementary radius works in every existing RV fibre. The
component, focus, coefficient and point map are unchanged. -/

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

theorem CentripetalData.exists_uniform_tagged_covariance
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier)
    (k : Fin r) (hTag : ∀ p ∈ A.carrier,rv M (p.1 D.coordinate)=p.2 k) :
    ∃ β : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}} ∧ 1 ≤ β ∧
      ∀ u ∈ D.activeTags.carrier,
        (S ∪ Set.range (rvValues u)).Definable LRV {z : Fin 1 → M |
          z 0 ∈ Values.gammaPullback {taggedApertureRadius D.coefficient D.coefficient_nonzero u k}} ∧
        NamedGammaTuple (S ∪ Set.range (rvValues u)) (fun _ : Fin n => β) ∧
        AlphaInvariant (fun i => if i=D.coordinate then taggedApertureRadius D.coefficient D.coefficient_nonzero u k else β)
          (vfFibre A.carrier u) ∧
        (∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
          Congruent (fun _ => β) (Function.update a D.coordinate 0) (Function.update b D.coordinate 0) →
          (taggedApertureRadius D.coefficient D.coefficient_nonzero u k).val <
            vfValue (D.focus (Function.update a D.coordinate 0) u-D.focus (Function.update b D.coordinate 0) u)) ∧
        ∀ a ∈ vfFibre A.carrier u,
          (taggedApertureRadius D.coefficient D.coefficient_nonzero u k).val ≤
            vfValue (D.coefficient*D.focus (Function.update a D.coordinate 0) u) := by
  obtain ⟨ρ,hρ,hBound⟩ := D.aperture_values_named_upper_bound h00 hc linear hκ hs hv hsmall hΓ
  obtain ⟨η,hη,hη1,hInv⟩ := D.source_invariant_at_tagged_aperture h00 hc linear hκ hs hv hsmall hΓ k hTag
  obtain ⟨ξ,hξ,hξ1,hCov⟩ := D.uniform_named_erased_covariance h00 hc linear hκ hs hv hsmall hΓ hARV ρ hρ
  let β := max η ξ
  have hβ := gamma_max_named η ξ hη hξ
  refine ⟨β,hβ,hη1.trans (le_max_left _ _),?_⟩
  intro u hu
  refine ⟨taggedApertureRadius_named hc D.coefficient D.coefficient_nonzero D.coefficient_definable u k,
    (fun _ => hβ.mono Set.subset_union_left),hInv β (le_max_left _ _) u hu,?_,?_⟩
  · intro a ha b hb hab
    have hCut : (taggedApertureRadius D.coefficient D.coefficient_nonzero u k).val ≤ ρ.val := by
      rw [D.tagged_aperture_value k hTag (a,u) ha hu]
      exact hBound (a,u) ha hu
    exact hCut.trans_lt (hCov u hu a ha b hb (hab.of_larger_radius (fun _ => le_max_right _ _)))
  · intro a ha
    rw [D.tagged_aperture_value k hTag (a,u) ha hu,D.extendedFocus_active ha hu]

end DiamondIntegral.Section6
