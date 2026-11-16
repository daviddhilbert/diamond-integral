import «section 6».MeasuredContinuousFocusRealization

/-! The same finite continuity-repair discs protect every measure level
as well as the ambient and the finite protected family. The levels use
one uniform radius and need no individually named parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_measured_projected_focus_freezing
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S) (hA : ProperInvariant S A.carrier)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hf : ∀ u a, Continuous (focusTailMap f u a))
    (hFocusRV : ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre f p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last (n+1))))
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hP : ∀ i, ProperInvariant S (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin (n+2) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    ∃ D : FMT.FocusFreezingData (projectedActiveDomain A U),
      (∀ u, Continuous (FMT.focusFibre (D.frozenMap f) u)) ∧
      (∀ p ∈ A.carrier, p.2 ∈ U.carrier →
        rv M (totalFocusFibre (D.frozenMap f) p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last (n+1)))) ∧
      (∀ E : D.balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val)
        (D.centers E) (0 : Fin (n+1)).castSucc) ∧
      (∀ i, ∀ E : D.balls, FMT.CoordinateProductDomain (P i).carrier (FMT.vfOpenBall E.val)
        (D.centers E) (0 : Fin (n+1)).castSucc) ∧
      ∀ γ, ∀ E : D.balls, FMT.CoordinateProductDomain
        {p | p ∈ A.carrier ∧ gammaFormExtension ω p = γ} (FMT.vfOpenBall E.val)
        (D.centers E) (0 : Fin (n+1)).castSucc := by
  let H : Fin (k+1) → Set (Mixed M (n+2) r) := Fin.cons A.carrier (fun i => (P i).carrier)
  have hH : ∀ i, ProperInvariant S (H i) := Fin.cases hA hP
  obtain ⟨β,hβ,hβ1,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  obtain ⟨α,hα,hα1,hInvA,hInvLevels⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ
    hA (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) hLevels
  let δ := max α β
  have hδ := gamma_max_named α β hα hβ
  have hδ1 : 1 ≤ δ := hα1.trans (le_max_left _ _)
  have hAδ (u) : AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) :=
    (hInvA u).larger_radius (fun _ => le_max_left _ _)
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ1 hδ
  let Q : Fin (k+1) ⊕ Gamma M → Set (Mixed M (n+2) r) :=
    Sum.elim H (fun γ => {p | p ∈ A.carrier ∧ gammaFormExtension ω p = γ})
  have hQ : ∀ i u, AlphaInvariant (fun _ => δ) (vfFibre (Q i) u) := by
    rintro (i | γ) u
    · exact (hInv i u).larger_radius (fun _ => le_max_right _ _)
    · exact (hInvLevels γ u).larger_radius (fun _ => le_max_left _ _)
  obtain ⟨D,hCont,hProd⟩ := FMT.exists_continuous_focus_freezing_with_invariant_domains h00 hc hκ hs hsmall hv
    δ (projectedActiveDomain_uniform_radius U δ hAδ) s hs0 hsdef hδs.le f hf Q hQ
      (0 : Fin (n+1)).castSucc
  exact ⟨D,hCont,FMT.frozenProjectedFocus_leadingTerms D f (hProd (.inl 0)) hFocusRV,
    hProd (.inl 0),fun i => hProd (.inl i.succ),fun γ => hProd (.inr γ)⟩

end DiamondIntegral.Section6
