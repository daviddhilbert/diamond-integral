import «section 6».ProjectedFocusBounds

/-! Every actual continuous projected focus on a proper doubly bounded
tagged source has a permitted realization in every positive VF arity.
One original-base named coefficient and one uniform covariance bound
simultaneously protect any finite proper invariant subfamily. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_continuous_focus_protected_components
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hf : ∀ u, Continuous (FMT.focusFibre f u))
    (hFocusRV : ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre f p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last n)))
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ D : CentripetalData (G := G) A, D.coordinate = Fin.last n ∧ D.activeTags = U ∧
      (∀ x u, D.focus x u = totalFocusFibre f u (Fin.init x) 0) ∧
      ∀ i, ∃ E : CentripetalData (G := G) (C i), ApertureRestrictionData D E := by
  let H : Fin (k+1) → Set (Mixed M (n+1) r) := Fin.cons A.carrier (fun i => (C i).carrier)
  have hH : ∀ i, ProperInvariant S (H i) := Fin.cases hA hC
  obtain ⟨γ,hγ,hγ0,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  have hInvA : ∀ u, AlphaInvariant (fun _ => γ) (vfFibre A.carrier u) := hInv 0
  have hInvC (i) : ∀ u, AlphaInvariant (fun _ => γ) (vfFibre (C i).carrier u) := hInv i.succ
  obtain ⟨β,hβ,hβ0,hCov⟩ := continuous_mixed_focus_uniform_named_covariance h00 hc linear hκ hs hv hsmall hΓ
    f (projectedActiveDomain_properInvariant A U hA) hf γ hγ
  obtain ⟨η,hLower⟩ := projectedFocus_image_lowerBound f hAD hFocusRV
  obtain ⟨c,hc0,hcpos,hcdef,hcdom⟩ := exists_named_aperture_coefficient_of_lowerBound Valued.v hv hc h00
    V S hV hVS hSV hnt _ (scalarFocusImage_definable f) η hLower γ hγ
  have hCov' (u) := (hCov u).2
  let D := projectedFocusComponent (G := G) f (Set.Subset.refl A.carrier) hA hAD htag hf hFocusRV
    γ β hγ hβ hInvA hCov' c hc0 hcpos hcdef hcdom
  have hCD (i) : VFDoublyBounded (C i).carrier := by
    obtain ⟨δ,hδ⟩ := hAD
    exact ⟨δ,fun p hp => hδ p (hCA i hp)⟩
  have hCtag (i) : ∀ p ∈ (C i).carrier, ∀ q ∈ (C i).carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 :=
    fun p hp q hq => htag p (hCA i hp) q (hCA i hq)
  refine ⟨D,rfl,rfl,fun _ _ => rfl,fun i => ?_⟩
  let E := projectedFocusComponent (G := G) f (hCA i) (hC i) (hCD i) (hCtag i) hf hFocusRV
    γ β hγ hβ (hInvC i) hCov' c hc0 hcpos hcdef hcdom
  refine ⟨E,⟨hCA i,rfl,rfl,fun p hp => ?_⟩⟩
  by_cases hu : p.2 ∈ U.carrier
  · rw [E.extendedFocus_active hp hu,D.extendedFocus_active (hCA i hp) hu]
    rfl
  · rw [E.extendedFocus_inactive hu,D.extendedFocus_inactive hu]

end DiamondIntegral.Section6
