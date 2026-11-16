import «section 6».FrozenFocusLeadingTerms

/-! Full protected projected-focus freezing: choose a common original-
base radius, construct the finite exception discs and centers, verify
every current product domain, and retain the permitted leading term. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}

theorem projectedActiveDomain_uniform_radius
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (U : DefSet (rawRVSpace (M := M) r) S) (δ : Gamma M)
    (hInv : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u)) :
    ∀ u, AlphaInvariant (fun _ => δ) (vfFibre (projectedActiveDomain A U).carrier u) := by
  intro u
  change AlphaInvariant (fun _ => δ) (vfFibre (vfDropLast (focusActive A U)).image.carrier u)
  rw [vfDropLast_image_fibre]
  have hActive : AlphaInvariant (fun _ => δ) (vfFibre (focusActive A U).carrier u) :=
    fun a b hab => and_congr (hInv u a b hab) Iff.rfl
  exact hActive.image_init

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_protected_projected_focus_freezing
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
    (hP : ∀ i, ProperInvariant S (P i).carrier) :
    ∃ D : FMT.FocusFreezingData (projectedActiveDomain A U),
      (∀ u, Continuous (FMT.focusFibre (D.frozenMap f) u)) ∧
      (∀ p ∈ A.carrier, p.2 ∈ U.carrier →
        rv M (totalFocusFibre (D.frozenMap f) p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last (n+1)))) ∧
      (∀ E : D.balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val)
        (D.centers E) (0 : Fin (n+1)).castSucc) ∧
      ∀ i, ∀ E : D.balls, FMT.CoordinateProductDomain (P i).carrier (FMT.vfOpenBall E.val)
        (D.centers E) (0 : Fin (n+1)).castSucc := by
  let H : Fin (k+1) → Set (Mixed M (n+2) r) := Fin.cons A.carrier (fun i => (P i).carrier)
  have hH : ∀ i, ProperInvariant S (H i) := Fin.cases hA hP
  obtain ⟨δ,hδ,hδ0,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  have hInvA : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) := hInv 0
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ0 hδ
  let Q : Fin (k+1) → DefSet (rawMixedSpace (M := M) (n+2) r) S := Fin.cons A P
  have hQ : ∀ i u, AlphaInvariant (fun _ => δ) (vfFibre (Q i).carrier u) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hInv 0
    · exact hInv j.succ
  obtain ⟨D,hCont,hProd⟩ := FMT.exists_continuous_focus_freezing_with_domains h00 hc hκ hs hsmall hv
    δ (projectedActiveDomain_uniform_radius U δ hInvA) s hs0 hsdef hδs.le f hf Q hQ
      (0 : Fin (n+1)).castSucc
  exact ⟨D,hCont,FMT.frozenProjectedFocus_leadingTerms D f (hProd 0) hFocusRV,hProd 0,
    fun i => hProd i.succ⟩

end DiamondIntegral.Section6
