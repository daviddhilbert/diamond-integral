import «section 6».InvariantDomainFocusFreezing

/-! A continuous coordinate focus has a common permitted aperture for
all protected pieces and every Gamma level. One original-base named
coefficient is obtained from the actual focus image bound. -/

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

theorem exists_measured_continuous_focus_protected_components
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
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    ∃ δ : Gamma M, ∃ D : CentripetalData (G := G) A, D.coordinate = Fin.last n ∧ D.activeTags = U ∧
      (∀ x u, D.focus x u = totalFocusFibre f u (Fin.init x) 0) ∧
      (∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
        Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u) = gammaFormExtension ω (b,u)) ∧
      (∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p)) ∧
      ∀ i, ∃ E : CentripetalData (G := G) (C i), ApertureRestrictionData D E := by
  let H : Fin (k+1) → Set (Mixed M (n+1) r) := Fin.cons A.carrier (fun i => (C i).carrier)
  have hH : ∀ i, ProperInvariant S (H i) := Fin.cases hA hC
  obtain ⟨γ₀,hγ₀,hγ₀0,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  obtain ⟨α,hα,hα1,hInvAα,hInvLevels⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ
    hA (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) hLevels
  let γ := max α γ₀
  have hγ := gamma_max_named α γ₀ hα hγ₀
  have hInvA : ∀ u, AlphaInvariant (fun _ => γ) (vfFibre A.carrier u) :=
    fun u => (hInv 0 u).larger_radius (fun _ => le_max_right _ _)
  have hInvC (i) : ∀ u, AlphaInvariant (fun _ => γ) (vfFibre (C i).carrier u) :=
    fun u => (hInv i.succ u).larger_radius (fun _ => le_max_right _ _)
  have hConst (u) (a) (ha : a ∈ vfFibre A.carrier u) (b) (hb : b ∈ vfFibre A.carrier u)
      (hab : Congruent (fun _ => γ) a b) : gammaFormExtension ω (a,u) = gammaFormExtension ω (b,u) := by
    have h := (hInvLevels (gammaFormExtension ω (a,u)) u a b
      (hab.of_larger_radius (fun _ => le_max_left α γ₀))).mp ⟨ha,rfl⟩
    exact h.2.symm
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
  refine ⟨γ,D,rfl,rfl,fun _ _ => rfl,hConst,?_,?_⟩
  · intro p hp hCore
    have hu : p.2 ∈ U.carrier := by
      by_contra hn
      have hh := D.core_inactive hn
      rw [hCore] at hh
      cases hh
    rw [D.extendedFocus_active hp hu]
    change γ.val ≤ vfValue (c*totalFocusFibre f p.2 (Fin.init (Function.update p.1 (Fin.last n) 0)) 0)
    rw [init_update_last]
    let q : projectedActiveDomain A U := ⟨(Fin.init p.1,p.2),⟨⟨p,hp,hu⟩,rfl⟩⟩
    have he := congrFun (totalFocusFibre_at f p.2 (Fin.init p.1) q.property) 0
    rw [he]
    exact (hcdom _ ⟨q,rfl⟩).le
  · intro i
    let E := projectedFocusComponent (G := G) f (hCA i) (hC i) (hCD i) (hCtag i) hf hFocusRV
      γ β hγ hβ (hInvC i) hCov' c hc0 hcpos hcdef hcdom
    refine ⟨E,⟨hCA i,rfl,rfl,fun p hp => ?_⟩⟩
    by_cases hu : p.2 ∈ U.carrier
    · rw [E.extendedFocus_active hp hu,D.extendedFocus_active (hCA i hp) hu]
      rfl
    · rw [E.extendedFocus_inactive hu,D.extendedFocus_inactive hu]
end DiamondIntegral.Section6
