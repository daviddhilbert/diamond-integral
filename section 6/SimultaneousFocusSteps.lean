import «section 6».ContinuousFocusRealization

/-! Actual permitted focus steps in every positive VF arity. A common
centripetal component followed by actual regularization retains all
compatible protected components in one common finite-chain certificate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def centripetalStepMap (D : CentripetalData (G := G) A) :=
  (regularization D.map.image).comp D.bijection

theorem simultaneous_centripetal_step
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i, CentripetalData (G := G) (P i)) (hRestr : ∀ i, ApertureRestrictionData D (E i)) :
    SimultaneousCentripetalChain (G := G) I A (regularizeMap D.map.image).image (centripetalStepMap D) P := by
  let hPA (i) := (hRestr i).subset
  let Q (i : I) := (D.bijection.restrict (hPA i)).image
  have hQsub (i) : (Q i).carrier ⊆ D.map.image.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (D.bijection ⟨p.val,hPA i p.property⟩).property
  have hQeq (i) : (E i).map.image = Q i :=
    image_eq_of_surjective_liesOver D.bijection (E i).bijection ((E i).bijective h00).surjective
      (hPA i) (fun p => (hRestr i).point p.val p.property)
  have hQproper (i) : ProperInvariant S (Q i).carrier := by
    rw [← hQeq i]
    exact (E i).image_properInvariant h00 hc hκ hs hv
  have hQdouble (i) : VFDoublyBounded (Q i).carrier := by
    rw [← hQeq i]
    exact (E i).image_vfDoublyBounded
  exact .comp P hPA (.centripetal A D P hPA E (fun i p hp => (hRestr i).point p hp))
    (.regularize D.map.image (D.image_properInvariant h00 hc hκ hs hv)
      D.image_vfDoublyBounded Q hQsub hQproper hQdouble)

theorem continuous_focus_simultaneous_step_exists {k : ℕ}
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (B : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier)
    (htag : ∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (f : Map (projectedActiveDomain B U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hf : ∀ u, Continuous (FMT.focusFibre f u))
    (hFocusRV : ∀ p ∈ B.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre f p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last n)))
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hCB : ∀ i, (C i).carrier ⊆ B.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ D : CentripetalData (G := G) B, D.coordinate = Fin.last n ∧ D.activeTags = U ∧
      (∀ x u, D.focus x u = totalFocusFibre f u (Fin.init x) 0) ∧
      SimultaneousCentripetalChain (G := G) (Fin k) B (regularizeMap D.map.image).image
        (centripetalStepMap D) C := by
  obtain ⟨D,hj,hU,hFocus,hE⟩ := exists_continuous_focus_protected_components
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt B hB hBD htag U f hf hFocusRV C hCB hC
  let E (i) := (hE i).choose
  exact ⟨D,hj,hU,hFocus,simultaneous_centripetal_step h00 hc hκ hs hv D C E (fun i => (hE i).choose_spec)⟩

end DiamondIntegral.Section6
