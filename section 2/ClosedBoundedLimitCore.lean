import «section 2».RelativeLimitMaps
import «section 2».CurveSource

/-!
# The finite-limit contradictions in Lemma 2.48

Relative continuity sends the finite input limit to the output limit.
Approaching an affine point forces it into the image. Escaping past the
reciprocal input radius contradicts local boundedness of a finite limit.
These geometric steps precede the definable-family construction.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem image_mem_of_approaching_finite_limit
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M) (hf : ContinuousOn f A)
    (F : (Fin 1 → VF M) → Set (Fin n → VF M)) (L : Set (Fin n → VF M))
    (hL : HasMinimalLimitSet curveSource 0 F L) (hLf : L.Finite) (hLA : L ⊆ A)
    (hFA : ∀ c ∈ curveSource, F c ⊆ A) (hne : ∀ c ∈ curveSource, (F c).Nonempty)
    (b : Fin m → VF M)
    (hnear : ∀ c ∈ curveSource, ∀ x ∈ F c,
      vfValues (f x) ∈ SpecialTransformations.Section8.uniformBall (vfValues b) (c 0).val) :
    b ∈ f '' A := by
  have hImage : HasMinimalLimitSet curveSource 0 (fun c => f '' F c) (f '' L) :=
    hL.image_of_continuousWithinAt hv hLf A hFA f (fun a ha => hf a (hLA ha))
  have hPoint : HasMinimalLimitSet curveSource 0 (fun c => f '' F c) {b} :=
    vfApproach_hasMinimalLimitSet curveSource curveSource_nonzero curveSource_accumulates
      (f '' A) b (fun c => f '' F c) (by
        intro c hc
        rintro _ ⟨x,hx,rfl⟩
        exact ⟨⟨x,hFA c hc hx,rfl⟩,hnear c hc x hx⟩)
      (fun c hc => (hne c hc).image f)
  have heq : f '' L = {b} := by
    simpa only [(hLf.image f).isClosed.closure_eq,isClosed_singleton.closure_eq] using
      (lemma_2_43 hv hImage hPoint)
  have hb : b ∈ f '' L := heq.symm ▸ Set.mem_singleton b
  exact Set.image_mono hLA hb

theorem HasLimitSet.no_reciprocal_escape
    {F : (Fin 1 → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (hL : HasLimitSet curveSource 0 F L) (hLf : L.Finite)
    (hne : ∀ c ∈ curveSource, (F c).Nonempty)
    (hescape : ∀ c (hc : c ∈ curveSource), ∀ y ∈ F c, ∃ i,
      memLimitBall none (finiteValue (c 0) (curveSource_nonzero c hc)) (y i)) : False := by
  obtain ⟨δ,γ,hγ⟩ := hL.finite_locally_bounded hLf
  obtain ⟨c,hc,hnear⟩ := curveSource_accumulates (M := M) (max δ γ⁻¹)
  obtain ⟨y,hy⟩ := hne c hc.1
  obtain ⟨i,hi⟩ := hescape c hc.1 y hy
  have hcD : c ∈ (vfBall 0 δ ∩ curveSource) \ {(0 : Fin 1 → VF M)} :=
    ⟨⟨vfBall_anti (le_max_left _ _) hnear,hc.1⟩,hc.2⟩
  have hlower := hγ c hcD y hy i
  let η := finiteValue (c 0) (curveSource_nonzero c hc.1)
  have hlarge : γ⁻¹ < η := by
    have h := hnear 0
    change (max δ γ⁻¹).val < vfValue (c 0 - 0) at h
    simp only [sub_zero] at h
    exact (show (γ⁻¹).val ≤ (max δ γ⁻¹).val from le_max_right _ _).trans_lt h
  have hsmall : η⁻¹ < γ := by simpa only [inv_inv] using inv_lt_inv' hlarge
  have hi' : vfValue (y i) < (η⁻¹).val := hi
  exact (not_lt_of_ge hlower) (hi'.trans (show (η⁻¹).val < γ.val from hsmall))

end DiamondIntegral.Section2
