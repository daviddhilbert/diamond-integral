import «section 2».Differentiation
import «section 2».AlmostContinuity
import «section 2».FiniteBranchLimits
import Section9.MixedJacobianValue
import Section9.MixedDifferentiationAE

/-!
# Lemma 2.38: the mixed VF Jacobian is generically continuous

The checked fixed-label derivative and definable Jacobian value are reused.
The new assembly removes one same-base exceptional locus for both the
original map and a repeated-coordinate Jacobian map. Differentiability of
the latter implies actual continuity of the scalar Jacobian on VF fibres.
The auxiliary RV labels carry no topology. Empty VF arity gives determinant 1.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}

/-- Repeat a scalar coordinate in a square VF target, preserving definability. -/
noncomputable def repeatVFMap (n : ℕ) (S : Set M) :
    Map (DefSet.univ (rawVFSpace (M := M) 1) S)
      (DefSet.univ (rawMixedSpace (M := M) n 0) S) := by
  let P := rawVFSpace (M := M) 1
  let Q := rawMixedSpace (M := M) n 0
  let C (z : Fin 1 → M) : Fin n ⊕ Fin 0 → M := Sum.elim (fun _ => z 0) Fin.elim0
  have he (c : P.domain) : mixedValues ((fun _ : Fin n => P.decode c 0), Fin.elim0) = C c.val := by
    funext i
    cases i with
    | inl i => exact congrFun (vfValues_decode c) 0
    | inr i => exact i.elim0
  have hdom (c : P.domain) : C c.val ∈ Q.domain := by
    rw [← he c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes _ (fun a => (fun _ => a 0, Fin.elim0)) C
    (fun i => ?_) hdom ?_
  · cases i with
    | inl i => exact Set.DefinableFun.proj LRV
    | inr i => exact i.elim0
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode ⟨C c.val, hdom c⟩).trans (he c).symm

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

/-- A VF fibre of the Jacobian value, extended by zero off its original domain. -/
noncomputable def jacobianFibre
    (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S))
    (t : Fin r → RVInfinity M) (a : Fin n → VF M) : VF M := by
  classical
  exact if h : (a, t) ∈ A.carrier then (j ⟨(a, t), h⟩).val 0 else 0

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem HasDerivativeAt.continuousAt
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {m : ℕ} {f : (Fin n → VF M) → Fin m → VF M} {a : Fin n → VF M}
    {L : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)} (hf : HasDerivativeAt f a L) :
    ContinuousAt f a := by
  intro U hU
  obtain ⟨ε, hε⟩ := exists_vfBall_subset_nhds hv (f a) hU
  have hc : HasVFDerivativeAt f a L := (hasDerivativeAt_iff_companion f a L).mp hf
  obtain ⟨δ, hδ⟩ := hc.maps_vfBall ε
  change f ⁻¹' U ∈ 𝓝 a
  apply Filter.mem_of_superset (vfBall_mem_nhds hv a δ)
  intro x hx
  apply hε
  exact hδ hx

theorem jacobianFibre_continuousAt_of_chart
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : A)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hd : HasMixedVFDerivativeAt ((repeatVFMap n S).comp j) p L) :
    ContinuousAt (jacobianFibre j p.val.2) p.val.1 := by
  classical
  obtain ⟨H, ⟨ρ, hρ⟩, hH⟩ := hd
  change (Fin n → VF M) → Fin n → VF M at H
  let a : Fin n → VF M := p.val.1
  let t : Fin r → RVInfinity M := p.val.2
  let i : Fin n := ⟨0, hn⟩
  have hcH : ContinuousAt H p.val.1 :=
    HasDerivativeAt.continuousAt hv ((hasDerivativeAt_iff_companion H _ L).mpr hH)
  have heq : jacobianFibre j t =ᶠ[𝓝 a] (fun x => H x i) := by
    filter_upwards [vfBall_mem_nhds hv a ρ] with x hx
    obtain ⟨hxA, he⟩ := hρ x hx
    rw [jacobianFibre, dite_eq_left hxA]
    exact congrArg (fun q => q.1 i) he
  exact ((continuous_apply i).continuousAt.comp hcH).congr_of_eventuallyEq heq

/-- Lemma 2.38 for equal VF arities and arbitrary input/output RV arities.
The Jacobian is a definable VF value on the original domain. Its restriction
to every fixed input RV fibre is continuous off one same-base exceptional
set of smaller manuscript VF dimension. -/
theorem lemma_2_38 [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) :
    ∃ j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S),
      ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
        vfDimension E.carrier < (n : WithBot ℕ) ∧
        (∀ p : A, p.val ∉ E.carrier → HasMixedVFJacobianAt f p ((j p).val 0)) ∧
        ∀ t : Fin r → RVInfinity M,
          ContinuousOn (jacobianFibre j t) {a | (a, t) ∈ A.carrier \ E.carrier} := by
  classical
  obtain ⟨j, hj⟩ := exists_totalMixedJacobianMap f
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨j, DefSet.empty _ S, Set.empty_subset _, ?_, ?_, ?_⟩
    · rw [show (DefSet.empty (rawMixedSpace (M := M) 0 r) S).carrier = ∅ from rfl,
        vfDimension_empty]
      exact WithBot.bot_lt_coe 0
    · intro p _
      let H : (Fin 0 → VF M) → Fin 0 → VF M := fun _ => (f p).val.1
      have hH : HasVFDerivativeAt H p.val.1 (0 : (Fin 0 → VF M) →ₗ[VF M] (Fin 0 → VF M)) := by
        intro ε
        refine ⟨1, fun b hb _ => ?_⟩
        exact (hb (Subsingleton.elim b 0)).elim
      have hchart : IsVFChartAt f p H := by
        refine ⟨1, fun x _ => ?_⟩
        have he : x = p.val.1 := Subsingleton.elim _ _
        subst x
        exact ⟨p.property, rfl⟩
      have he := hj p 0 ⟨H, hchart, hH⟩
      rw [he]
      exact ⟨H, hchart, hH.hasJacobianAt⟩
    · intro t
      have he : jacobianFibre j t = fun _ => jacobianFibre j t 0 :=
        funext (fun x => congrArg (jacobianFibre j t) (Subsingleton.elim x 0))
      rw [he]
      exact continuous_const.continuousOn
  · let g := (repeatVFMap n S).comp j
    let Df := {x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L}
    let Dg := {x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt g p L}
    let P := rawMixedSpace (M := M) n r
    let E : DefSet P S := ⟨A.carrier \ (Df ∩ Dg), A.definable.sdiff P
      ((mixedDifferentiabilityLocus_definable hn f).inter P
        (mixedDifferentiabilityLocus_definable hn g))⟩
    have hgood (p : A) (hp : p.val ∉ E.carrier) : p.val ∈ Df ∩ Dg := by
      by_contra h
      exact hp ⟨p.property, h⟩
    refine ⟨j, E, Set.sdiff_subset, ?_, ?_, ?_⟩
    · apply vfDimension_lt_of_companion_lt hc hs hsmall _ (rawRVSpace_rvCoded 1) hv E
      apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn E
      intro p hp
      let q : A := ⟨p.val, p.property.1⟩
      exact p.property.2
        ⟨⟨q, rfl, mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f q hp⟩,
          ⟨q, rfl, mixedDifferentiableAt_of_independent hc hκ hs hsmall hv g q hp⟩⟩
    · intro p hp
      obtain ⟨q, hq, L, hL⟩ := (hgood p hp).1
      have he : q = p := Subtype.ext hq
      subst q
      rw [hj p L hL]
      obtain ⟨H, hchart, hH⟩ := hL
      exact ⟨H, hchart, hH.hasJacobianAt⟩
    · intro t a ha
      let p : A := ⟨(a, t), ha.1⟩
      obtain ⟨q, hq, L, hL⟩ := (hgood p ha.2).2
      have he : q = p := Subtype.ext hq
      subst q
      exact (jacobianFibre_continuousAt_of_chart hv hn j p hL).continuousWithinAt

end DiamondIntegral.Section2
