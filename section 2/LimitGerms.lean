import «section 2».FiniteBranchLimits

/-!
# Locality of finite limits and the curve-selection extension

The approved curve-selection proof extends a continuous germ by a constant
finite correspondence on a clopen complement. These are actual valuative
limit statements; no definable scalar realizing a radius is assumed.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open scoped Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem HasLimitSet.of_eventuallyEq
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f g : (Fin n → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (h : HasLimitSet A a f L) (heq : f =ᶠ[𝓝 a] g) : HasLimitSet A a g L := by
  obtain ⟨η, hη⟩ := exists_vfBall_subset_nhds hv a heq
  intro ε
  obtain ⟨δ, hδ⟩ := h ε
  refine ⟨max η δ, fun x hx hnear y hy => ?_⟩
  have he : f x = g x := hη (vfBall_anti (le_max_left _ _) hnear)
  rw [← he] at hy
  exact hδ x hx (vfBall_anti (le_max_right _ _) hnear) y hy

theorem hasMinimalLimitSet_iff_of_eventuallyEq
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f g : (Fin n → VF M) → Set (Fin m → VF M)} {L : Set (Fin m → VF M)}
    (heq : f =ᶠ[𝓝 a] g) :
    HasMinimalLimitSet A a f L ↔ HasMinimalLimitSet A a g L := by
  constructor
  · rintro ⟨h, hmin⟩
    exact ⟨h.of_eventuallyEq hv heq,
      fun K hK hlim => hmin K hK (hlim.of_eventuallyEq hv heq.symm)⟩
  · rintro ⟨h, hmin⟩
    exact ⟨h.of_eventuallyEq hv heq.symm,
      fun K hK hlim => hmin K hK (hlim.of_eventuallyEq hv heq)⟩

theorem finite_constant_minimal_limit
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (A : Set (Fin n → VF M)) (a : Fin n → VF M) (hA : A ∈ 𝓝 a)
    (E : Set (Fin m → VF M)) (hE : E.Finite) :
    HasMinimalLimitSet A a (fun _ => E) E := by
  let : Fintype E := hE.fintype
  have h := finite_continuous_branches_minimal_limit (ι := E) hv hn A a hA
    (fun e _ => e.val) (fun _ => continuousAt_const)
  have hr : Set.range (fun e : E => e.val) = E := by
    ext b
    exact ⟨fun ⟨e, he⟩ => he ▸ e.property, fun hb => ⟨⟨b, hb⟩, rfl⟩⟩
  simpa only [hr] using h

/-- The topological gluing step in the approved proof of Lemma 2.46.
The correspondence is only assumed continuous on the chosen clopen piece.
The empty constant correspondence is included. -/
theorem clopen_extension_continuous
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (A : Set (Fin n → VF M)) (hA : IsOpen A)
    (D : Set (Fin n → VF M)) (hD : IsClopen D)
    (f : (Fin n → VF M) → Set (Fin m → VF M))
    (E : Set (Fin m → VF M)) (hE : E.Finite)
    (hf : ∀ a ∈ A ∩ D, HasMinimalLimitSet A a f (f a)) :
    ∀ a ∈ A, HasMinimalLimitSet A a (D.piecewise f (fun _ => E))
      (D.piecewise f (fun _ => E) a) := by
  intro a ha
  by_cases haD : a ∈ D
  · have heq : f =ᶠ[𝓝 a] D.piecewise f (fun _ => E) := by
      filter_upwards [hD.isOpen.mem_nhds haD] with x hx
      simp only [Set.piecewise, ite_eq_left hx]
    have h := (hasMinimalLimitSet_iff_of_eventuallyEq hv heq).mp (hf a ⟨ha, haD⟩)
    simpa only [Set.piecewise, ite_eq_left haD] using h
  · have heq : (fun _ : Fin n → VF M => E) =ᶠ[𝓝 a] D.piecewise f (fun _ => E) := by
      filter_upwards [hD.isClosed.isOpen_compl.mem_nhds haD] with x hx
      simp only [Set.mem_compl_iff] at hx
      simp only [Set.piecewise, ite_eq_right hx]
    have h := (hasMinimalLimitSet_iff_of_eventuallyEq hv heq).mp
      (finite_constant_minimal_limit hv hn A a (hA.mem_nhds ha) E hE)
    simpa only [Set.piecewise, ite_eq_right haD] using h

end DiamondIntegral.Section2
