import «section 2».FiniteBranchLimits

/-! A singleton limit is the ordinary punctured topological limit.
Replacing the value at the centre by that limit gives a continuous germ. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open scoped Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem HasLimitSet.singleton_tendsto
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Fin m → VF M} {b : Fin m → VF M}
    (h : HasLimitSet A a (fun x => {f x}) {b}) :
    Tendsto f (𝓝[A \ {a}] a) (𝓝 b) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨ε,hε⟩ := exists_vfBall_subset_nhds hv b hU
  obtain ⟨δ,hδ⟩ := h ε
  have hnear : ∀ᶠ x in 𝓝[A \ {a}] a, x ∈ vfBall a δ :=
    mem_nhdsWithin_of_mem_nhds (vfBall_mem_nhds hv a δ)
  filter_upwards [hnear,self_mem_nhdsWithin] with x hx hxA
  obtain ⟨c,hc,hfc⟩ := hδ x hxA hx (f x) (Set.mem_singleton _)
  have he : c = b := hc
  exact hε (he ▸ hfc)

theorem HasLimitSet.continuousAt_update
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {f : (Fin n → VF M) → Fin m → VF M} {b : Fin m → VF M}
    (h : HasLimitSet A a (fun x => {f x}) {b}) (hA : A ∈ 𝓝 a) :
    ContinuousAt (Function.update f a b) a := by
  classical
  apply continuousAt_iff_punctured_nhds.mpr
  rw [Function.update_self]
  have hfilter : 𝓝[A \ {a}] a = 𝓝[≠] a :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hA)
  have ht := h.singleton_tendsto hv
  rw [hfilter] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxa : x ≠ a := hx
  exact (Function.update_of_ne hxa b f).symm

end DiamondIntegral.Section2
