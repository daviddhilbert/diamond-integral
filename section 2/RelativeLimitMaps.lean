import «section 2».FiniteLimitMaps

/-!
# Finite limits under maps continuous on the actual target set

Lemma 2.48 needs continuity within its closed domain, rather than a
continuous extension to all VF tuples. Every value of the approaching
correspondence remains in that domain throughout these estimates.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousWithinAt_ball_estimate
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF M) → Fin m → VF M) (A : Set (Fin n → VF M)) (a : Fin n → VF M)
    (hf : ContinuousWithinAt f A a) (ε : Gamma M) :
    ∃ δ : Gamma M, ∀ x ∈ A, x ∈ vfBall a δ → f x ∈ vfBall (f a) ε := by
  have h := hf.preimage_mem_nhdsWithin (vfBall_mem_nhds hv (f a) ε)
  obtain ⟨V,hV,hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  obtain ⟨δ,hδ⟩ := exists_vfBall_subset_nhds hv a hV
  exact ⟨δ,fun x hx hnear => hsub ⟨hδ hnear,hx⟩⟩

theorem HasLimitSet.image_of_continuousWithinAt
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : Set (Fin k → VF M)} {a : Fin k → VF M}
    {F : (Fin k → VF M) → Set (Fin n → VF M)} {L : Set (Fin n → VF M)}
    (hL : HasLimitSet U a F L) (hLf : L.Finite)
    (A : Set (Fin n → VF M)) (hFA : ∀ c ∈ U, F c ⊆ A)
    (f : (Fin n → VF M) → Fin m → VF M) (hf : ∀ b ∈ L, ContinuousWithinAt f A b) :
    HasLimitSet U a (fun c => f '' F c) (f '' L) := by
  classical
  intro ε
  choose δ hδ using fun b : L => continuousWithinAt_ball_estimate hv f A b.val (hf b.val b.property) ε
  haveI : Finite L := hLf.to_subtype
  obtain ⟨η,hη⟩ := (Set.finite_range δ).bddAbove
  obtain ⟨ζ,hζ⟩ := hL η
  refine ⟨ζ,?_⟩
  rintro c hc hnear _ ⟨y,hy,rfl⟩
  obtain ⟨b,hb,hyb⟩ := hζ c hc hnear y hy
  refine ⟨f b,⟨b,hb,rfl⟩,?_⟩
  exact hδ ⟨b,hb⟩ y (hFA c hc.1 hy)
    (vfBall_anti (hη (Set.mem_range_self ⟨b,hb⟩)) hyb)

theorem HasMinimalLimitSet.image_of_continuousWithinAt
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : Set (Fin k → VF M)} {a : Fin k → VF M}
    {F : (Fin k → VF M) → Set (Fin n → VF M)} {L : Set (Fin n → VF M)}
    (hL : HasMinimalLimitSet U a F L) (hLf : L.Finite)
    (A : Set (Fin n → VF M)) (hFA : ∀ c ∈ U, F c ⊆ A)
    (f : (Fin n → VF M) → Fin m → VF M) (hf : ∀ b ∈ L, ContinuousWithinAt f A b) :
    HasMinimalLimitSet U a (fun c => f '' F c) (f '' L) := by
  apply (hL.1.image_of_continuousWithinAt hv hLf A hFA f hf).minimal_of_frequent_hits (hLf.image f)
  rintro _ ⟨b,hb,rfl⟩ ε δ
  obtain ⟨η,hη⟩ := continuousWithinAt_ball_estimate hv f A b (hf b hb) ε
  obtain ⟨c,hc,hnear,y,hy,hyb⟩ := hL.frequently_hits hb η δ
  exact ⟨c,hc,hnear,f y,⟨y,hy,rfl⟩,hη y (hFA c hc.1 hy) hyb⟩

end DiamondIntegral.Section2
