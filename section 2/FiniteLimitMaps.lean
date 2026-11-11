import «section 2».UnaryLimits
import «section 2».FiniteBranchLimits

/-!
# Continuous images of finite minimal limit sets

Only continuity at the finitely many candidate limit points is needed.
This permits the reciprocal projective chart, whose inverse is continuous
at its nonzero finite values even though it is not continuous at zero.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n m : ℕ}

theorem HasLimitSet.minimal_of_frequent_hits
    {U : Set (Fin k → VF M)} {a : Fin k → VF M}
    {F : (Fin k → VF M) → Set (Fin n → VF M)} {L : Set (Fin n → VF M)}
    (hL : HasLimitSet U a F L) (hLf : L.Finite)
    (hhit : ∀ b ∈ L, ∀ ε δ : Gamma M,
      ∃ c ∈ U \ {a}, c ∈ vfBall a δ ∧ ∃ y ∈ F c, y ∈ vfBall b ε) :
    HasMinimalLimitSet U a F L := by
  refine ⟨hL,?_⟩
  intro K hK hlim
  obtain ⟨b,hb,hbK⟩ := Set.exists_of_ssubset hK
  have hKf : K.Finite := hLf.subset hK.1
  have hp : IsLimitSet U a F (finiteLimitPoint '' K) :=
    (hasLimitSet_iff_companion U a F K).mp hlim
  have hbimage : finiteLimitPoint b ∈ finiteLimitPoint '' K :=
    hp.mem_of_frequently_hits (hKf.image _) (by
      intro ε δ
      obtain ⟨c,hc,hnear,y,hy,hynear⟩ := hhit b hb ε δ
      exact ⟨c,hc,hnear,y,hy,by simpa only [limitBall_finite] using hynear⟩)
  obtain ⟨b',hb',he⟩ := hbimage
  exact hbK (finiteLimitPoint_injective he ▸ hb')

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem HasLimitSet.image_of_continuousAt
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : Set (Fin k → VF M)} {a : Fin k → VF M}
    {F : (Fin k → VF M) → Set (Fin n → VF M)} {L : Set (Fin n → VF M)}
    (hL : HasLimitSet U a F L) (hLf : L.Finite)
    (f : (Fin n → VF M) → Fin m → VF M) (hf : ∀ b ∈ L, ContinuousAt f b) :
    HasLimitSet U a (fun c => f '' F c) (f '' L) := by
  classical
  intro ε
  choose δ hδ using fun b : L => continuousAt_ball_estimate hv f b.val (hf b.val b.property) ε
  haveI : Finite L := hLf.to_subtype
  obtain ⟨η,hη⟩ := (Set.finite_range δ).bddAbove
  obtain ⟨ζ,hζ⟩ := hL η
  refine ⟨ζ,?_⟩
  rintro c hc hnear _ ⟨y,hy,rfl⟩
  obtain ⟨b,hb,hyb⟩ := hζ c hc hnear y hy
  refine ⟨f b,⟨b,hb,rfl⟩,?_⟩
  exact hδ ⟨b,hb⟩ y (vfBall_anti (hη (Set.mem_range_self ⟨b,hb⟩)) hyb)

theorem HasMinimalLimitSet.image_of_continuousAt
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : Set (Fin k → VF M)} {a : Fin k → VF M}
    {F : (Fin k → VF M) → Set (Fin n → VF M)} {L : Set (Fin n → VF M)}
    (hL : HasMinimalLimitSet U a F L) (hLf : L.Finite)
    (f : (Fin n → VF M) → Fin m → VF M) (hf : ∀ b ∈ L, ContinuousAt f b) :
    HasMinimalLimitSet U a (fun c => f '' F c) (f '' L) := by
  apply (hL.1.image_of_continuousAt hv hLf f hf).minimal_of_frequent_hits (hLf.image f)
  rintro _ ⟨b,hb,rfl⟩ ε δ
  obtain ⟨η,hη⟩ := continuousAt_ball_estimate hv f b (hf b hb) ε
  obtain ⟨c,hc,hnear,y,hy,hyb⟩ := hL.frequently_hits hb η δ
  exact ⟨c,hc,hnear,f y,⟨y,hy,rfl⟩,hη y hyb⟩

end DiamondIntegral.Section2
