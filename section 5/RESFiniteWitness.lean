import «section 5».FiniteStabilization
import «section 4».Section3RESRingEquivalences
import «section 4».RESDimensionFreeReduction

/-! Finite positive witnesses in the actual original-base RES quotient.
The native positive semiring retains degrees; forgetting degree is one of
the displayed generating pairs, represented by actual underlying bijections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open RVMeasuredCharts Algebra Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

def positiveClass {k : ℕ} (a : RESChart B k) : GammaGroundRESDirectSum hc B :=
  gammaGroundRESDirectSumClass (Section3RVChartBridge.nativeRES hc a)

theorem of_positiveClass {k : ℕ} (a : RESChart B k) :
    (of (positiveClass hc B a) : GrothendieckAddGroup (GammaGroundRESDirectSum hc B)) =
      Section3RESRingEquivalences.ordinary hc B (RESOrdinaryRing.objectClass a) :=
  (Section3RESRingEquivalences.ordinary_class hc B a).symm

def relationPairs : Set ((GammaGroundRESDirectSum hc B) × (GammaGroundRESDirectSum hc B)) :=
  {p | (∃ k l, ∃ a : RESChart B k, ∃ b : RESChart B l,
      ∃ _F : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart,
        p = (positiveClass hc B a, positiveClass hc B b)) ∨
    (∃ α : Values.Gamma (M := M), ∃ hα : GammaDefinableClosureAtBase B α,
      p = (positiveClass hc B (RESFibreObjects.fibre B α 1 hα
        (GammaGroupNames.one_definable_base B)), positiveClass hc B (RESFibreObjects.torus B)))}

theorem relationIdeal_eq_map :
    positiveRelationIdeal (relationPairs hc B) =
      Ideal.map (Section3RESRingEquivalences.ordinary hc B).toRingHom
        (RESDimensionFreeRing.degreeIdeal B ⊔ RESOrdinaryReduction.fibreIdeal B) := by
  rw [RESDimensionFreeRing.degreeIdeal, RESOrdinaryReduction.fibreIdeal,
    ← Ideal.span_union, Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with h | h
    · obtain ⟨k, l, a, b, F, rfl⟩ := h
      refine ⟨RESOrdinaryRing.objectClass a - RESOrdinaryRing.objectClass b,
        Or.inl ⟨k, l, a, b, F, rfl⟩, ?_⟩
      simp only [map_sub, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [← of_positiveClass, ← of_positiveClass]
    · obtain ⟨α, hα, rfl⟩ := h
      refine ⟨_, Or.inr ⟨α, hα, rfl⟩, ?_⟩
      simp only [map_sub, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [← of_positiveClass, ← of_positiveClass]
  · rintro ⟨y, hy, rfl⟩
    rcases hy with h | h
    · obtain ⟨k, l, a, b, F, rfl⟩ := h
      refine ⟨(positiveClass hc B a, positiveClass hc B b),
        Or.inl ⟨k, l, a, b, F, rfl⟩, ?_⟩
      simp only [map_sub, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [← of_positiveClass, ← of_positiveClass]
    · obtain ⟨α, hα, rfl⟩ := h
      refine ⟨_, Or.inr ⟨α, hα, rfl⟩, ?_⟩
      simp only [map_sub, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [← of_positiveClass, ← of_positiveClass]

theorem relationIdeal_mem_iff (x : RESOrdinaryRing.Ring B) :
    Section3RESRingEquivalences.ordinary hc B x ∈ positiveRelationIdeal (relationPairs hc B) ↔
      x ∈ RESDimensionFreeRing.degreeIdeal B ⊔ RESOrdinaryReduction.fibreIdeal B := by
  rw [relationIdeal_eq_map]
  rw [Ideal.mem_map_iff_of_surjective (Section3RESRingEquivalences.ordinary hc B).toRingHom
    (Section3RESRingEquivalences.ordinary hc B).surjective]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Section3RESRingEquivalences.ordinary hc B).injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Actual reduced, ungraded RES equality is witnessed by one positive
stabilizer and a finite sum of positive generator pairs. Its positive
classes belong to the checked native category over precisely the same base. -/
theorem res_finite_stabilized_equality {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b) ↔
    ∃ C L R : GammaGroundRESDirectSum hc B,
      PositiveRelationSum (relationPairs hc B) L R ∧
      positiveClass hc B a + C + R = positiveClass hc B b + C + L := by
  rw [← finite_stabilized_quotient_equality, Ideal.Quotient.eq]
  rw [of_positiveClass, of_positiveClass, ← map_sub, relationIdeal_mem_iff]
  rw [← RESDimensionFreeReduction.kernel_fromOrdinary]
  change _ ↔ RESDimensionFreeReduction.fromOrdinary B
    (RESOrdinaryRing.objectClass a - RESOrdinaryRing.objectClass b) = 0
  rw [map_sub, sub_eq_zero]

theorem res_finite_list_equality {k l : ℕ} (a : RESChart B k) (b : RESChart B l)
    (he : RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b)) :
    ∃ C : GammaGroundRESDirectSum hc B,
      ∃ entries : List ((GammaGroundRESDirectSum hc B) × (GammaGroundRESDirectSum hc B)),
        (∀ p ∈ entries, OrientedPositivePair (relationPairs hc B) p) ∧
        positiveClass hc B a + C + (entries.map Prod.snd).sum =
          positiveClass hc B b + C + (entries.map Prod.fst).sum := by
  obtain ⟨C, L, R, h, he⟩ := (res_finite_stabilized_equality hc B a b).mp he
  obtain ⟨entries, hp, hL, hR⟩ := h.finite_list
  exact ⟨C, entries, hp, by rwa [← hL, ← hR]⟩

end DiamondIntegral.Section5.RESFiniteWitness
