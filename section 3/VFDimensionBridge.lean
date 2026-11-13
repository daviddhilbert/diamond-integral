import «section 2».AlmostContinuity
import Section4.FullDimension

/-! The exceptional-set dimension in Definition 3.5 is exactly the
coordinate-interior dimension of section 2. The comparison with the
companion's finite-map dimension includes empty sets in positive degree;
degree zero is stated separately with the manuscript's bottom convention. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {S : Set M} {n r : ℕ}

theorem vf_small_iff_companion
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Section2.vfDimension A.carrier < (n : WithBot ℕ) ↔
      vfDim (rawRVSpace 1) A < n := by
  constructor
  · intro hd
    apply lt_of_le_of_ne (vfDim_le_arity (rawRVSpace 1) A)
    intro he
    by_cases hne : A.carrier.Nonempty
    · obtain ⟨t, D, hD⟩ := (lemma_4_6 hc hs hS _ (rawRVSpace_rvCoded 1) hv A hne).mp he
      have hf : Section2.vfDimension A.carrier = (n : WithBot ℕ) :=
        (Section2.lemma_2_17 A.carrier).mpr ⟨t, D, hD⟩
      exact hd.ne hf
    · have hz : vfDim (rawRVSpace 1) A ≤ 0 :=
        (vfDim_le_iff_point_trdeg hc hs hS _ (rawRVSpace_rvCoded 1) A 0).mpr
          (fun a => (hne ⟨a.val, a.property⟩).elim)
      exact (Nat.not_le_of_gt hn) (he ▸ hz)
  · exact Section2.vfDimension_lt_of_companion_lt hc hs hS _ (rawRVSpace_rvCoded 1) hv A

theorem vf_small_zero_iff_empty (A : Set (Section2.Mixed M n r)) :
    Section2.vfDimension A < (0 : WithBot ℕ) ↔ A = ∅ := by
  constructor
  · intro h
    by_contra he
    have hd := ((Section2.hasVFInteriorDim_zero_iff A).mpr
      (Set.nonempty_iff_ne_empty.mpr he)).le_dimension
    exact (not_le_of_gt h) hd
  · rintro rfl
    rw [Section2.vfDimension_empty]
    exact WithBot.bot_lt_coe 0

end DiamondIntegral.Section3
