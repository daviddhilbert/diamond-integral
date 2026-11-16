import «section 6».UnaryParameterFreezing
import «section 6».UnaryIndexedFocusGraphs

/-! Freezing the unary parameter recomputes an entire indexed family.
Current ambient and protected product checks preserve their complete
restricted source sets, while later program domains are recomputed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FMT.FocusFreezingData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem unaryIndexed_mem_iff_freeze (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s) (p : Mixed M (n+1) (r+s)) :
    p ∈ (unaryIndexedMixedFamily (D.unaryParameter hB η) T).carrier ↔
      FMT.mixedFamilyFreeze D.balls D.centers 0 p ∈ (unaryIndexedMixedFamily η T).carrier := by
  let fp := FMT.mixedFamilyFreeze D.balls D.centers 0 p
  by_cases hpB : unaryFamilyBasePoint p ∈ B.carrier
  · let b : B := ⟨unaryFamilyBasePoint p,hpB⟩
    have hBase : unaryFamilyBasePoint fp=(D.unaryBaseFreeze hB b).val := by
      rw [D.unaryFamilyBasePoint_freeze]
      rfl
    have hTail : Fin.tail fp.1=Fin.tail p.1 := by
      funext i
      change Function.update p.1 0 (FMT.vfFamilyFreeze D.balls D.centers (p.1 0)) i.succ=p.1 i.succ
      exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
    rw [mem_unaryIndexedMixedFamily_at (D.unaryParameter hB η) T p b rfl,
      mem_unaryIndexedMixedFamily_at η T fp (D.unaryBaseFreeze hB b) hBase]
    rw [hTail]
    rfl
  · have hfB : unaryFamilyBasePoint fp ∉ B.carrier := by
      intro h
      have hFrozen : FMT.mixedFamilyFreeze D.balls D.centers 0 (unaryFamilyBasePoint p) ∈ B.carrier := by
        rw [← D.unaryFamilyBasePoint_freeze]
        exact h
      exact hpB ((FMT.mixedFamilyFreeze_mem_iff D.balls D.centers 0 D.separated B.carrier hB
        (unaryFamilyBasePoint p)).mp hFrozen)
    constructor
    · intro h
      obtain ⟨b,hb,hT⟩ := (mem_unaryIndexedMixedFamily _ T p).mp h
      exact (hpB (hb.symm ▸ b.property)).elim
    · intro h
      obtain ⟨b,hb,hT⟩ := (mem_unaryIndexedMixedFamily η T fp).mp h
      exact (hfB (hb.symm ▸ b.property)).elim

theorem unaryIndexed_restricted_family_preserved (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hW : ∀ E : D.balls,FMT.CoordinateProductDomain W.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (hQ : ∀ E : D.balls,FMT.CoordinateProductDomain
      (W.carrier ∩ (unaryIndexedMixedFamily η T).carrier) (FMT.vfOpenBall E.val) (D.centers E) 0) :
    W.carrier ∩ (unaryIndexedMixedFamily (D.unaryParameter hB η) T).carrier=
      W.carrier ∩ (unaryIndexedMixedFamily η T).carrier := by
  ext p
  change (p ∈ W.carrier ∧ p ∈ (unaryIndexedMixedFamily (D.unaryParameter hB η) T).carrier) ↔ _
  rw [D.unaryIndexed_mem_iff_freeze hB η T p]
  have hWAt := FMT.mixedFamilyFreeze_mem_iff D.balls D.centers 0 D.separated W.carrier hW p
  have hQAt := FMT.mixedFamilyFreeze_mem_iff D.balls D.centers 0 D.separated
    (W.carrier ∩ (unaryIndexedMixedFamily η T).carrier) hQ p
  exact (and_congr hWAt.symm Iff.rfl).trans hQAt

end DiamondIntegral.Section6.FMT.FocusFreezingData
