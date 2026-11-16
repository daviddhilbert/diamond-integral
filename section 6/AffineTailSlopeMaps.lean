import «section 6».VFTupleArithmeticMaps
import Section9.AffineTailMaps

/-! The guarded affine slopes form an actual map over the same base.
Evaluate the affine tail one unit from its source centre and subtract
the target centre; no extra representative is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {S : Set M} {m : ℕ}

theorem exists_affineTailSlopesMap (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {P : SpecialTransformations.DefinableGeometry.Space LRV M} {A : DefSet P S}
    (a b : Map A (DefSet.univ (rawVFSpace (M := M) m) S))
    (D c : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (j : Fin m)
    (ha : ∀ p i, (a p).val i ≠ 0) (hb : ∀ p i, (b p).val i ≠ 0) :
    ∃ s : Map A (DefSet.univ (rawVFSpace (M := M) m) S), ∀ p,
      (s p).val = affineTailSlopesForHead v (a p).val (b p).val j ((D p).val 0) ((c p).val 0) := by
  let x := (vfTupleBinaryMap S .add).comp (a.pair (vfTupleOnesMap (m := m) A)).toUniv
  obtain ⟨T,hT⟩ := exists_affineTailMap v hv a b x D c j ha hb
  let s := (vfTupleBinaryMap S .sub).comp (T.pair b).toUniv
  refine ⟨s,fun p => ?_⟩
  change (fun i => (T p).val i - (b p).val i) = _
  rw [hT p]
  funext i
  change (b p).val i + _ * ((a p).val i + 1 - (a p).val i) - (b p).val i = _
  ring

end DiamondIntegral.Section6
