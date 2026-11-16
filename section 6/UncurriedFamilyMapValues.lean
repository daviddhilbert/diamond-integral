import «section 6».UncurriedContinuousFamilyMaps
import «section 6».RVFocusContinuity

/-! Actual values and continuous tail fibres of the joint focus map.
No continuity in the parameter coordinate is presumed here; that is
the separate finite-freezing step in the fusion argument. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem uncurriedFamilyMap_value
    (F : ContinuousRVGraphTemplate (M := M) S 1 r n m)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hGood : ∀ x ∈ A.carrier,(fun _ : Fin 1 => (x.1 0).val) ∈ F.good) (x : A) :
    (uncurriedFamilyMap F A hGood x).val=
      F.value _ (hGood x.val x.property) x.val.2 (Fin.tail x.val.1) := by
  have hR : uncurriedFamilyRelation F A x.val (uncurriedFamilyMap F A hGood x).val := by
    unfold uncurriedFamilyMap
    exact Map.ofFunctionalRelation_graph _ _ _ _ x
  exact ((F.value_graph_at _ (hGood x.val x.property) x.val.2 (Fin.tail x.val.1) _).mp hR.2).symm

theorem uncurriedFamilyMap_tail_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : ContinuousRVGraphTemplate (M := M) S 1 r n 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hGood : ∀ x ∈ A.carrier,(fun _ : Fin 1 => (x.1 0).val) ∈ F.good)
    (u : Fin r → RVInfinity M) (a : VF M) : Continuous (focusTailMap (uncurriedFamilyMap F A hGood) u a) := by
  by_cases hNonempty : Nonempty (focusTailDomain A u a)
  · obtain ⟨p⟩ := hNonempty
    have ha : (fun _ : Fin 1 => a.val) ∈ F.good := hGood (Fin.cons a p.val,u) p.property
    have he : focusTailMap (uncurriedFamilyMap F A hGood) u a=
        (fun b : focusTailDomain A u a => F.value _ ha u b.val) := by
      funext b
      change (uncurriedFamilyMap F A hGood ⟨(Fin.cons a b.val,u),b.property⟩).val=_
      rw [uncurriedFamilyMap_value]
      rfl
    rw [he]
    exact (F.value_continuous hv _ ha u).comp continuous_subtype_val
  · have he : focusTailMap (uncurriedFamilyMap F A hGood) u a=
        (fun _ : focusTailDomain A u a => (0 : Fin 1 → VF M)) := by
      funext b
      exact (hNonempty ⟨b⟩).elim
    rw [he]
    exact continuous_const

end DiamondIntegral.Section6
