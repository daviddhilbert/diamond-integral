import «section 3».MeasuredLocalMonomialCongruence
import «section 3».MeasuredRESWeightPartitions
import «section 3».RESUnitCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r : ℕ}
namespace GammaGroundRESUnitChart

def measured (X : GammaGroundRESUnitChart hc B r) : GammaGroundMeasuredRESObject hc B r :=
  X.object.withCombinedWeight (gammaGroundOneForm X.object.obj.domain)

@[simp] theorem measured_weight (X : GammaGroundRESUnitChart hc B r) (a : X.measured.obj.underlying.domain) :
    X.measured.obj.combinedWeight a = 1 :=
  (X.object.obj.withCombinedWeight_value _ a).trans (gammaGroundOneForm_value _ a)

/-- Native RES restrictions retain their actual finite labels and
prescribed combined weight one in a positive finite partition. -/
theorem measured_finite_partition {ι : Type} [Fintype ι]
    (X : GammaGroundRESUnitChart hc B r)
    (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (hA : ∀ i, (A i).carrier ⊆ X.native.carrier)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.native.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundMeasuredRESDirectSumClass X.measured =
      ∑ i, gammaGroundMeasuredRESDirectSumClass (X.restrict (A i) (hA i)).measured := by
  let E := fun i => X.bijection.inverseImage (A i)
  have hE := fun i => X.bijection.inverseImage_subset (A i)
  have hEd : ∀ i j, i ≠ j → Disjoint (E i).carrier (E j).carrier := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,hai⟩ ⟨b,hb,hbj⟩
    have he : a = b := Subtype.ext (ha.trans hb.symm)
    rw [← he] at hbj
    exact Set.disjoint_left.mp (hd i j hij) hai hbj
  have hEc : ∀ x, x ∈ X.object.obj.domain.carrier ↔ ∃ i, x ∈ (E i).carrier := by
    intro x
    constructor
    · intro hx
      let a : X.object.obj.domain := ⟨x,hx⟩
      obtain ⟨i,hi⟩ := (hcov (X.bijection.map a).val).mp (X.bijection.map a).property
      exact ⟨i,a,rfl,hi⟩
    · rintro ⟨i,hi⟩
      exact hE i hi
  have hp := gammaGroundMeasuredRESDirectSumClass_finite_partition X.measured E hEd hEc
  calc
    _ = ∑ i, gammaGroundMeasuredRESDirectSumClass (X.measured.restrict (E i) (hE i)) := hp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply gammaGroundMeasuredRESDirectSumClass_weight_bijection _ _ (GammaGroundBijection.id (E i))
      intro a
      change X.measured.obj.combinedWeight ⟨a.val,hE i a.property⟩ = (X.restrict (A i) (hA i)).measured.obj.combinedWeight a
      rw [X.measured_weight,(X.restrict (A i) (hA i)).measured_weight]

theorem measured_class_of_empty (X : GammaGroundRESUnitChart hc B r) (hX : X.native.carrier = ∅) :
    gammaGroundMeasuredRESDirectSumClass X.measured = 0 := by
  have hObj : X.object.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := (X.bijection.map ⟨x,hx⟩).property
    exact (Set.eq_empty_iff_forall_notMem.mp hX) _ h
  have he : gammaGroundMeasuredRESClass X.measured = 0 := by
    apply gammaGroundMeasuredRESToRVKPlus_injective
    rw [gammaGroundMeasuredRESToRVKPlus_class,map_zero]
    exact gammaGroundMeasuredRVClass_of_empty X.measured.obj hObj
  have h := congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) r) he
  simpa only [gammaGroundMeasuredRESDirectSumClass,map_zero] using h
end GammaGroundRESUnitChart
end DiamondIntegral.Section3
