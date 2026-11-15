import «section 5».RESActualFamilyWitnesses
import «section 5».GammaRVSetObjects

/-! The finite stabilized family witness produces one literal tagged
RV-domain bijection between actual RES objects over the same base.
Every degree component and every zero/one tag is retained in the encoding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {k l : ℕ} {a : RESChart B k} {b : RESChart B l}

def ActualFamilyWitness.leftTotal (w : ActualFamilyWitness hc B a b) : List (GradedObject hc B) :=
  stabilizedFamily hc B a w.stabilizer w.right_relations

def ActualFamilyWitness.rightTotal (w : ActualFamilyWitness hc B a b) : List (GradedObject hc B) :=
  stabilizedFamily hc B b w.stabilizer w.left_relations

def ActualFamilyWitness.degreeCount (w : ActualFamilyWitness hc B a b) : ℕ :=
  positiveFamilyBound hc B w.leftTotal w.rightTotal

def actualFamilyDegreeDomain (L : List (GradedObject hc B)) (d : ℕ) : GammaRVSet hc B :=
  ⟨(positiveFamilyAtDegree hc B d L).obj.arity, (positiveFamilyAtDegree hc B d L).obj.domain⟩

def ActualFamilyWitness.taggedLeft (w : ActualFamilyWitness hc B a b) : GammaRVSet hc B :=
  taggedRVFinFamily hc B w.degreeCount (fun d => actualFamilyDegreeDomain w.leftTotal d.val)

def ActualFamilyWitness.taggedRight (w : ActualFamilyWitness hc B a b) : GammaRVSet hc B :=
  taggedRVFinFamily hc B w.degreeCount (fun d => actualFamilyDegreeDomain w.rightTotal d.val)

theorem ActualFamilyWitness.taggedLeft_finite (w : ActualFamilyWitness hc B a b) :
    GammaRVFiniteValues hc B w.taggedLeft.2 :=
  taggedRVFinFamily_finite_values hc B w.degreeCount _
    (fun d => (positiveFamilyAtDegree hc B d.val w.leftTotal).property)

theorem ActualFamilyWitness.taggedRight_finite (w : ActualFamilyWitness hc B a b) :
    GammaRVFiniteValues hc B w.taggedRight.2 :=
  taggedRVFinFamily_finite_values hc B w.degreeCount _
    (fun d => (positiveFamilyAtDegree hc B d.val w.rightTotal).property)

def ActualFamilyWitness.taggedSourceObject (w : ActualFamilyWitness hc B a b) :
    GammaGroundRESObject hc B w.taggedLeft.1 :=
  nativeRESObjectOfGammaSet hc B w.taggedLeft.2 w.taggedLeft_finite

def ActualFamilyWitness.taggedTargetObject (w : ActualFamilyWitness hc B a b) :
    GammaGroundRESObject hc B w.taggedRight.1 :=
  nativeRESObjectOfGammaSet hc B w.taggedRight.2 w.taggedRight_finite

def ActualFamilyWitness.taggedBijection (w : ActualFamilyWitness hc B a b) :
    GammaGroundBijection w.taggedSourceObject.obj.domain w.taggedTargetObject.obj.domain := by
  change GammaGroundBijection w.taggedLeft.2 w.taggedRight.2
  exact taggedRVFinFamilyBijection hc B w.degreeCount
    (fun d => actualFamilyDegreeDomain w.leftTotal d.val)
    (fun d => actualFamilyDegreeDomain w.rightTotal d.val) (fun d => (w.isomorphisms d).hom.hom)

theorem res_equality_has_literal_tagged_witness (a : RESChart B k) (b : RESChart B l)
    (he : RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b)) :
    ∃ w : ActualFamilyWitness hc B a b,
      Nonempty (GammaGroundBijection w.taggedSourceObject.obj.domain w.taggedTargetObject.obj.domain) := by
  obtain ⟨w⟩ := (res_equality_iff_actual_family_witness hc B a b).mp he
  exact ⟨w, ⟨w.taggedBijection⟩⟩

end DiamondIntegral.Section5.RESFiniteWitness
