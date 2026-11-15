import «section 5».RESPositiveFamilies

/-! Equality in the actual ungraded reduced RES ring has a finite
stabilized witness whose total families contain the original objects
literally, and whose comparison maps are actual same-base RES isomorphisms.
The generating relation data are retained alongside these maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

def stabilizedFamily {k : ℕ} (a : RESChart B k)
    (C R : List (GradedObject hc B)) : List (GradedObject hc B) :=
  [⟨k, Section3RVChartBridge.nativeRES hc a⟩] ++ C ++ R

theorem stabilizedFamily_class {k : ℕ} (a : RESChart B k) (C R : List (GradedObject hc B)) :
    positiveFamilyClass hc B (stabilizedFamily hc B a C R) =
      positiveClass hc B a + positiveFamilyClass hc B C + positiveFamilyClass hc B R := by
  simp only [stabilizedFamily, positiveFamilyClass_append]
  simp only [positiveFamilyClass, List.map_singleton, List.sum_singleton, positiveClass]

structure ActualFamilyWitness {k l : ℕ} (a : RESChart B k) (b : RESChart B l) where
  stabilizer : List (GradedObject hc B)
  left_relations : List (GradedObject hc B)
  right_relations : List (GradedObject hc B)
  relations : PositiveRelationSum (relationPairs hc B)
    (positiveFamilyClass hc B left_relations) (positiveFamilyClass hc B right_relations)
  isomorphisms : ∀ d : Fin (positiveFamilyBound hc B
      (stabilizedFamily hc B a stabilizer right_relations)
      (stabilizedFamily hc B b stabilizer left_relations)),
    positiveFamilyAtDegree hc B d.val (stabilizedFamily hc B a stabilizer right_relations) ≅
      positiveFamilyAtDegree hc B d.val (stabilizedFamily hc B b stabilizer left_relations)

theorem res_equality_iff_actual_family_witness {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b) ↔
        Nonempty (ActualFamilyWitness hc B a b) := by
  constructor
  · intro he
    obtain ⟨C, L, R, hrel, htotal⟩ := (res_finite_stabilized_equality hc B a b).mp he
    obtain ⟨C', hC⟩ := positive_family_representative hc B C
    obtain ⟨L', hL⟩ := positive_family_representative hc B L
    obtain ⟨R', hR⟩ := positive_family_representative hc B R
    have htotal' : positiveFamilyClass hc B (stabilizedFamily hc B a C' R') =
        positiveFamilyClass hc B (stabilizedFamily hc B b C' L') := by
      rw [stabilizedFamily_class, stabilizedFamily_class, hC, hL, hR]
      exact htotal
    refine ⟨{
      stabilizer := C'
      left_relations := L'
      right_relations := R'
      relations := by rwa [hL, hR]
      isomorphisms := fun d => Classical.choice
        (positive_family_finite_bijections hc B _ _ htotal' d) }⟩
  · rintro ⟨w⟩
    let L := stabilizedFamily hc B a w.stabilizer w.right_relations
    let R := stabilizedFamily hc B b w.stabilizer w.left_relations
    have htotal : positiveFamilyClass hc B L = positiveFamilyClass hc B R :=
      (positive_family_equality_iff_finite_bijections hc B L R (positiveFamilyBound hc B L R)
        (positiveFamilyBound_left hc B L R) (positiveFamilyBound_right hc B L R)).mpr
          (fun d => ⟨w.isomorphisms d⟩)
    apply (res_finite_stabilized_equality hc B a b).mpr
    refine ⟨positiveFamilyClass hc B w.stabilizer, positiveFamilyClass hc B w.left_relations,
      positiveFamilyClass hc B w.right_relations, w.relations, ?_⟩
    exact (stabilizedFamily_class hc B a _ _).symm.trans
      (htotal.trans (stabilizedFamily_class hc B b _ _))

end DiamondIntegral.Section5.RESFiniteWitness
