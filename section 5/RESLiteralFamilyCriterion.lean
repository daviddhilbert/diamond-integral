import «section 5».RESLiteralRelationTerms
import «section 5».RESLiteralTaggedWitnesses

/-! The finite stabilized criterion with literal generator data.
Every coefficient is a finite family of actual RES objects; every
primitive is an actual underlying bijection or a definable value-fibre
pair. No equality of positive classes is included as witness input. -/
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
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

structure LiteralFamilyWitness {k l : ℕ} (a : RESChart B k) (b : RESChart B l) where
  stabilizer : List (GradedObject hc B)
  terms : List (RelationTerm hc B)
  isomorphisms : ∀ d : Fin (positiveFamilyBound hc B
      (stabilizedFamily hc B a stabilizer (relationRightFamily hc B terms))
      (stabilizedFamily hc B b stabilizer (relationLeftFamily hc B terms))),
    positiveFamilyAtDegree hc B d.val
      (stabilizedFamily hc B a stabilizer (relationRightFamily hc B terms)) ≅
    positiveFamilyAtDegree hc B d.val
      (stabilizedFamily hc B b stabilizer (relationLeftFamily hc B terms))

variable {hc B}

def LiteralFamilyWitness.toActual {k l : ℕ} {a : RESChart B k} {b : RESChart B l}
    (w : LiteralFamilyWitness hc B a b) : ActualFamilyWitness hc B a b where
  stabilizer := w.stabilizer
  left_relations := relationLeftFamily hc B w.terms
  right_relations := relationRightFamily hc B w.terms
  relations := relationTerms_positive_relation hc B w.terms
  isomorphisms := w.isomorphisms

def LiteralFamilyWitness.taggedBijection {k l : ℕ} {a : RESChart B k} {b : RESChart B l}
    (w : LiteralFamilyWitness hc B a b) :
    GammaGroundBijection w.toActual.taggedSourceObject.obj.domain w.toActual.taggedTargetObject.obj.domain :=
  w.toActual.taggedBijection

variable (hc B)

theorem res_equality_iff_literal_family_witness {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b) ↔
        Nonempty (LiteralFamilyWitness hc B a b) := by
  constructor
  · intro he
    obtain ⟨C, L, R, hrel, htotal⟩ := (res_finite_stabilized_equality hc B a b).mp he
    obtain ⟨C', hC⟩ := positive_family_representative hc B C
    obtain ⟨terms, hL, hR⟩ := positive_relation_literal_terms hc B hrel
    have he' : positiveFamilyClass hc B
        (stabilizedFamily hc B a C' (relationRightFamily hc B terms)) =
        positiveFamilyClass hc B (stabilizedFamily hc B b C' (relationLeftFamily hc B terms)) := by
      rw [stabilizedFamily_class, stabilizedFamily_class, hC, hL, hR]
      exact htotal
    exact ⟨{
      stabilizer := C'
      terms := terms
      isomorphisms := fun d => Classical.choice (positive_family_finite_bijections hc B _ _ he' d) }⟩
  · rintro ⟨w⟩
    exact (res_equality_iff_actual_family_witness hc B a b).mpr ⟨w.toActual⟩

end DiamondIntegral.Section5.RESFiniteWitness
