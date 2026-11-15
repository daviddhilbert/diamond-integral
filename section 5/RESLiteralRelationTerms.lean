import «section 5».RESPositiveFamilies

/-! The positive ideal certificates expand into literal original-base
RES generators, actual underlying bijection graphs or value-fibre pairs,
finite coefficient-object families and an orientation bit. -/
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

inductive PrimitivePair (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  | underlying {k l : ℕ} (a : RESChart B k) (b : RESChart B l)
      (map : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart)
  | fibre (α : Values.Gamma (M := M)) (definable : GammaDefinableClosureAtBase B α)

def PrimitivePair.leftObject : PrimitivePair hc B → GradedObject hc B
  | .underlying a _ _ => ⟨_, Section3RVChartBridge.nativeRES hc a⟩
  | .fibre α hα => ⟨1, Section3RVChartBridge.nativeRES hc
      (RESFibreObjects.fibre B α 1 hα (GammaGroupNames.one_definable_base B))⟩

def PrimitivePair.rightObject : PrimitivePair hc B → GradedObject hc B
  | .underlying _ b _ => ⟨_, Section3RVChartBridge.nativeRES hc b⟩
  | .fibre _ _ => ⟨1, Section3RVChartBridge.nativeRES hc (RESFibreObjects.torus B)⟩

theorem PrimitivePair.relation (p : PrimitivePair hc B) :
    (gammaGroundRESDirectSumClass p.leftObject.2, gammaGroundRESDirectSumClass p.rightObject.2) ∈
      relationPairs hc B := by
  cases p with
  | underlying a b f => exact Or.inl ⟨_, _, a, b, f, rfl⟩
  | fibre α hα => exact Or.inr ⟨α, hα, rfl⟩

theorem relationPairs_literal {a b : GammaGroundRESDirectSum hc B}
    (h : (a, b) ∈ relationPairs hc B) :
    ∃ p : PrimitivePair hc B, gammaGroundRESDirectSumClass p.leftObject.2 = a ∧
      gammaGroundRESDirectSumClass p.rightObject.2 = b := by
  rcases h with h | h
  · obtain ⟨k, l, A, C, f, he⟩ := h
    exact ⟨.underlying A C f, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
  · obtain ⟨α, hα, he⟩ := h
    exact ⟨.fibre α hα, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

structure RelationTerm where
  primitive : PrimitivePair hc B
  coefficient : List (GradedObject hc B)
  reversed : Bool

def RelationTerm.leftFamily (t : RelationTerm hc B) : List (GradedObject hc B) :=
  positiveFamilyProduct hc B t.coefficient
    [if t.reversed then t.primitive.rightObject else t.primitive.leftObject]

def RelationTerm.rightFamily (t : RelationTerm hc B) : List (GradedObject hc B) :=
  positiveFamilyProduct hc B t.coefficient
    [if t.reversed then t.primitive.leftObject else t.primitive.rightObject]

theorem positiveFamilyClass_singleton (U : GradedObject hc B) :
    positiveFamilyClass hc B [U] = gammaGroundRESDirectSumClass U.2 := by
  simp only [positiveFamilyClass, List.map_singleton, List.sum_singleton]

theorem RelationTerm.positive_relation (t : RelationTerm hc B) :
    PositiveRelationSum (relationPairs hc B) (positiveFamilyClass hc B t.leftFamily)
      (positiveFamilyClass hc B t.rightFamily) := by
  cases ht : t.reversed
  · simpa only [RelationTerm.leftFamily, RelationTerm.rightFamily, ht, Bool.false_eq_true,
      if_false, positiveFamilyClass_product, positiveFamilyClass_singleton, zero_add] using
      (PositiveRelationSum.zero (P := relationPairs hc B)).step t.primitive.relation
        (positiveFamilyClass hc B t.coefficient)
  · simpa only [RelationTerm.leftFamily, RelationTerm.rightFamily, ht, if_true,
      positiveFamilyClass_product, positiveFamilyClass_singleton, zero_add] using
      (PositiveRelationSum.zero (P := relationPairs hc B)).reverse t.primitive.relation
        (positiveFamilyClass hc B t.coefficient)

def relationLeftFamily (terms : List (RelationTerm hc B)) : List (GradedObject hc B) :=
  terms.flatMap (RelationTerm.leftFamily hc B)

def relationRightFamily (terms : List (RelationTerm hc B)) : List (GradedObject hc B) :=
  terms.flatMap (RelationTerm.rightFamily hc B)

theorem relationTerms_positive_relation (terms : List (RelationTerm hc B)) :
    PositiveRelationSum (relationPairs hc B) (positiveFamilyClass hc B (relationLeftFamily hc B terms))
      (positiveFamilyClass hc B (relationRightFamily hc B terms)) := by
  induction terms with
  | nil => exact .zero
  | cons t terms ih =>
    simpa only [relationLeftFamily, relationRightFamily, List.flatMap_cons, positiveFamilyClass_append] using
      t.positive_relation.add ih

theorem literal_relation_term {a b : GammaGroundRESDirectSum hc B}
    (hab : (a, b) ∈ relationPairs hc B) (c : GammaGroundRESDirectSum hc B) (flip : Bool) :
    ∃ t : RelationTerm hc B,
      positiveFamilyClass hc B t.leftFamily = (if flip then c * b else c * a) ∧
      positiveFamilyClass hc B t.rightFamily = (if flip then c * a else c * b) := by
  obtain ⟨p, hpL, hpR⟩ := relationPairs_literal hc B hab
  obtain ⟨C, hC⟩ := positive_family_representative hc B c
  refine ⟨⟨p, C, flip⟩, ?_, ?_⟩ <;>
    cases flip <;> simp only [RelationTerm.leftFamily, RelationTerm.rightFamily,
      Bool.false_eq_true, if_false, if_true, positiveFamilyClass_product,
      positiveFamilyClass_singleton, hC, hpL, hpR]

theorem relationLeftFamilyClass_append (terms more : List (RelationTerm hc B)) :
    positiveFamilyClass hc B (relationLeftFamily hc B (terms ++ more)) =
      positiveFamilyClass hc B (relationLeftFamily hc B terms) +
        positiveFamilyClass hc B (relationLeftFamily hc B more) := by
  simp only [relationLeftFamily, List.flatMap_append, positiveFamilyClass_append]

theorem relationRightFamilyClass_append (terms more : List (RelationTerm hc B)) :
    positiveFamilyClass hc B (relationRightFamily hc B (terms ++ more)) =
      positiveFamilyClass hc B (relationRightFamily hc B terms) +
        positiveFamilyClass hc B (relationRightFamily hc B more) := by
  simp only [relationRightFamily, List.flatMap_append, positiveFamilyClass_append]

theorem positive_relation_literal_terms {L R : GammaGroundRESDirectSum hc B}
    (h : PositiveRelationSum (relationPairs hc B) L R) :
    ∃ terms : List (RelationTerm hc B),
      positiveFamilyClass hc B (relationLeftFamily hc B terms) = L ∧
        positiveFamilyClass hc B (relationRightFamily hc B terms) = R := by
  induction h with
  | zero => exact ⟨[], rfl, rfl⟩
  | @step L R h a b hab c ih =>
    obtain ⟨terms, hL, hR⟩ := ih
    obtain ⟨t, htL, htR⟩ := literal_relation_term hc B hab c false
    refine ⟨terms ++ [t], ?_, ?_⟩
    · rw [relationLeftFamilyClass_append, hL]
      simpa only [relationLeftFamily, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Bool.false_eq_true, if_false] using congrArg (fun z => L + z) htL
    · rw [relationRightFamilyClass_append, hR]
      simpa only [relationRightFamily, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Bool.false_eq_true, if_false] using congrArg (fun z => R + z) htR
  | @reverse L R h a b hab c ih =>
    obtain ⟨terms, hL, hR⟩ := ih
    obtain ⟨t, htL, htR⟩ := literal_relation_term hc B hab c true
    refine ⟨terms ++ [t], ?_, ?_⟩
    · rw [relationLeftFamilyClass_append, hL]
      simpa only [relationLeftFamily, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        if_true] using congrArg (fun z => L + z) htL
    · rw [relationRightFamilyClass_append, hR]
      simpa only [relationRightFamily, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        if_true] using congrArg (fun z => R + z) htR

end DiamondIntegral.Section5.RESFiniteWitness
