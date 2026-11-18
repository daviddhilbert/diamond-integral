import «section 5».RESFibreOnlyCriterion

/-! Test 5.20 with tuple Gamma parameters `α_j ∈ Γ^{n_j}`.

Each relation pair is `(α_j^♯ × Z_j, (G_m)^{n_j} × Z_j)` or its reverse, with
`Z_j` a single original-base RES object and every coordinate of `α_j` definable
over the original base. The objects are actual iterated products: the RV
product domain is the image of the concatenation map, so
`Z × α_1^♯ × ⋯ × α_{n}^♯` is literally `Z × α^♯` with
`α^♯ = {u ∈ RV^n : vrv(u) = α}`, and similarly for the torus power.

Both directions are proved. The forward direction reuses the one-coordinate
fibre-only witness: each one-coordinate pair with a finite coefficient family
splits into tuple pairs of arity one with single coefficient objects, with
literally the same tagged families. The converse uses only the one-coordinate
generators and multiplicativity, as in the manuscript ("tuple generators give
the same ideal by expanding a difference of products"). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness.Test520
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

/-- A base-definable value tuple `α ∈ Γ^n`. -/
structure GammaTuple where
  arity : ℕ
  value : Fin arity → Values.Gamma (M := M)
  definable : ∀ i, GammaDefinableClosureAtBase B (value i)

/-- The one-coordinate value fibre `α^♯ ⊆ RV`, exactly as in the primitive pair. -/
def fibreFactor (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) :
    GradedObject hc B := (PrimitivePair.fibre (hc := hc) α hα).leftObject

/-- The torus `G_m ⊆ RV` (the value fibre over the unit of `Γ`), exactly as in the primitive pair. -/
def torusFactor : GradedObject hc B :=
  ⟨1, Section3RVChartBridge.nativeRES hc (RESFibreObjects.torus B)⟩

theorem primitive_fibre_rightObject (α : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) :
    (PrimitivePair.fibre (hc := hc) α hα).rightObject = torusFactor hc B := rfl

variable {B} in
/-- The coordinate fibres of `α^♯ = α_1^♯ × ⋯ × α_n^♯`. -/
def GammaTuple.fibreFactors (α : GammaTuple B) : List (GradedObject hc B) :=
  List.ofFn (fun i => fibreFactor hc B (α.value i) (α.definable i))

variable {B} in
/-- The coordinate factors of `(G_m)^n`. -/
def GammaTuple.torusFactors (α : GammaTuple B) : List (GradedObject hc B) :=
  List.replicate α.arity (torusFactor hc B)

/-- The actual iterated product `Z × U_1 × ⋯ × U_n`. -/
def iteratedObject : GradedObject hc B → List (GradedObject hc B) → GradedObject hc B
  | Z, [] => Z
  | Z, U :: L => iteratedObject (gradedObjectProduct hc B Z U) L

/-- A tuple relation pair `(L_j, R_j)`: `(α^♯ × Z, (G_m)^n × Z)` or its reverse. -/
structure TupleRelationTerm where
  values : GammaTuple B
  coefficient : GradedObject hc B
  reversed : Bool

variable {hc B} in
def TupleRelationTerm.left (t : TupleRelationTerm hc B) : GradedObject hc B :=
  iteratedObject hc B t.coefficient
    (if t.reversed then t.values.torusFactors hc else t.values.fibreFactors hc)

variable {hc B} in
def TupleRelationTerm.right (t : TupleRelationTerm hc B) : GradedObject hc B :=
  iteratedObject hc B t.coefficient
    (if t.reversed then t.values.fibreFactors hc else t.values.torusFactors hc)

/-- `⨆_j L_j`, as a tagged family. -/
def tupleLeftFamily (terms : List (TupleRelationTerm hc B)) : List (GradedObject hc B) :=
  terms.map TupleRelationTerm.left

/-- `⨆_j R_j`, as a tagged family. -/
def tupleRightFamily (terms : List (TupleRelationTerm hc B)) : List (GradedObject hc B) :=
  terms.map TupleRelationTerm.right

/-- The finite witness of Test 5.20 with tuple parameters: a common stabilizer
`C`, finitely many tuple pairs, and an actual original-base bijection
`P ⊔ C ⊔ ⨆_j R_j ≃ Q ⊔ C ⊔ ⨆_j L_j` of tagged disjoint unions. -/
structure TupleFibreFamilyWitness {k l : ℕ} (a : RVMeasuredCharts.RESChart B k)
    (b : RVMeasuredCharts.RESChart B l) where
  stabilizer : List (GradedObject hc B)
  terms : List (TupleRelationTerm hc B)
  bijection : GammaGroundBijection
    (familyRVSet hc B (stabilizedFamily hc B a stabilizer (tupleRightFamily hc B terms))).2
    (familyRVSet hc B (stabilizedFamily hc B b stabilizer (tupleLeftFamily hc B terms))).2

/-! ### Converse: a tuple witness gives equality in `R(𝕋)` -/

theorem fibreFactor_reduced (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) :
    reducedPositiveHom hc B (gammaGroundRESDirectSumClass (fibreFactor hc B α hα).2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass (torusFactor hc B).2) := by
  have h := (PositiveRelationSum.zero (P := relationPairs hc B)).step
    (PrimitivePair.fibre (hc := hc) α hα).relation 1
  rw [zero_add, zero_add, one_mul, one_mul] at h
  exact positiveRelation_reduced_eq hc B h

theorem iteratedObject_reduced (Z : GradedObject hc B) (L : List (GradedObject hc B))
    (hL : ∀ U ∈ L, reducedPositiveHom hc B (gammaGroundRESDirectSumClass U.2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass (torusFactor hc B).2)) :
    reducedPositiveHom hc B (gammaGroundRESDirectSumClass (iteratedObject hc B Z L).2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass Z.2) *
        reducedPositiveHom hc B (gammaGroundRESDirectSumClass (torusFactor hc B).2) ^ L.length := by
  induction L generalizing Z with
  | nil => simp [iteratedObject]
  | cons U L ih =>
    change reducedPositiveHom hc B (gammaGroundRESDirectSumClass
      (iteratedObject hc B (gradedObjectProduct hc B Z U) L).2) = _
    rw [ih _ (fun V hV => hL V (List.mem_cons_of_mem _ hV))]
    change reducedPositiveHom hc B (gammaGroundRESDirectSumClass (Z.2.product U.2)) * _ = _
    rw [gammaGroundRESDirectSumClass_product, map_mul, hL U List.mem_cons_self,
      List.length_cons, pow_succ]
    ring

theorem fibreFactors_reduced (α : GammaTuple B) :
    ∀ U ∈ α.fibreFactors hc, reducedPositiveHom hc B (gammaGroundRESDirectSumClass U.2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass (torusFactor hc B).2) := by
  intro U hU
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hU
  exact fibreFactor_reduced hc B _ _

theorem torusFactors_reduced (α : GammaTuple B) :
    ∀ U ∈ α.torusFactors hc, reducedPositiveHom hc B (gammaGroundRESDirectSumClass U.2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass (torusFactor hc B).2) := by
  intro U hU
  rw [List.eq_of_mem_replicate hU]

/-- Each tuple pair is a relation of `R(𝕋)`: `[α^♯ × Z] = [(G_m)^n × Z]`. -/
theorem TupleRelationTerm.reduced_eq (t : TupleRelationTerm hc B) :
    reducedPositiveHom hc B (gammaGroundRESDirectSumClass t.left.2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass t.right.2) := by
  obtain ⟨v, Z, r⟩ := t
  have hF := iteratedObject_reduced hc B Z _ (fibreFactors_reduced hc B v)
  have hT := iteratedObject_reduced hc B Z _ (torusFactors_reduced hc B v)
  have hl : (v.fibreFactors hc).length = (v.torusFactors hc).length := by
    simp [GammaTuple.fibreFactors, GammaTuple.torusFactors]
  cases r
  · change reducedPositiveHom hc B (gammaGroundRESDirectSumClass
        (iteratedObject hc B Z (v.fibreFactors hc)).2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass (iteratedObject hc B Z (v.torusFactors hc)).2)
    rw [hF, hT, hl]
  · change reducedPositiveHom hc B (gammaGroundRESDirectSumClass
        (iteratedObject hc B Z (v.torusFactors hc)).2) =
      reducedPositiveHom hc B (gammaGroundRESDirectSumClass (iteratedObject hc B Z (v.fibreFactors hc)).2)
    rw [hF, hT, hl]

theorem tupleFamilies_reduced_eq (terms : List (TupleRelationTerm hc B)) :
    reducedPositiveHom hc B (positiveFamilyClass hc B (tupleLeftFamily hc B terms)) =
      reducedPositiveHom hc B (positiveFamilyClass hc B (tupleRightFamily hc B terms)) := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    change reducedPositiveHom hc B (positiveFamilyClass hc B (t.left :: tupleLeftFamily hc B terms)) =
      reducedPositiveHom hc B (positiveFamilyClass hc B (t.right :: tupleRightFamily hc B terms))
    rw [positiveFamilyClass_cons, positiveFamilyClass_cons, map_add, map_add, ih,
      TupleRelationTerm.reduced_eq hc B t]

variable {hc B} in
theorem TupleFibreFamilyWitness.reduced_equality {k l : ℕ} {a : RVMeasuredCharts.RESChart B k}
    {b : RVMeasuredCharts.RESChart B l} (w : TupleFibreFamilyWitness hc B a b) :
    RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b) := by
  have hu := nativeUngradedClass_bijection hc
    (familyNativeObject hc B (stabilizedFamily hc B a w.stabilizer (tupleRightFamily hc B w.terms)))
    (familyNativeObject hc B (stabilizedFamily hc B b w.stabilizer (tupleLeftFamily hc B w.terms)))
    w.bijection
  have he := congrArg (RESDimensionFreeReduction.quotient B) hu
  change RESDimensionFreeReduction.quotient B (familyUngradedClass hc B _) =
    RESDimensionFreeReduction.quotient B (familyUngradedClass hc B _) at he
  rw [familyReducedClass_eq,familyReducedClass_eq,stabilizedFamily_class,stabilizedFamily_class,
    map_add,map_add,map_add,map_add,reducedPositiveHom_positiveClass,reducedPositiveHom_positiveClass] at he
  rw [tupleFamilies_reduced_eq hc B w.terms] at he
  exact add_right_cancel (add_right_cancel he)

/-! ### Forward: equality gives a tuple witness (via arity one) -/

variable {B} in
/-- A single value as a tuple of arity one. -/
def oneTuple (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) : GammaTuple B :=
  ⟨1, fun _ => α, fun _ => hα⟩

variable {hc B} in
/-- Split each one-coordinate fibre term `(α^♯ × ⨆ Z, G_m × ⨆ Z)` into arity-one
tuple pairs with single coefficient objects. -/
def termsToTuple : (L : List (RelationTerm hc B)) → (∀ t ∈ L, t.primitive.IsFibre) →
    List (TupleRelationTerm hc B)
  | [], _ => []
  | ⟨.fibre α hα, C, r⟩ :: L, h =>
      C.map (fun Z => ⟨oneTuple α hα, Z, r⟩) ++
        termsToTuple L (fun t ht => h t (List.mem_cons_of_mem _ ht))
  | ⟨.underlying _ _ _, _, _⟩ :: _, h => False.elim (h _ List.mem_cons_self)

theorem oneTuple_fibreFactors (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) :
    (oneTuple α hα).fibreFactors hc = [(PrimitivePair.fibre (hc := hc) α hα).leftObject] := rfl

theorem oneTuple_torusFactors (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) :
    (oneTuple α hα).torusFactors hc = [(PrimitivePair.fibre (hc := hc) α hα).rightObject] := rfl

theorem oneTuple_coefficient_families (α : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (C : List (GradedObject hc B)) (r : Bool) :
    (C.map (fun Z => (⟨oneTuple α hα, Z, r⟩ : TupleRelationTerm hc B))).map TupleRelationTerm.left =
        RelationTerm.leftFamily hc B ⟨.fibre α hα, C, r⟩ ∧
      (C.map (fun Z => (⟨oneTuple α hα, Z, r⟩ : TupleRelationTerm hc B))).map TupleRelationTerm.right =
        RelationTerm.rightFamily hc B ⟨.fibre α hα, C, r⟩ := by
  induction C with
  | nil => exact ⟨rfl, rfl⟩
  | cons Z C ihC =>
    simp only [List.map_cons, RelationTerm.leftFamily, RelationTerm.rightFamily,
      positiveFamilyProduct, List.flatMap_cons] at ihC ⊢
    rw [ihC.1, ihC.2]
    cases r <;> exact ⟨rfl, rfl⟩

theorem termsToTuple_families (L : List (RelationTerm hc B)) (h : ∀ t ∈ L, t.primitive.IsFibre) :
    tupleLeftFamily hc B (termsToTuple L h) = relationLeftFamily hc B L ∧
      tupleRightFamily hc B (termsToTuple L h) = relationRightFamily hc B L := by
  induction L with
  | nil => exact ⟨rfl, rfl⟩
  | cons t L ih =>
    obtain ⟨p, C, r⟩ := t
    cases p with
    | underlying a b f => exact False.elim (h _ List.mem_cons_self)
    | fibre α hα =>
      have ih' := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
      have hC := oneTuple_coefficient_families hc B α hα C r
      change tupleLeftFamily hc B (C.map (fun Z => ⟨oneTuple α hα, Z, r⟩) ++
          termsToTuple L (fun t ht => h t (List.mem_cons_of_mem _ ht))) =
          RelationTerm.leftFamily hc B ⟨.fibre α hα, C, r⟩ ++ relationLeftFamily hc B L ∧
        tupleRightFamily hc B (C.map (fun Z => ⟨oneTuple α hα, Z, r⟩) ++
          termsToTuple L (fun t ht => h t (List.mem_cons_of_mem _ ht))) =
          RelationTerm.rightFamily hc B ⟨.fibre α hα, C, r⟩ ++ relationRightFamily hc B L
      simp only [tupleLeftFamily, tupleRightFamily, List.map_append] at ih' ⊢
      rw [ih'.1, ih'.2, hC.1, hC.2]
      exact ⟨rfl, rfl⟩

variable {hc B} in
/-- Every fibre-only witness is a tuple witness with all `n_j = 1`. -/
def fibreOnlyToTuple {k l : ℕ} {a : RVMeasuredCharts.RESChart B k}
    {b : RVMeasuredCharts.RESChart B l} (w : FibreOnlyFamilyWitness hc B a b) :
    TupleFibreFamilyWitness hc B a b where
  stabilizer := w.stabilizer
  terms := termsToTuple w.terms w.fibre_only
  bijection := by
    rw [(termsToTuple_families hc B w.terms w.fibre_only).1,
      (termsToTuple_families hc B w.terms w.fibre_only).2]
    exact w.bijection

/-- **Test 5.20** with tuple parameters `α_j ∈ Γ^{n_j}`, both directions:
`[P] = [Q]` in `R(𝕋)` iff there are a stabilizer `C`, finitely many tuple pairs
`(L_j, R_j) = (α_j^♯ × Z_j, (G_m)^{n_j} × Z_j)` or reversed, and an actual
original-base bijection `P ⊔ C ⊔ ⨆ R_j ≃ Q ⊔ C ⊔ ⨆ L_j`. -/
theorem test_5_20_tuples {k l : ℕ}
    (a : RVMeasuredCharts.RESChart B k) (b : RVMeasuredCharts.RESChart B l) :
    RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b) ↔
        Nonempty (TupleFibreFamilyWitness hc B a b) := by
  constructor
  · intro he
    obtain ⟨w⟩ := res_equality_has_fibre_only_witness hc B a b he
    exact ⟨fibreOnlyToTuple w⟩
  · rintro ⟨w⟩
    exact w.reduced_equality

/-- Tuple witnesses with arbitrary arities are equivalent to the one-coordinate
fibre-only witnesses of `res_equality_iff_fibre_only_family_witness`. -/
theorem tuple_witness_iff_fibre_only_witness {k l : ℕ}
    (a : RVMeasuredCharts.RESChart B k) (b : RVMeasuredCharts.RESChart B l) :
    Nonempty (TupleFibreFamilyWitness hc B a b) ↔ Nonempty (FibreOnlyFamilyWitness hc B a b) :=
  (test_5_20_tuples hc B a b).symm.trans (res_equality_iff_fibre_only_family_witness hc B a b)

end DiamondIntegral.Section5.RESFiniteWitness.Test520
