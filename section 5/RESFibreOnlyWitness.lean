import «section 5».RESUngradedPositiveFamilies

/-! The literal finite RES witness can be chosen with only value-fibre
pairs. Every degree-forgetting pair already has an actual underlying
bijection, so its positive family is moved to the common stabilizer.
This uses no positive cancellation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def PrimitivePair.IsFibre : PrimitivePair hc B → Prop
  | .underlying _ _ _ => False
  | .fibre _ _ => True

instance (t : PrimitivePair hc B) : Decidable t.IsFibre := by cases t <;> simp only [PrimitivePair.IsFibre] <;> infer_instance

def fibreTerms (L : List (RelationTerm hc B)) : List (RelationTerm hc B) :=
  L.filter (fun t => t.primitive.IsFibre)

def underlyingTermsFamily : List (RelationTerm hc B) → List (GradedObject hc B)
  | [] => []
  | t :: L => if t.primitive.IsFibre then underlyingTermsFamily L
      else t.leftFamily ++ underlyingTermsFamily L

variable (hc B)
theorem productFamily_underlying_eq (L : List (GradedObject hc B))
    (U V : GradedObject hc B) (e : GammaGroundBijection U.2.obj.domain V.2.obj.domain) :
    familyUnderlyingClass hc B (positiveFamilyProduct hc B L [U]) =
      familyUnderlyingClass hc B (positiveFamilyProduct hc B L [V]) := by
  induction L with
  | nil => rfl
  | cons C L ih =>
    change familyUnderlyingClass hc B ([gradedObjectProduct hc B C U] ++ positiveFamilyProduct hc B L [U]) =
      familyUnderlyingClass hc B ([gradedObjectProduct hc B C V] ++ positiveFamilyProduct hc B L [V])
    rw [familyUnderlyingClass_append,familyUnderlyingClass_append,ih]
    apply congrArg (fun x => x + familyUnderlyingClass hc B (positiveFamilyProduct hc B L [V]))
    rw [familyUnderlyingClass_singleton,familyUnderlyingClass_singleton]
    exact (nativeRVSetIsoClass_eq_iff _ _).mpr
      ⟨nativeRawProductBijection (GammaGroundBijection.id C.2.obj.domain) e⟩

theorem RelationTerm.underlying_eq (t : RelationTerm hc B) (ht : ¬ t.primitive.IsFibre) :
    familyUnderlyingClass hc B t.leftFamily = familyUnderlyingClass hc B t.rightFamily := by
  rcases t with ⟨p,C,b⟩
  cases p with
  | fibre α hα => exact False.elim (ht trivial)
  | underlying A D e =>
    let f := nativeUnderlyingBijection (hc := hc) e
    cases b
    · exact productFamily_underlying_eq hc B C _ _ f
    · exact productFamily_underlying_eq hc B C _ _ f.symm

theorem relationFamilies_underlying_split (L : List (RelationTerm hc B)) :
    familyUnderlyingClass hc B (relationLeftFamily hc B L) =
      familyUnderlyingClass hc B (underlyingTermsFamily L) +
        familyUnderlyingClass hc B (relationLeftFamily hc B (fibreTerms L)) ∧
    familyUnderlyingClass hc B (relationRightFamily hc B L) =
      familyUnderlyingClass hc B (underlyingTermsFamily L) +
        familyUnderlyingClass hc B (relationRightFamily hc B (fibreTerms L)) := by
  induction L with
  | nil => simp [familyUnderlyingClass,familyRVSet,relationLeftFamily,relationRightFamily,
      underlyingTermsFamily,fibreTerms,nativeRVSetIsoClass_empty]
  | cons t L ih =>
    by_cases ht : t.primitive.IsFibre
    · have hf : fibreTerms (t :: L) = t :: fibreTerms L := by simp [fibreTerms,ht]
      simp only [relationLeftFamily,relationRightFamily,List.flatMap_cons,familyUnderlyingClass_append,
        underlyingTermsFamily,ht,ite_true,hf] at ih ⊢
      exact ⟨by rw [ih.1]; ac_rfl,by rw [ih.2]; ac_rfl⟩
    · have he := RelationTerm.underlying_eq hc B t ht
      have hf : fibreTerms (t :: L) = fibreTerms L := by simp [fibreTerms,ht]
      simp only [relationLeftFamily,relationRightFamily,List.flatMap_cons,familyUnderlyingClass_append,
        underlyingTermsFamily,ht,ite_false,hf] at ih ⊢
      exact ⟨by rw [ih.1]; ac_rfl,by rw [ih.2,←he]; ac_rfl⟩

structure FibreOnlyFamilyWitness {k l : ℕ} (a : RVMeasuredCharts.RESChart B k)
    (b : RVMeasuredCharts.RESChart B l) where
  stabilizer : List (GradedObject hc B)
  terms : List (RelationTerm hc B)
  fibre_only : ∀ t ∈ terms, t.primitive.IsFibre
  bijection : GammaGroundBijection
    (familyRVSet hc B (stabilizedFamily hc B a stabilizer (relationRightFamily hc B terms))).2
    (familyRVSet hc B (stabilizedFamily hc B b stabilizer (relationLeftFamily hc B terms))).2

def LiteralFamilyWitness.fibreOnly {k l : ℕ} {a : RVMeasuredCharts.RESChart B k}
    {b : RVMeasuredCharts.RESChart B l} (w : LiteralFamilyWitness hc B a b) :
    FibreOnlyFamilyWitness hc B a b := by
  let U := underlyingTermsFamily w.terms
  have htot : positiveFamilyClass hc B
      (stabilizedFamily hc B a w.stabilizer (relationRightFamily hc B w.terms)) =
    positiveFamilyClass hc B
      (stabilizedFamily hc B b w.stabilizer (relationLeftFamily hc B w.terms)) :=
    (positive_family_equality_iff_finite_bijections hc B _ _ _
      (positiveFamilyBound_left hc B _ _) (positiveFamilyBound_right hc B _ _)).mpr
        (fun d => ⟨w.isomorphisms d⟩)
  have he := congrArg (nativeRESGradedUnderlying (hc := hc) (B := B)) htot
  rw [← familyUnderlyingClass_eq,← familyUnderlyingClass_eq] at he
  have hs := relationFamilies_underlying_split hc B w.terms
  simp only [stabilizedFamily,familyUnderlyingClass_append] at he
  rw [hs.1,hs.2] at he
  refine {
    stabilizer := w.stabilizer ++ U
    terms := fibreTerms w.terms
    fibre_only := fun t ht => of_decide_eq_true (List.mem_filter.mp ht).2
    bijection := Classical.choice ((familyUnderlyingClass_eq_iff hc B _ _).mp ?_) }
  simp only [stabilizedFamily,familyUnderlyingClass_append]
  change _ = _
  calc
    _ = familyUnderlyingClass hc B [⟨k,Section3RVChartBridge.nativeRES hc a⟩] +
        familyUnderlyingClass hc B w.stabilizer +
        (familyUnderlyingClass hc B U + familyUnderlyingClass hc B (relationRightFamily hc B (fibreTerms w.terms))) := by ac_rfl
    _ = _ := he
    _ = _ := by dsimp only [U]; ac_rfl

theorem res_equality_has_fibre_only_witness {k l : ℕ}
    (a : RVMeasuredCharts.RESChart B k) (b : RVMeasuredCharts.RESChart B l)
    (he : RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass b)) :
    Nonempty (FibreOnlyFamilyWitness hc B a b) := by
  obtain ⟨w⟩ := (res_equality_iff_literal_family_witness hc B a b).mp he
  exact ⟨w.fibreOnly hc B⟩

end DiamondIntegral.Section5.RESFiniteWitness
