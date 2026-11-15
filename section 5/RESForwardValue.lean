import «section 5».FiniteFramePartitions
import «section 5».RationalFramedMaps
import «section 5».DiagonalFinitePartitions

/-! The forward comparison value of every actual finite-value original
RV domain, as a finite sum over its intrinsic value and zero patterns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance resForwardValueStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

def valuePattern {n : ℕ} (r : Fin n → CanonicalRV.RVSort Carrier) : Fin n → WithTop ℚ :=
  fun i => value (taggedRVEquiv (r i))

def actualValuePatterns {n : ℕ} (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) :
    Set (Fin n → WithTop ℚ) := Set.range (fun u : A => valuePattern u.val)

theorem actualValuePatterns_finite {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) :
    (actualValuePatterns A).Finite := (native_finite_value_patterns_iff A).mp hA

def valuePatternWeights {n : ℕ} (p : Fin n → WithTop ℚ) : Fin n → ℚ := fun i => (p i).untopD 0

theorem patternPiece_rationalSupport {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) (p : Fin n → WithTop ℚ) :
    RationalFrameSupport (valuePatternWeights p) (patternPiece A p) := by
  intro r hr i
  have hp := (patternPiece_mem_iff A p r).mp hr
  by_cases hz : taggedRVEquiv (r i) = none
  · exact Or.inl hz
  · right
    have hpi : p i ≠ ⊤ := by
      intro he
      exact hz ((value_eq_top_iff _).mp ((congrFun hp.2 i).trans he))
    have he : (((p i).untopD 0 : ℚ) : WithTop ℚ) = p i := by
      cases h : p i with
      | top => exact (hpi h).elim
      | coe q => simp
    exact (congrFun hp.2 i).trans he.symm

def valuePatternObject {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) (p : Fin n → WithTop ℚ) :
    DiagonalConstructible.Object := framedObject (valuePatternWeights p) (patternPiece A p)

def valuePatternClass {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) (p : Fin n → WithTop ℚ) :
    DiagonalConstructible.Ring := DiagonalConstructible.objectClass (valuePatternObject A p)

theorem valuePatternClass_zero {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) (p : Fin n → WithTop ℚ)
    (hp : p ∉ actualValuePatterns A) : valuePatternClass A p = 0 := by
  apply DiagonalConstructible.objectClass_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hm := (patternPiece_mem_iff A p (rationalFrame (valuePatternWeights p) x)).mp hx
  exact hp ⟨⟨_, hm.1⟩, hm.2⟩

def forwardRESValue {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) : DiagonalConstructible.Ring :=
  ∑ p ∈ (actualValuePatterns_finite A hA).toFinset, valuePatternClass A p

theorem forwardRESValue_eq_sum {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (s : Finset (Fin n → WithTop ℚ)) (hs : actualValuePatterns A ⊆ (s : Set _)) :
    forwardRESValue A hA = ∑ p ∈ s, valuePatternClass A p := by
  apply Finset.sum_subset
  · intro p hp
    exact hs ((actualValuePatterns_finite A hA).mem_toFinset.mp hp)
  · intro p _ hp
    exact valuePatternClass_zero A p (by
      intro he
      exact hp ((actualValuePatterns_finite A hA).mem_toFinset.mpr he))

theorem valuePatternClass_congr {n : ℕ}
    (A B : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (he : A.carrier = B.carrier) (p : Fin n → WithTop ℚ) :
    valuePatternClass A p = valuePatternClass B p := by
  have hab : A = B := by cases A; cases B; cases he; rfl
  subst B
  rfl

theorem forwardRESValue_congr {n : ℕ}
    (A B : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (he : A.carrier = B.carrier) : forwardRESValue A hA = forwardRESValue B hB := by
  have hab : A = B := by cases A; cases B; cases he; rfl
  subst B
  rfl

end DiamondIntegral.Section5.PuiseuxOriginal
