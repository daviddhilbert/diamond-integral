import «section 5».RESRawComparisonMaps
import «section 5».RESFinitePartitions

/-! Both composition identities for the raw comparison, on all actual
finite-value original RV domains with zeros and arbitrary finite labels.
The geometric variety bridge and the further quotient ideal remain separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance resRawComparisonEquivalenceStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem patternPiece_finite_values {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) (p : Fin n → WithTop ℚ) :
    (Set.range (fun u : patternPiece A p => fun i => Values.vrv (u.val i))).Finite :=
  finite_native_values_of_frameSupport _ _ _ (patternPiece_support A p)

theorem canonical_pattern_partition {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (s : Finset (Fin n → WithTop ℚ)) (hs : actualValuePatterns A ⊆ (s : Set _)) :
    Pairwise (fun p q : s => Disjoint (patternPiece A p.val).carrier (patternPiece A q.val).carrier) ∧
      ∀ r, r ∈ A.carrier ↔ ∃ p : s, r ∈ (patternPiece A p.val).carrier := by
  constructor
  · intro p q hpq
    apply Set.disjoint_left.mpr
    intro r hp hq
    have hpr := (patternPiece_mem_iff A p.val r).mp hp
    have hqr := (patternPiece_mem_iff A q.val r).mp hq
    exact hpq (Subtype.ext (hpr.2.symm.trans hqr.2))
  · intro r
    constructor
    · intro hr
      let p := valuePattern r
      have hp : p ∈ s := hs ⟨⟨r, hr⟩, rfl⟩
      exact ⟨⟨p, hp⟩, (patternPiece_mem_iff A p r).mpr ⟨hr, rfl⟩⟩
    · rintro ⟨p, hp⟩
      exact ((patternPiece_mem_iff A p.val r).mp hp).1

theorem rational_descent_framed {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : RationalFrameSupport q A) :
    (rationalDescendedSet q (rationalFramedSet q A) (framedObject q A).definable).carrier = A.carrier := by
  ext r
  have hi : RationalInvariant q (rationalFramedSet q A) := (framedObject q A).invariant
  rw [rationalDescent_mem_image q (rationalFramedSet q A) _ hi r]
  constructor
  · rintro ⟨x, hx, he⟩
    exact he ▸ hx
  · intro hr
    let u : A := ⟨r, hr⟩
    let x := (rationalFrameEquiv q A hA) u
    exact ⟨x.val, x.property, rationalFrame_reconstruction q A hA u⟩

theorem diagonalToRES_framedObject {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hs : RationalFrameSupport q A) :
    diagonalToRES (DiagonalConstructible.objectClass (framedObject q A)) =
      resSetClass canonicalInterpret_isCanonical A hA := by
  rw [diagonalToRES_objectClass]
  exact resSetClass_congr canonicalInterpret_isCanonical _ A _ hA (rational_descent_framed q A hs)

theorem diagonalToRES_forwardRESValue {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) :
    diagonalToRES (forwardRESValue A hA) = resSetClass canonicalInterpret_isCanonical A hA := by
  let s := (actualValuePatterns_finite A hA).toFinset
  have hs : actualValuePatterns A ⊆ (s : Set _) := fun _ hp => (actualValuePatterns_finite A hA).mem_toFinset.mpr hp
  obtain ⟨hd, hc⟩ := canonical_pattern_partition A s hs
  have hp := resSetClass_finite_partition canonicalInterpret_isCanonical A hA
    (fun p : s => patternPiece A p.val) (fun p => patternPiece_finite_values A p.val) hd hc
  have hsum := hp.trans (Finset.sum_coe_sort s (fun p =>
    resSetClass canonicalInterpret_isCanonical (patternPiece A p) (patternPiece_finite_values A p)))
  rw [forwardRESValue_eq_sum A hA s hs, map_sum]
  exact (Finset.sum_congr rfl (fun p _ =>
    diagonalToRES_framedObject (valuePatternWeights p) (patternPiece A p)
      (patternPiece_finite_values A p) (patternPiece_rationalSupport A p))).trans hsum.symm

theorem forwardRESValue_of_support {n : ℕ} (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hS : RationalFrameSupport q A) :
    forwardRESValue A hA = DiagonalConstructible.objectClass (framedObject q A) := by
  let s := (actualValuePatterns_finite A hA).toFinset
  have hs : actualValuePatterns A ⊆ (s : Set _) := fun _ hp => (actualValuePatterns_finite A hA).mem_toFinset.mpr hp
  obtain ⟨hd, hc⟩ := canonical_pattern_partition A s hs
  have hp := framedObject_class_finite_partition q A (fun p : s => patternPiece A p.val) hd hc
  have hsum := hp.trans (Finset.sum_coe_sort s (fun p =>
    DiagonalConstructible.objectClass (framedObject q (patternPiece A p))))
  rw [forwardRESValue_eq_sum A hA s hs]
  apply Eq.trans _ hsum.symm
  apply Finset.sum_congr rfl
  intro p _
  exact (DiagonalConstructible.objectClass_iso (rationalFramedIso q (valuePatternWeights p)
    (patternPiece A p) (patternPiece A p) (fun r hr => hS r hr.1)
    (patternPiece_rationalSupport A p) (DefinableBijection.id _))).symm

theorem rationalDescendedSet_support (X : DiagonalConstructible.Object) :
    RationalFrameSupport X.weights (rationalDescendedSet X.weights X.domain X.definable) := by
  intro r hr
  obtain ⟨x, _, rfl⟩ := (rationalDescent_mem_image X.weights X.domain X.definable X.invariant r).mp hr
  intro i
  by_cases hx : x i = 0
  · left
    exact dif_pos hx
  · right
    change value (linePoint (X.weights i) (x i)) = _
    rw [linePoint, dif_neg hx]
    rfl

theorem resToDiagonal_diagonalRESClass (X : DiagonalConstructible.Object) :
    resToDiagonal (diagonalRESClass X) = DiagonalConstructible.objectClass X := by
  change resToDiagonal (resSetClass canonicalInterpret_isCanonical
    (rationalDescendedSet X.weights X.domain X.definable) _) = _
  rw [resToDiagonal_resSetClass, forwardRESValue_of_support _ _ _ (rationalDescendedSet_support X)]
  exact DiagonalConstructible.setClass_congr X.weights _ X.domain _ _ X.definable X.invariant
    (rational_framed_descent X)

theorem resToDiagonal_diagonalToRES : resToDiagonal.comp diagonalToRES = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro X
  change resToDiagonal (diagonalToRES (DiagonalConstructible.objectClass X)) = DiagonalConstructible.objectClass X
  rw [diagonalToRES_objectClass, resToDiagonal_diagonalRESClass]

theorem diagonalToRES_nativeForwardValue {k : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k) :
    diagonalToRES (nativeForwardValue U) = nativeUngradedClass canonicalInterpret_isCanonical U :=
  (diagonalToRES_forwardRESValue _ _).trans (resSetClass_originalDomain _ U)

theorem diagonalToRES_resToDiagonal : diagonalToRES.comp resToDiagonal = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RESOrdinaryRing.hom_ext originalPuiseuxGround
  intro k a
  change diagonalToRES (resToDiagonal (RESDimensionFreeRing.objectClass a)) = RESDimensionFreeRing.objectClass a
  rw [resToDiagonal_objectClass, diagonalToRES_nativeForwardValue]
  exact RESDimensionFreeRing.objectClass_iso _ _
    (RVUnderlyingIsomorphisms.ofFixed (Section3RVRoundtripBridge.chart_native a.toChart))

def rawRESComparison : RESDimensionFreeRing.Ring originalPuiseuxGround ≃+* DiagonalConstructible.Ring :=
  RingEquiv.ofRingHom resToDiagonal diagonalToRES resToDiagonal_diagonalToRES diagonalToRES_resToDiagonal

theorem rawRESComparison_resSetClass {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) :
    rawRESComparison (resSetClass canonicalInterpret_isCanonical A hA) = forwardRESValue A hA :=
  resToDiagonal_resSetClass A hA

end DiamondIntegral.Section5.PuiseuxOriginal
