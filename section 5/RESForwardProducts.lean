import «section 5».RESForwardBijections
import «section 5».RESSetOperations

/-! The forward finite-pattern comparison preserves the actual native
cartesian product, including every zero stratum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
local instance resForwardProductsStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem valuePattern_eq_append_iff {n m : ℕ} (r : Fin (n + m) → CanonicalRV.RVSort Carrier)
    (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    valuePattern r = Fin.append p q ↔
      valuePattern (fun i => r (Fin.castAdd m i)) = p ∧
      valuePattern (fun i => r (Fin.natAdd n i)) = q := by
  constructor
  · intro he
    constructor
    · funext i
      simpa only [valuePattern, Fin.append_left] using congrFun he (Fin.castAdd m i)
    · funext i
      simpa only [valuePattern, Fin.append_right] using congrFun he (Fin.natAdd n i)
  · rintro ⟨hp, hq⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [valuePattern, Fin.append_left] using congrFun hp j
    · simpa only [valuePattern, Fin.append_right] using congrFun hq j

theorem valuePatternObject_product {n m : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    valuePatternObject (resSetProduct canonicalInterpret_isCanonical A B hA hB) (Fin.append p q) =
      DiagonalConstructible.product (valuePatternObject A p) (valuePatternObject B q) := by
  let P := resSetProduct canonicalInterpret_isCanonical A B hA hB
  have hw : valuePatternWeights (Fin.append p q) = Fin.append (valuePatternWeights p) (valuePatternWeights q) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [valuePatternWeights]
  have hd : rationalFramedSet (valuePatternWeights (Fin.append p q)) (patternPiece P (Fin.append p q)) =
      tupleProductSet (rationalFramedSet (valuePatternWeights p) (patternPiece A p))
        (rationalFramedSet (valuePatternWeights q) (patternPiece B q)) := by
    ext x
    let r := rationalFrame (valuePatternWeights (Fin.append p q)) x
    have hl : (fun i => r (Fin.castAdd m i)) = rationalFrame (valuePatternWeights p) (fun i => x (Fin.castAdd m i)) := by
      funext i
      simp [r, rationalFrame, valuePatternWeights]
    have hr : (fun i => r (Fin.natAdd n i)) = rationalFrame (valuePatternWeights q) (fun i => x (Fin.natAdd n i)) := by
      funext i
      simp [r, rationalFrame, valuePatternWeights]
    change r ∈ (patternPiece P (Fin.append p q)).carrier ↔ _
    rw [patternPiece_mem_iff, resSetProduct_mem]
    change ((_ ∧ _) ∧ valuePattern r = Fin.append p q) ↔ _
    rw [valuePattern_eq_append_iff, hl, hr]
    change (_ ∧ _) ∧ (_ ∧ _) ↔
      rationalFrame (valuePatternWeights p) (fun i => x (Fin.castAdd m i)) ∈ (patternPiece A p).carrier ∧
      rationalFrame (valuePatternWeights q) (fun i => x (Fin.natAdd n i)) ∈ (patternPiece B q).carrier
    rw [patternPiece_mem_iff, patternPiece_mem_iff]
    tauto
  change DiagonalConstructible.Object.mk (n + m) _ _ _ _ = DiagonalConstructible.Object.mk (n + m) _ _ _ _
  congr 1

theorem forwardRESValue_product {n m : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite) :
    forwardRESValue (resSetProduct canonicalInterpret_isCanonical A B hA hB)
      (originalDomain_finite_values _ _) = forwardRESValue A hA * forwardRESValue B hB := by
  let P := resSetProduct canonicalInterpret_isCanonical A B hA hB
  let s := (actualValuePatterns_finite A hA).toFinset
  let t := (actualValuePatterns_finite B hB).toFinset
  let append : ((Fin n → WithTop ℚ) × (Fin m → WithTop ℚ)) → (Fin (n + m) → WithTop ℚ) :=
    fun pq => Fin.append pq.1 pq.2
  have hs : actualValuePatterns P ⊆ (↑((s ×ˢ t).image append) : Set _) := by
    rintro p ⟨u, rfl⟩
    have hu := (resSetProduct_mem canonicalInterpret_isCanonical A B hA hB u.val).mp u.property
    let a : A := ⟨fun i => u.val (Fin.castAdd m i), hu.1⟩
    let b : B := ⟨fun i => u.val (Fin.natAdd n i), hu.2⟩
    refine Finset.mem_image.mpr ⟨(valuePattern a.val, valuePattern b.val),
      Finset.mem_product.mpr ⟨(actualValuePatterns_finite A hA).mem_toFinset.mpr ⟨a, rfl⟩,
        (actualValuePatterns_finite B hB).mem_toFinset.mpr ⟨b, rfl⟩⟩, ?_⟩
    exact ((valuePattern_eq_append_iff u.val _ _).mpr ⟨rfl, rfl⟩).symm
  have hi : Function.Injective append := by
    intro x y he
    apply Prod.ext
    · funext i
      simpa only [append, Fin.append_left] using congrFun he (Fin.castAdd m i)
    · funext i
      simpa only [append, Fin.append_right] using congrFun he (Fin.natAdd n i)
  rw [forwardRESValue_eq_sum P _ _ hs, Finset.sum_image (fun _ _ _ _ he => hi he), Finset.sum_product]
  change (∑ p ∈ s, ∑ q ∈ t, valuePatternClass P (Fin.append p q)) = _
  have hpq (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
      valuePatternClass P (Fin.append p q) = valuePatternClass A p * valuePatternClass B q := by
    change DiagonalConstructible.objectClass (valuePatternObject P (Fin.append p q)) = _
    rw [valuePatternObject_product, DiagonalConstructible.objectClass_product]
    rfl
  simp_rw [hpq]
  exact (Finset.sum_mul_sum s t (valuePatternClass A) (valuePatternClass B)).symm

end DiamondIntegral.Section5.PuiseuxOriginal
