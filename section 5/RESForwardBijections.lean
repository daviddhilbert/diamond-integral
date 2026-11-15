import «section 5».RESBijectionSlices

/-! The forward finite-pattern value is invariant under every actual
original-base definable bijection, including changes of tuple arity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
local instance resForwardBijectionsStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem framedObject_class_finite_partition {n : ℕ} {I : Type} [Fintype I] (q : Fin n → ℚ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (D : I → DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hd : Pairwise (fun i j => Disjoint (D i).carrier (D j).carrier))
    (hc : ∀ r, r ∈ A.carrier ↔ ∃ i, r ∈ (D i).carrier) :
    DiagonalConstructible.objectClass (framedObject q A) =
      ∑ i, DiagonalConstructible.objectClass (framedObject q (D i)) := by
  apply DiagonalConstructible.finite_partition_class q (rationalFramedSet q A)
    (framedObject q A).definable (framedObject q A).invariant
    (fun i => rationalFramedSet q (D i)) (fun i => (framedObject q (D i)).definable)
    (fun i => (framedObject q (D i)).invariant)
  · intro i j hij
    exact Set.disjoint_left.mpr (fun _ hi hj => Set.disjoint_left.mp (hd hij) hi hj)
  · exact fun x => hc (rationalFrame q x)

theorem valuePatternClass_slice_sum {n m : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (f : Map A B) (p : Fin n → WithTop ℚ)
    (s : Finset (Fin m → WithTop ℚ)) (hs : actualValuePatterns B ⊆ (s : Set _)) :
    valuePatternClass A p = ∑ q ∈ s,
      DiagonalConstructible.objectClass (framedObject (valuePatternWeights p) (rvMapSlice f p q)) := by
  obtain ⟨hd, hc⟩ := rvMapSlice_partition f p s hs
  have he := framedObject_class_finite_partition (valuePatternWeights p) (patternPiece A p)
    (fun q : s => rvMapSlice f p q.val) hd hc
  exact he.trans (Finset.sum_coe_sort s (fun q =>
    DiagonalConstructible.objectClass (framedObject (valuePatternWeights p) (rvMapSlice f p q))))

theorem valuePatternClass_image_sum {n m : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (f : DefinableBijection A B) (q : Fin m → WithTop ℚ)
    (s : Finset (Fin n → WithTop ℚ)) (hs : actualValuePatterns A ⊆ (s : Set _)) :
    valuePatternClass B q = ∑ p ∈ s,
      DiagonalConstructible.objectClass (framedObject (valuePatternWeights q) (rvSliceImage f.map p q)) := by
  obtain ⟨hd, hc⟩ := rvSliceImage_partition f q s hs
  have he := framedObject_class_finite_partition (valuePatternWeights q) (patternPiece B q)
    (fun p : s => rvSliceImage f.map p.val q) hd hc
  exact he.trans (Finset.sum_coe_sort s (fun p =>
    DiagonalConstructible.objectClass (framedObject (valuePatternWeights q) (rvSliceImage f.map p q))))

theorem forwardRESValue_bijection {n m : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (f : DefinableBijection A B) : forwardRESValue A hA = forwardRESValue B hB := by
  let s := (actualValuePatterns_finite A hA).toFinset
  let t := (actualValuePatterns_finite B hB).toFinset
  have hs : actualValuePatterns A ⊆ (s : Set _) := fun _ hp => (actualValuePatterns_finite A hA).mem_toFinset.mpr hp
  have ht : actualValuePatterns B ⊆ (t : Set _) := fun _ hp => (actualValuePatterns_finite B hB).mem_toFinset.mpr hp
  calc
    forwardRESValue A hA = ∑ p ∈ s, valuePatternClass A p := forwardRESValue_eq_sum A hA s hs
    _ = ∑ p ∈ s, ∑ q ∈ t, DiagonalConstructible.objectClass
        (framedObject (valuePatternWeights p) (rvMapSlice f.map p q)) :=
      Finset.sum_congr rfl (fun p _ => valuePatternClass_slice_sum A B f.map p t ht)
    _ = ∑ p ∈ s, ∑ q ∈ t, DiagonalConstructible.objectClass
        (framedObject (valuePatternWeights q) (rvSliceImage f.map p q)) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact DiagonalConstructible.objectClass_iso
        (rationalFramedIso _ _ _ _ (rvMapSlice_support f.map p q) (rvSliceImage_support f.map p q)
          (rvSliceBijection f p q))
    _ = ∑ q ∈ t, ∑ p ∈ s, DiagonalConstructible.objectClass
        (framedObject (valuePatternWeights q) (rvSliceImage f.map p q)) := Finset.sum_comm
    _ = ∑ q ∈ t, valuePatternClass B q :=
      Finset.sum_congr rfl (fun q _ => (valuePatternClass_image_sum A B f q s hs).symm)
    _ = forwardRESValue B hB := (forwardRESValue_eq_sum B hB t ht).symm

end DiamondIntegral.Section5.PuiseuxOriginal
