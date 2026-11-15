import «section 5».RESForwardValue

/-! The forward finite-pattern value respects actual original-base
scissors, with finite supports chosen intrinsically from the source domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance resForwardScissorsStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem framedObject_class_scissor {n : ℕ} (q : Fin n → ℚ)
    (A D E : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hd : D.carrier ⊆ A.carrier) (he : E.carrier = A.carrier \ D.carrier) :
    DiagonalConstructible.objectClass (framedObject q A) =
      DiagonalConstructible.objectClass (framedObject q D) +
      DiagonalConstructible.objectClass (framedObject q E) := by
  let XA := framedObject q A
  let XD := framedObject q D
  let XE := framedObject q E
  have h := DiagonalConstructible.objectClass_scissor XA XD.domain XD.definable XD.invariant
  have hi : (DiagonalConstructible.cut XA XD.domain XD.definable XD.invariant).domain = XD.domain := by
    ext x
    change (rationalFrame q x ∈ A.carrier ∧ rationalFrame q x ∈ D.carrier) ↔ rationalFrame q x ∈ D.carrier
    exact ⟨And.right, fun hx => ⟨hd hx, hx⟩⟩
  have ho : (DiagonalConstructible.outside XA XD.domain XD.definable XD.invariant).domain = XE.domain := by
    ext x
    change (rationalFrame q x ∈ A.carrier ∧ rationalFrame q x ∉ D.carrier) ↔ rationalFrame q x ∈ E.carrier
    rw [he]
    rfl
  have hic : DiagonalConstructible.objectClass (DiagonalConstructible.cut XA XD.domain XD.definable XD.invariant) =
      DiagonalConstructible.objectClass XD := DiagonalConstructible.setClass_congr q _ _ _ _ _ _ hi
  have hoc : DiagonalConstructible.objectClass (DiagonalConstructible.outside XA XD.domain XD.definable XD.invariant) =
      DiagonalConstructible.objectClass XE := DiagonalConstructible.setClass_congr q _ _ _ _ _ _ ho
  exact h.trans (congrArg₂ (· + ·) hic hoc)

theorem valuePatternClass_scissor {n : ℕ}
    (A D E : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hd : D.carrier ⊆ A.carrier) (he : E.carrier = A.carrier \ D.carrier)
    (p : Fin n → WithTop ℚ) : valuePatternClass A p = valuePatternClass D p + valuePatternClass E p := by
  apply framedObject_class_scissor
  · intro r hr
    have hm := (patternPiece_mem_iff D p r).mp hr
    exact (patternPiece_mem_iff A p r).mpr ⟨hd hm.1, hm.2⟩
  · ext r
    rw [Set.mem_sdiff, patternPiece_mem_iff, patternPiece_mem_iff, patternPiece_mem_iff, he]
    simp only [Set.mem_sdiff]
    tauto

theorem actualValuePatterns_mono {n : ℕ}
    (A B : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (h : A.carrier ⊆ B.carrier) : actualValuePatterns A ⊆ actualValuePatterns B := by
  rintro p ⟨u, rfl⟩
  exact ⟨⟨u.val, h u.property⟩, rfl⟩

theorem forwardRESValue_scissor {n : ℕ}
    (A D E : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hD : (Set.range (fun u : D => fun i => Values.vrv (u.val i))).Finite)
    (hE : (Set.range (fun u : E => fun i => Values.vrv (u.val i))).Finite)
    (hd : D.carrier ⊆ A.carrier) (he : E.carrier = A.carrier \ D.carrier) :
    forwardRESValue A hA = forwardRESValue D hD + forwardRESValue E hE := by
  let s := (actualValuePatterns_finite A hA).toFinset
  have hs : actualValuePatterns A ⊆ (s : Set _) := fun _ hp => (actualValuePatterns_finite A hA).mem_toFinset.mpr hp
  have hds : actualValuePatterns D ⊆ (s : Set _) := (actualValuePatterns_mono D A hd).trans hs
  have hes : actualValuePatterns E ⊆ (s : Set _) :=
    (actualValuePatterns_mono E A (by rw [he]; exact Set.sdiff_subset)).trans hs
  rw [forwardRESValue_eq_sum A hA s hs, forwardRESValue_eq_sum D hD s hds,
    forwardRESValue_eq_sum E hE s hes, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p _ => valuePatternClass_scissor A D E hd he p)

theorem forwardRESValue_empty {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (he : A.carrier = ∅) : forwardRESValue A hA = 0 := by
  rw [forwardRESValue_eq_sum A hA ∅ (by rintro p ⟨u, _⟩; simpa only [he, Set.mem_empty_iff_false] using u.property)]
  exact Finset.sum_empty

end DiamondIntegral.Section5.PuiseuxOriginal
