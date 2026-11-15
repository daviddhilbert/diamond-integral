import «section 5».RESFiniteWitness

/-! Native positive graded RES elements have finite actual-object
representatives. Equality of such families gives actual tagged RES
bijections in every degree, over exactly the original parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

abbrev GradedObject := Σ k, GammaGroundRESObject hc B k

def positiveFamilyClass (L : List (GradedObject hc B)) : GammaGroundRESDirectSum hc B :=
  (L.map (fun U => gammaGroundRESDirectSumClass U.2)).sum

theorem positiveFamilyClass_append (L R : List (GradedObject hc B)) :
    positiveFamilyClass hc B (L ++ R) = positiveFamilyClass hc B L + positiveFamilyClass hc B R := by
  simp only [positiveFamilyClass, List.map_append, List.sum_append]

theorem positiveFamilyClass_cons (U : GradedObject hc B) (L : List (GradedObject hc B)) :
    positiveFamilyClass hc B (U :: L) = gammaGroundRESDirectSumClass U.2 + positiveFamilyClass hc B L := by
  simp only [positiveFamilyClass, List.map_cons, List.sum_cons]

def gradedObjectProduct (U V : GradedObject hc B) : GradedObject hc B :=
  ⟨U.1 + V.1, U.2.product V.2⟩

def positiveFamilyProduct (L R : List (GradedObject hc B)) : List (GradedObject hc B) :=
  L.flatMap (fun U => R.map (gradedObjectProduct hc B U))

theorem positiveFamilyClass_product_map (U : GradedObject hc B) (R : List (GradedObject hc B)) :
    positiveFamilyClass hc B (R.map (gradedObjectProduct hc B U)) =
      gammaGroundRESDirectSumClass U.2 * positiveFamilyClass hc B R := by
  induction R with
  | nil => simp [positiveFamilyClass]
  | cons V R ih =>
    rw [List.map_cons, positiveFamilyClass_cons, positiveFamilyClass_cons, ih, mul_add]
    exact congrArg (fun x => x + gammaGroundRESDirectSumClass U.2 * positiveFamilyClass hc B R)
      (gammaGroundRESDirectSumClass_product U.2 V.2)

theorem positiveFamilyClass_product (L R : List (GradedObject hc B)) :
    positiveFamilyClass hc B (positiveFamilyProduct hc B L R) =
      positiveFamilyClass hc B L * positiveFamilyClass hc B R := by
  induction L with
  | nil => simp [positiveFamilyProduct, positiveFamilyClass]
  | cons U L ih =>
    change positiveFamilyClass hc B ((R.map (gradedObjectProduct hc B U)) ++
      positiveFamilyProduct hc B L R) = _
    rw [positiveFamilyClass_append, positiveFamilyClass_product_map, ih,
      positiveFamilyClass_cons, add_mul]

theorem positive_family_representative (a : GammaGroundRESDirectSum hc B) :
    ∃ L : List (GradedObject hc B), positiveFamilyClass hc B L = a := by
  induction a using DirectSum.induction_on with
  | zero => exact ⟨[], rfl⟩
  | of k a =>
    refine ⟨[⟨k, gammaGroundRESRepresentative a⟩], ?_⟩
    simp [positiveFamilyClass, gammaGroundRESDirectSumClass]
  | add a b ha hb =>
    obtain ⟨L, hL⟩ := ha
    obtain ⟨R, hR⟩ := hb
    exact ⟨L ++ R, by rw [positiveFamilyClass_append, hL, hR]⟩

def positiveFamilyAtDegree (k : ℕ) : List (GradedObject hc B) → GammaGroundRESObject hc B k
  | [] => GammaGroundRESObject.empty hc B k
  | U :: L => if h : U.1 = k then
      (Eq.mp (congrArg (GammaGroundRESObject hc B) h) U.2).coprod (positiveFamilyAtDegree k L)
    else positiveFamilyAtDegree k L

theorem positiveFamilyAtDegree_class (k : ℕ) (L : List (GradedObject hc B)) :
    gammaGroundRESClass (positiveFamilyAtDegree hc B k L) = positiveFamilyClass hc B L k := by
  induction L with
  | nil => simp [positiveFamilyAtDegree, positiveFamilyClass]
  | cons U L ih =>
    obtain ⟨l, U⟩ := U
    rw [positiveFamilyClass_cons]
    by_cases h : l = k
    · subst l
      simp [positiveFamilyAtDegree, gammaGroundRESClass_coprod,
        gammaGroundRESDirectSumClass, DirectSum.of_apply, ih]
    · simp [positiveFamilyAtDegree, h, gammaGroundRESDirectSumClass,
        DirectSum.of_apply, ih]

theorem positive_family_equality_iff_bijections (L R : List (GradedObject hc B)) :
    positiveFamilyClass hc B L = positiveFamilyClass hc B R ↔
      ∀ k, Nonempty (positiveFamilyAtDegree hc B k L ≅ positiveFamilyAtDegree hc B k R) := by
  constructor
  · intro he k
    apply gammaGroundRESClass_eq_iff_iso.mp
    rw [positiveFamilyAtDegree_class, positiveFamilyAtDegree_class, he]
  · intro h
    apply DFinsupp.ext
    intro k
    rw [← positiveFamilyAtDegree_class, ← positiveFamilyAtDegree_class]
    exact gammaGroundRESClass_eq_iff_iso.mpr (h k)

def positiveFamilyDegrees (L : List (GradedObject hc B)) : Finset ℕ :=
  (L.map (fun U => U.1)).toFinset

theorem positiveFamilyAtDegree_eq_empty (k : ℕ) (L : List (GradedObject hc B))
    (hk : k ∉ positiveFamilyDegrees hc B L) :
    positiveFamilyAtDegree hc B k L = GammaGroundRESObject.empty hc B k := by
  induction L with
  | nil => rfl
  | cons U L ih =>
    have hU : U.1 ≠ k := by
      intro he
      apply hk
      simp [positiveFamilyDegrees, he]
    have hL : k ∉ positiveFamilyDegrees hc B L := by
      intro h
      apply hk
      simp only [positiveFamilyDegrees, List.map_cons, List.toFinset_cons, Finset.mem_insert] at h ⊢
      exact Or.inr h
    simpa only [positiveFamilyAtDegree, dif_neg hU] using ih hL

theorem positive_family_equality_iff_finite_bijections
    (L R : List (GradedObject hc B)) (N : ℕ)
    (hL : ∀ k ∈ positiveFamilyDegrees hc B L, k < N)
    (hR : ∀ k ∈ positiveFamilyDegrees hc B R, k < N) :
    positiveFamilyClass hc B L = positiveFamilyClass hc B R ↔
      ∀ k : Fin N, Nonempty (positiveFamilyAtDegree hc B k.val L ≅ positiveFamilyAtDegree hc B k.val R) := by
  rw [positive_family_equality_iff_bijections]
  constructor
  · exact fun h k => h k.val
  · intro h k
    by_cases hk : k < N
    · exact h ⟨k, hk⟩
    · have hLk : k ∉ positiveFamilyDegrees hc B L := fun hmem => hk (hL k hmem)
      have hRk : k ∉ positiveFamilyDegrees hc B R := fun hmem => hk (hR k hmem)
      rw [positiveFamilyAtDegree_eq_empty hc B k L hLk, positiveFamilyAtDegree_eq_empty hc B k R hRk]
      exact ⟨Iso.refl _⟩

def positiveFamilyBound (L R : List (GradedObject hc B)) : ℕ :=
  (positiveFamilyDegrees hc B L ∪ positiveFamilyDegrees hc B R).sup id + 1

theorem positive_family_finite_bijections (L R : List (GradedObject hc B))
    (he : positiveFamilyClass hc B L = positiveFamilyClass hc B R) :
    ∀ k : Fin (positiveFamilyBound hc B L R),
      Nonempty (positiveFamilyAtDegree hc B k.val L ≅ positiveFamilyAtDegree hc B k.val R) :=
  fun k => (positive_family_equality_iff_bijections hc B L R).mp he k.val

theorem positiveFamilyBound_left (L R : List (GradedObject hc B))
    (k : ℕ) (hk : k ∈ positiveFamilyDegrees hc B L) : k < positiveFamilyBound hc B L R :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_union_left _ hk))

theorem positiveFamilyBound_right (L R : List (GradedObject hc B))
    (k : ℕ) (hk : k ∈ positiveFamilyDegrees hc B R) : k < positiveFamilyBound hc B L R :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_union_right _ hk))

end DiamondIntegral.Section5.RESFiniteWitness
