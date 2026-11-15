import «section 5».DescendedFiniteValues

/-! Individual rational value patterns are original-Laurent-base definable,
with all zero positions encoded by the existing absorbing RV element. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance valuePatternSetsStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

def complexZeroPattern {n : ℕ} (Z : Set (Fin n)) : Set (Fin n → ℂ) :=
  {x | ∀ i, x i = 0 ↔ i ∈ Z}

theorem complexZeroPattern_definable {n : ℕ} (Z : Set (Fin n)) :
    (Set.univ : Set ℂ).Definable Language.ring (complexZeroPattern Z) := by
  have hi (i : Fin n) : (Set.univ : Set ℂ).Definable Language.ring
      {x : Fin n → ℂ | x i = 0 ↔ i ∈ Z} := by
    have hz := (Set.DefinableFun.proj Language.ring (A := (Set.univ : Set ℂ)) (i := i)).ofPred_eq_const
      (Set.mem_univ (0 : ℂ))
    by_cases h : i ∈ Z
    · simpa only [h, iff_true] using hz
    · simpa only [h, iff_false, Set.compl_setOf] using hz.compl
  change (Set.univ : Set ℂ).Definable Language.ring {x | ∀ i, x i = 0 ↔ i ∈ Z}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite hi

theorem complexZeroPattern_invariant {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (Z : Set (Fin n)) :
    FiniteInvariant N a (complexZeroPattern Z) := by
  intro ζ x
  change (∀ i, (((ζ.val ^ a i : ℂˣ) : ℂ) * x i) = 0 ↔ i ∈ Z) ↔
    ∀ i, x i = 0 ↔ i ∈ Z
  have hc (i : Fin n) : (((ζ.val ^ a i : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _
  simp only [mul_eq_zero, hc, false_or]

theorem linePoint_value (q : ℚ) (c : ℂ) :
    value (linePoint q c) = if c = 0 then ⊤ else (q : WithTop ℚ) := by
  by_cases hc : c = 0 <;> simp only [linePoint, hc, ↓reduceDIte, ↓reduceIte, value] <;> rfl

theorem value_eq_top_iff (r : RV) : value r = ⊤ ↔ r = none := by
  cases r <;> simp [value]

theorem lineCoefficient_eq_zero_iff (r : RV) : lineCoefficient r = 0 ↔ r = none := by
  cases r <;> simp [lineCoefficient, Units.ne_zero]

def originalValuePattern {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (Z : Set (Fin n)) :
    DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c} :=
  descendedOriginalSet N a (complexZeroPattern Z) (complexZeroPattern_definable Z)

theorem originalValuePattern_values {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (Z : Set (Fin n))
    (r : originalValuePattern N a Z) (i : Fin n) :
    value (taggedRVEquiv (r.val i)) = if i ∈ Z then ⊤ else (((a i : ℚ) / (N : ℕ) : ℚ) : WithTop ℚ) := by
  have hr := r.property
  change r.val ∈ Set.range (fun u : descentSource N (complexZeroPattern Z)
    (complexZeroPattern_definable Z) => (descentMonomialMap N a _ _ u).val) at hr
  rw [descentMonomialMap_range] at hr
  obtain ⟨root, x, hx, he⟩ := hr
  have hi := congrFun he i
  rw [hi]
  change value (linePoint _ (((root.val.2 ^ a i : ℂˣ) : ℂ) * x i)) = _
  rw [linePoint_value]
  have hz : (((root.val.2 ^ a i : ℂˣ) : ℂ) * x i) = 0 ↔ i ∈ Z :=
    (mul_eq_zero.trans (or_iff_right (Units.ne_zero _))).trans (hx i)
  simp only [hz]

theorem originalValuePattern_mem_iff {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (Z : Set (Fin n))
    (r : Fin n → CanonicalRV.RVSort Carrier) :
    r ∈ (originalValuePattern N a Z).carrier ↔
      ∀ i, value (taggedRVEquiv (r i)) =
        if i ∈ Z then ⊤ else (((a i : ℚ) / (N : ℕ) : ℚ) : WithTop ℚ) := by
  constructor
  · intro hr i
    exact originalValuePattern_values N a Z ⟨r, hr⟩ i
  · intro hr
    let x : Fin n → ℂ := fun i => lineCoefficient (taggedRVEquiv (r i))
    have hzero (i : Fin n) : taggedRVEquiv (r i) = none ↔ i ∈ Z := by
      rw [← value_eq_top_iff, hr i]
      by_cases h : i ∈ Z <;> simp [h]
    have hx : x ∈ complexZeroPattern Z := fun i =>
      (lineCoefficient_eq_zero_iff _).trans (hzero i)
    have hreconstruct : (fun i => rvTag (finiteFrame N a x i)) = r := by
      funext i
      have hline : taggedRVEquiv (r i) = none ∨
          value (taggedRVEquiv (r i)) = (((a i : ℚ) / (N : ℕ) : ℚ) : WithTop ℚ) := by
        by_cases h : i ∈ Z
        · exact Or.inl ((hzero i).mpr h)
        · exact Or.inr (by simpa only [h, ↓reduceIte] using hr i)
      have he := linePoint_coefficient ((a i : ℚ) / (N : ℕ))
        (⟨taggedRVEquiv (r i), hline⟩ : ValueLine _)
      change rvTag (linePoint _ (lineCoefficient (taggedRVEquiv (r i)))) = r i
      rw [he]
      exact taggedRVEquiv.symm_apply_apply _
    change r ∈ Set.range (fun u : descentSource N (complexZeroPattern Z)
      (complexZeroPattern_definable Z) => (descentMonomialMap N a _ _ u).val)
    rw [descentMonomialMap_range]
    refine ⟨rootOfPhase N 1, x, hx, ?_⟩
    simp only [frameAtRoot, rootOfPhase, OneMemClass.coe_one, weightedAction_one]
    exact hreconstruct.symm

end DiamondIntegral.Section5.PuiseuxOriginal
