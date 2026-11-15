import «section 5».PuiseuxRVBase
import CanonicalStructure

/-! The original RV-language structure on concrete complex Puiseux series.
The RV sort is the already proved normal form of the actual principal-unit
quotient. No section is named in the language. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section5

abbrev RV := Option (RationalRVUnits ℂ)
abbrev Carrier := PuiseuxSeries ℂ ⊕ RV

def rvNormalEquiv : RVCalc.RV (puiseuxValuation ℂ) ≃ RV :=
  _root_.Equiv.optionCongr (puiseuxRVUnitEquiv (k := ℂ)).toEquiv

def rvOfField (f : PuiseuxSeries ℂ) : RV := rvNormalEquiv (RVCalc.rv (puiseuxValuation ℂ) f)

def characterEquiv (χ : Multiplicative ℚ →* ℂˣ) : RationalRVUnits ℂ ≃* RationalRVUnits ℂ where
  toFun u := (u.1, χ u.1 * u.2)
  invFun u := (u.1, (χ u.1)⁻¹ * u.2)
  left_inv u := by ext <;> simp
  right_inv u := by ext <;> simp
  map_mul' u w := by ext <;> simp [map_mul, mul_mul_mul_comm]

def rvAction (η : CompatibleRoots ℂ) : RV ≃ RV :=
  _root_.Equiv.optionCongr (characterEquiv (compatibleRootCharacter η)).toEquiv

theorem rvAction_normal (η : CompatibleRoots ℂ) (r : RVCalc.RV (puiseuxValuation ℂ)) :
    rvAction η (rvNormalEquiv r) = rvNormalEquiv
      (valuedRVEquiv (puiseuxValuation ℂ) (puiseuxRootSystemAction η).toRingEquiv
        (puiseuxAutomorphism_valuation (puiseuxRootSystemAction η)) r) := by
  cases r with
  | none => rfl
  | some r =>
    change some _ = some _
    congr 1
    exact (puiseuxRVAction_coordinates η r).symm

theorem rvAction_rv (η : CompatibleRoots ℂ) (f : PuiseuxSeries ℂ) :
    rvAction η (rvOfField f) = rvOfField (puiseuxRootSystemAction η f) := by
  rw [rvOfField, rvAction_normal, valuedRVEquiv_rv]
  rfl

def rvMul : RV → RV → RV
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a * b)

def rvInv : RV → RV
  | none => none
  | some a => some a⁻¹

def value : RV → WithTop ℚ
  | none => ⊤
  | some a => a.1.toAdd

def inResidue : RV → Prop
  | none => True
  | some a => a.1 = 1

def residue : RV → ℂ
  | none => 0
  | some a => if a.1 = 1 then (a.2 : ℂ) else 0

def residueLift (c : ℂ) : RV := if hc : c = 0 then none else some (1, Units.mk0 c hc)

def kAdd (a b : RV) : RV :=
  if inResidue a ∧ inResidue b then residueLift (residue a + residue b) else none

def kNeg (a : RV) : RV := if inResidue a then residueLift (-residue a) else none

theorem rvAction_mul (η : CompatibleRoots ℂ) (a b : RV) :
    rvAction η (rvMul a b) = rvMul (rvAction η a) (rvAction η b) := by
  cases a <;> cases b <;> simp [rvMul, rvAction, _root_.Equiv.optionCongr]

theorem rvAction_inv (η : CompatibleRoots ℂ) (a : RV) :
    rvAction η (rvInv a) = rvInv (rvAction η a) := by
  cases a <;> simp [rvInv, rvAction, _root_.Equiv.optionCongr]

theorem rvAction_value (η : CompatibleRoots ℂ) (a : RV) : value (rvAction η a) = value a := by
  cases a <;> rfl

theorem rvAction_inResidue (η : CompatibleRoots ℂ) (a : RV) :
    inResidue (rvAction η a) ↔ inResidue a := by
  cases a <;> rfl

theorem rvAction_residue (η : CompatibleRoots ℂ) (a : RV) : residue (rvAction η a) = residue a := by
  cases a with
  | none => rfl
  | some u =>
    change (if u.1 = 1 then ((compatibleRootCharacter η u.1 * u.2 : ℂˣ) : ℂ) else 0) = _
    by_cases hu : u.1 = 1 <;> simp [residue, hu]

theorem rvAction_residueLift (η : CompatibleRoots ℂ) (c : ℂ) :
    rvAction η (residueLift c) = residueLift c := by
  by_cases hc : c = 0 <;> simp [residueLift, hc, rvAction, _root_.Equiv.optionCongr, characterEquiv]

theorem rvAction_kAdd (η : CompatibleRoots ℂ) (a b : RV) :
    rvAction η (kAdd a b) = kAdd (rvAction η a) (rvAction η b) := by
  simp only [kAdd, rvAction_inResidue, rvAction_residue]
  split_ifs
  · exact rvAction_residueLift η _
  · rfl

theorem rvAction_kNeg (η : CompatibleRoots ℂ) (a : RV) :
    rvAction η (kNeg a) = kNeg (rvAction η a) := by
  simp only [kNeg, rvAction_inResidue, rvAction_residue]
  split_ifs
  · exact rvAction_residueLift η _
  · rfl

def vfPart : Carrier → PuiseuxSeries ℂ
  | .inl f => f
  | .inr _ => 0

def rvPart : Carrier → RV
  | .inl _ => none
  | .inr r => r

def inVF : Carrier → Prop
  | .inl _ => True
  | .inr _ => False

def function : {n : ℕ} → Fn n → (Fin n → Carrier) → Carrier
  | _, .vfZero, _ => .inl 0
  | _, .vfOne, _ => .inl 1
  | _, .vfAdd, x => .inl (vfPart (x 0) + vfPart (x 1))
  | _, .vfNeg, x => .inl (-vfPart (x 0))
  | _, .vfMul, x => .inl (vfPart (x 0) * vfPart (x 1))
  | _, .rvZero, _ => .inr none
  | _, .rvOne, _ => .inr (some 1)
  | _, .rvMul, x => .inr (rvMul (rvPart (x 0)) (rvPart (x 1)))
  | _, .rvInv, x => .inr (rvInv (rvPart (x 0)))
  | _, .kAdd, x => .inr (kAdd (rvPart (x 0)) (rvPart (x 1)))
  | _, .kNeg, x => .inr (kNeg (rvPart (x 0)))
  | _, .rvMap, x => .inr (rvOfField (vfPart (x 0)))

def relation : {n : ℕ} → Rel n → (Fin n → Carrier) → Prop
  | _, .memVF, x => inVF (x 0)
  | _, .memRV, x => ¬ inVF (x 0)
  | _, .memUnits, x => ¬ inVF (x 0) ∧ value (rvPart (x 0)) = 0
  | _, .rvLe, x => ¬ inVF (x 0) ∧ ¬ inVF (x 1) ∧ value (rvPart (x 0)) ≤ value (rvPart (x 1))

@[instance_reducible] def interpret : LRV.Structure Carrier where
  funMap := function
  RelMap := relation

local instance rawStructure : LRV.Structure Carrier := interpret

def carrierAction (η : CompatibleRoots ℂ) : Carrier ≃ Carrier :=
  _root_.Equiv.sumCongr (puiseuxRootSystemAction η).toEquiv (rvAction η)

theorem carrierAction_vfPart (η : CompatibleRoots ℂ) (x : Carrier) :
    vfPart (carrierAction η x) = puiseuxRootSystemAction η (vfPart x) := by
  cases x <;> simp [carrierAction, vfPart]

theorem carrierAction_rvPart (η : CompatibleRoots ℂ) (x : Carrier) :
    rvPart (carrierAction η x) = rvAction η (rvPart x) := by cases x <;> rfl

theorem carrierAction_inVF (η : CompatibleRoots ℂ) (x : Carrier) :
    inVF (carrierAction η x) ↔ inVF x := by cases x <;> rfl

@[simp] theorem carrierAction_inl (η : CompatibleRoots ℂ) (f : PuiseuxSeries ℂ) :
    carrierAction η (Sum.inl f) = Sum.inl (puiseuxRootSystemAction η f) := rfl

@[simp] theorem carrierAction_inr (η : CompatibleRoots ℂ) (r : RV) :
    carrierAction η (Sum.inr r) = Sum.inr (rvAction η r) := rfl

def languageAction (η : CompatibleRoots ℂ) : Carrier ≃[LRV] Carrier where
  toEquiv := carrierAction η
  map_fun' f x := by
    change carrierAction η (function f x) = function f (carrierAction η ∘ x)
    cases f <;> simp only [interpret, function, Function.comp_apply,
      carrierAction_vfPart, carrierAction_rvPart, carrierAction_inl, carrierAction_inr]
    all_goals try rfl
    all_goals try exact congrArg Sum.inl (map_zero (puiseuxRootSystemAction η))
    all_goals try exact congrArg Sum.inl (map_one (puiseuxRootSystemAction η))
    all_goals try exact congrArg Sum.inl (map_add (puiseuxRootSystemAction η) _ _)
    all_goals try exact congrArg Sum.inl (map_mul (puiseuxRootSystemAction η) _ _)
    all_goals try exact congrArg Sum.inl (map_neg (puiseuxRootSystemAction η) _)
    all_goals try exact congrArg Sum.inr (congrArg Option.some (map_one (characterEquiv (compatibleRootCharacter η))))
    all_goals try exact congrArg Sum.inr (rvAction_mul η _ _)
    all_goals try exact congrArg Sum.inr (rvAction_inv η _)
    all_goals try exact congrArg Sum.inr (rvAction_kAdd η _ _)
    all_goals try exact congrArg Sum.inr (rvAction_kNeg η _)
    all_goals try exact congrArg Sum.inr (rvAction_rv η _)
  map_rel' r x := by
    change relation r (carrierAction η ∘ x) ↔ relation r x
    cases r <;> simp only [relation, Function.comp_apply, carrierAction_inVF,
      carrierAction_rvPart, rvAction_value]


theorem carrierAction_function (η : CompatibleRoots ℂ) {n : ℕ} (f : Fn n)
    (x : Fin n → Carrier) : carrierAction η (function f x) = function f (carrierAction η ∘ x) :=
  (languageAction η).map_fun f x

theorem carrierAction_relation (η : CompatibleRoots ℂ) {n : ℕ} (r : Rel n)
    (x : Fin n → Carrier) : relation r (carrierAction η ∘ x) ↔ relation r x :=
  (languageAction η).map_rel r x

/-- The concrete original-language structure with canonical off-sort values. -/
@[instance_reducible] def canonicalInterpret : LRV.Structure Carrier :=
  @CanonicalStructure.normalize Carrier interpret

theorem canonicalInterpret_isCanonical :
    @CanonicalStructure.IsCanonical Carrier canonicalInterpret :=
  @CanonicalStructure.normalize_isCanonical Carrier interpret

theorem carrierAction_sort (η : CompatibleRoots ℂ) (s : SortTag) (x : Carrier) :
    sortEval s (carrierAction η x) ↔ sortEval s x := by
  cases s
  · exact carrierAction_inVF η x
  · exact not_congr (carrierAction_inVF η x)

/-- The action also preserves the canonical totalization of the whole language. -/
def canonicalLanguageAction (η : CompatibleRoots ℂ) :
    @FirstOrder.Language.Equiv LRV Carrier Carrier canonicalInterpret canonicalInterpret := by
  letI : LRV.Structure Carrier := canonicalInterpret
  refine { toEquiv := carrierAction η, map_fun' := ?_, map_rel' := ?_ }
  · intro n f x
    change carrierAction η
      (if ∀ i, @sortEval Carrier interpret (Fn.argSort f i) (x i) then function f x
        else @CanonicalStructure.sortZero Carrier interpret (Fn.resSort f)) =
      if ∀ i, @sortEval Carrier interpret (Fn.argSort f i) (carrierAction η (x i)) then
        function f (carrierAction η ∘ x) else @CanonicalStructure.sortZero Carrier interpret (Fn.resSort f)
    by_cases hx : ∀ i, @sortEval Carrier interpret (Fn.argSort f i) (x i)
    · have hm : ∀ i, @sortEval Carrier interpret (Fn.argSort f i) (carrierAction η (x i)) :=
        fun i => (carrierAction_sort η _ _).mpr (hx i)
      rw [if_pos hx, if_pos hm]
      exact carrierAction_function η f x
    · have hm : ¬ ∀ i, @sortEval Carrier interpret (Fn.argSort f i) (carrierAction η (x i)) :=
        fun h => hx (fun i => (carrierAction_sort η _ _).mp (h i))
      rw [if_neg hx, if_neg hm]
      cases hs : Fn.resSort f
      · exact congrArg Sum.inl (map_zero (puiseuxRootSystemAction η))
      · rfl
  · intro n r x
    cases r with
    | memVF => exact carrierAction_relation η _ x
    | memRV => exact carrierAction_relation η _ x
    | memUnits => exact carrierAction_relation η _ x
    | rvLe =>
      change ((∀ i : Fin 2, @sortEval Carrier interpret .rv (carrierAction η (x i))) ∧
        relation .rvLe (carrierAction η ∘ x)) ↔
          (∀ i : Fin 2, @sortEval Carrier interpret .rv (x i)) ∧ relation .rvLe x
      exact and_congr (forall_congr' (fun i => carrierAction_sort η .rv (x i)))
        (carrierAction_relation η _ x)


/-- The actual parameter base: Laurent-field elements and their RV image. -/
def baseCarrier : Carrier → Prop
  | .inl f => f ∈ puiseuxBaseSubfield ℂ
  | .inr none => True
  | .inr (some u) => ∃ z : ℤ, u.1 = Multiplicative.ofAdd (z : ℚ)

theorem carrierAction_fixes_base (η : CompatibleRoots ℂ) (x : Carrier) (hx : baseCarrier x) :
    carrierAction η x = x := by
  rcases x with f | r
  · change Sum.inl (puiseuxRootSystemAction η f) = Sum.inl f
    exact congrArg Sum.inl ((puiseuxRootSystemAction η).commutes (⟨f, hx⟩ : puiseuxBaseSubfield ℂ))
  · cases r with
    | none => rfl
    | some u =>
      obtain ⟨z, hz⟩ := hx
      change Sum.inr (some (u.1, compatibleRootCharacter η u.1 * u.2)) = Sum.inr (some u)
      rw [hz, compatibleRootCharacter_int, one_mul]
      exact congrArg (fun q => Sum.inr (some (q, u.2))) hz.symm

section CanonicalFormulas
local instance canonicalFormulaStructure : LRV.Structure Carrier := canonicalInterpret

/-- Every original-language formula, including VF quantifiers, is preserved.
All field and RV parameters remain in the actual Laurent base. -/
theorem original_formula_invariant (η : CompatibleRoots ℂ) {α : Type*} {n : ℕ}
    (φ : LRV.BoundedFormula α n) (v : α → Carrier)
    (hv : ∀ a, baseCarrier (v a)) (r : Fin n → RV) :
    φ.Realize v (fun i => Sum.inr (rvAction η (r i))) ↔
      φ.Realize v (fun i => Sum.inr (r i)) := by
  have h := StrongHomClass.realize_boundedFormula (canonicalLanguageAction η) φ
    (v := v) (xs := fun i => Sum.inr (r i))
  have he : (canonicalLanguageAction η) ∘ v = v :=
    funext (fun a => carrierAction_fixes_base η (v a) (hv a))
  rw [he] at h
  exact h

end CanonicalFormulas

end DiamondIntegral.Section5.PuiseuxOriginal
