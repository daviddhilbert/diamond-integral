import «section 5».RESRawComparisonEquivalence
import «section 4».RESFibreObjects

/-! Exact rational coordinates for native nonzero Gamma values and the
actual native RES value-fibre domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance puiseuxRationalValuesStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem rv_normal_eq_none_iff (r : CanonicalRV.RVSort Carrier) :
    taggedRVEquiv r = none ↔ r.val = iRVZero := by
  constructor
  · intro h
    have he : r = rvTag none := taggedRVEquiv.injective h
    exact congrArg Subtype.val he
  · intro h
    have he : r = rvTag none := Subtype.ext h
    exact congrArg taggedRVEquiv he

def gammaRational (α : Values.Gamma (M := Carrier)) : ℚ :=
  (value (taggedRVEquiv (GammaParameters.representative α).val)).untopD 0

theorem gammaRational_value (α : Values.Gamma (M := Carrier)) :
    value (taggedRVEquiv (GammaParameters.representative α).val) = (gammaRational α : WithTop ℚ) := by
  have hn : taggedRVEquiv (GammaParameters.representative α).val ≠ none :=
    fun h => (GammaParameters.representative α).property ((rv_normal_eq_none_iff _).mp h)
  cases h : taggedRVEquiv (GammaParameters.representative α).val with
  | none => exact (hn h).elim
  | some u => simp [gammaRational, h, value]

theorem gammaRational_vrv_iff (α : Values.Gamma (M := Carrier)) (r : CanonicalRV.RVSort Carrier) :
    Values.vrv r = α.val ↔ value (taggedRVEquiv r) = (gammaRational α : WithTop ℚ) := by
  have he : Values.vrv (GammaParameters.representative α).val = α.val :=
    congrArg Subtype.val (GammaParameters.representative_value α)
  rw [← he, vrv_eq_iff_value_eq, gammaRational_value]

def rationalGamma (q : ℚ) : Values.Gamma (M := Carrier) :=
  GammaParameters.value ⟨rvTag (some (Multiplicative.ofAdd q, 1)), by intro h; cases h⟩

theorem gammaRational_rationalGamma (q : ℚ) : gammaRational (rationalGamma q) = q := by
  have h := (gammaRational_vrv_iff (rationalGamma q) (rvTag (some (Multiplicative.ofAdd q, 1)))).mp rfl
  change (q : WithTop ℚ) = (gammaRational (rationalGamma q) : WithTop ℚ) at h
  exact (WithTop.coe_injective h).symm

theorem gammaRational_surjective : Function.Surjective gammaRational :=
  fun q => ⟨rationalGamma q, gammaRational_rationalGamma q⟩

theorem gammaRational_one : gammaRational (1 : Values.Gamma (M := Carrier)) = 0 := by
  have hn : taggedRVEquiv (1 : CanonicalRV.RVSort Carrier) = some (Multiplicative.ofAdd 0, 1) := by
    change rvPart (1 : CanonicalRV.RVSort Carrier).val = _
    rw [RVOperations.one_val]
    rfl
  have h := (gammaRational_vrv_iff 1 (1 : CanonicalRV.RVSort Carrier)).mp RVOperations.vrv_one
  rw [hn] at h
  change (0 : WithTop ℚ) = (gammaRational 1 : WithTop ℚ) at h
  exact (WithTop.coe_injective h).symm

def originalValueFibre (α : Values.Gamma (M := Carrier))
    (hα : GammaParameters.GammaDefinableClosureAtBase originalPuiseuxGround α) :
    DefSet (rawRVSpace (M := Carrier) 1) {c | baseCarrier c} :=
  originalDomain canonicalInterpret_isCanonical (Section3RVChartBridge.nativeRES canonicalInterpret_isCanonical
    (RESFibreObjects.fibre originalPuiseuxGround α 1 hα (GammaGroupNames.one_definable_base originalPuiseuxGround)))

theorem originalValueFibre_mem (α : Values.Gamma (M := Carrier))
    (hα : GammaParameters.GammaDefinableClosureAtBase originalPuiseuxGround α)
    (r : Fin 1 → CanonicalRV.RVSort Carrier) :
    r ∈ (originalValueFibre α hα).carrier ↔ value (taggedRVEquiv (r 0)) = (gammaRational α : WithTop ℚ) := by
  change (GammaParameters.Proper (rvValues r) ∧ GammaParameters.codeValue (rvValues r 0) = α) ↔ _
  constructor
  · rintro ⟨hr, he⟩
    let c : GammaParameters.Code (M := Carrier) := ⟨r 0, (hr 0).2⟩
    have hc : GammaParameters.value c = α := (GammaParameters.codeValue_raw c).symm.trans he
    exact (gammaRational_vrv_iff α (r 0)).mp (congrArg Subtype.val hc)
  · intro hr
    have hn : taggedRVEquiv (r 0) ≠ none := by
      intro he
      simp only [he, value, WithTop.top_ne_coe] at hr
    have hz : (r 0).val ≠ iRVZero := fun he => hn ((rv_normal_eq_none_iff _).mpr he)
    let c : GammaParameters.Code (M := Carrier) := ⟨r 0, hz⟩
    refine ⟨(fun i => by fin_cases i; exact ⟨(r 0).property, hz⟩), ?_⟩
    exact (GammaParameters.codeValue_raw c).trans (Subtype.ext ((gammaRational_vrv_iff α (r 0)).mpr hr))

end DiamondIntegral.Section5.PuiseuxOriginal
