import «section 4».RVSharpCharts
import «section 4».GammaBoundedProducts

/-! Actual RV domain bounds, ignoring the infinity coordinates. Every
measured RES chart is doubly bounded because its full value-pattern range
is finite. The proof uses finite upper/lower bounds in the actual ordered
Gamma group, without an Archimedean or definable-choice assumption. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredBounds
open RVMeasuredCharts RVSharpCharts GammaRVChartPresentation

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def finiteValue (γ : Values.GammaTop (M := M)) : Values.Gamma (M := M) :=
  if h : γ ≠ Values.infinity then ⟨γ, h⟩ else 1

theorem finiteValue_vrv (t : CanonicalRV.RVSort M) :
    finiteValue (Values.vrv t) = codeValue t.val := by
  by_cases ht : t.val = iRVZero
  · have hv := (Values.vrv_eq_infinity_iff t).mpr ht
    have hl : finiteValue (Values.vrv t) = 1 :=
      (congrArg finiteValue hv).trans (dite_eq_right (fun h => h rfl))
    have hr : codeValue t.val = 1 := dite_eq_right (fun h => h.2 ht)
    exact hl.trans hr.symm
  · have hv : Values.vrv t ≠ Values.infinity := fun h => ht ((Values.vrv_eq_infinity_iff t).mp h)
    let c : Code (M := M) := ⟨t, ht⟩
    have hl : finiteValue (Values.vrv t) = value c := dite_eq_left hv
    exact hl.trans (codeValue_raw c).symm

def DomainBounded {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Prop :=
  ∃ β : Values.Gamma (M := M), ∀ u ∈ a.domain, ∀ i, NonzeroRV (u i) →
    β⁻¹ ≤ codeValue (u i) ∧ codeValue (u i) ≤ β

theorem finite_patterns_bounded {B : Base (M := M)} {k : ℕ} (a : Chart B k)
    (ha : (Set.range a.valuePattern).Finite) : DomainBounded a := by
  let S : Set (Values.Gamma (M := M)) :=
    ⋃ p ∈ Set.range a.valuePattern, Set.range (fun i => finiteValue (p i))
  have hS : S.Finite := ha.biUnion (fun p _ => Set.finite_range (fun i => finiteValue (p i)))
  obtain ⟨l, hl⟩ := hS.bddBelow
  obtain ⟨b, hb⟩ := hS.bddAbove
  refine ⟨max b l⁻¹, ?_⟩
  intro u hu i _
  have hm : codeValue (u i) ∈ S := by
    refine Set.mem_iUnion.mpr ⟨a.valuePattern ⟨u, hu⟩, Set.mem_iUnion.mpr
      ⟨Set.mem_range_self _, Set.mem_range.mpr ⟨i, ?_⟩⟩⟩
    exact finiteValue_vrv ⟨u i, a.domain_definable.proper u hu i⟩
  have hi : (max b l⁻¹)⁻¹ ≤ l := by
    simpa only [inv_inv] using inv_le_inv_iff.mpr (le_max_right b l⁻¹)
  exact ⟨hi.trans (hl hm), (hb hm).trans (le_max_left b l⁻¹)⟩

theorem res_domain_bounded {B : Base (M := M)} {k : ℕ} (a : RESChart B k) :
    DomainBounded a.toChart := finite_patterns_bounded a.toChart a.finite_values

theorem sharp_domain_bounded {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n)
    (ha : GammaBoundedProducts.DomainBounded a.support) : DomainBounded (sharpChart a) := by
  obtain ⟨β, hβ⟩ := ha
  refine ⟨β, ?_⟩
  intro u hu i _
  exact hβ (codeValues u) hu.2 i

end DiamondIntegral.Section4.RVMeasuredBounds
