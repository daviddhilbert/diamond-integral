import «section 4».RVResidueCodes

/-! Pure-field codes for the actual original-base RES chart domains.
Their finite-pattern premise is derived from the RES object itself. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueChartCodes
open RVMeasuredCharts RVResidueFiniteNormalization RVResidueScaledCovers
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure RawCode {n : ℕ} (A : Set (Fin n → M)) where
  chart : FieldDefinableRing.Chart (ModelResidue M)
  decode : (Fin chart.arity → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)
  bijective : Set.BijOn (fun x => rvValues (decode x)) chart.domain A
  cover : Cover chart.domain decode

def typedSet {B : Base (M := M)} {k : ℕ} (a : Chart B k) :=
  RVResiduePullback.ofRaw a.domain a.domain_definable

def rawEquiv {B : Base (M := M)} {k : ℕ} (a : Chart B k) : a.domain ≃ typedSet a where
  toFun u := ⟨fun i => ⟨u.val i, a.domain_definable.proper u.val u.property i⟩, u.property⟩
  invFun t := ⟨rvValues t.val, t.property⟩
  left_inv _ := rfl
  right_inv t := by apply Subtype.ext; funext i; apply Subtype.ext; rfl

theorem patterns_finite {B : Base (M := M)} {k : ℕ} (a : RESChart B k) :
    Finite (Patterns (typedSet a.toChart)) := by
  have hs : (Patterns (typedSet a.toChart) : Set (Fin a.arity → Values.GammaTop (M := M))) ⊆
      Set.range a.toChart.valuePattern := by
    rintro γ ⟨t, rfl⟩
    exact ⟨(rawEquiv a.toChart).symm t, rfl⟩
  exact a.finite_values.subset hs

theorem rvValues_bijective {B : Base (M := M)} {k : ℕ} (a : Chart B k) :
    Set.BijOn rvValues (typedSet a).carrier a.domain := by
  refine ⟨fun _ ht => ht, fun _ _ _ _ he => rvValues_injective he, ?_⟩
  intro u hu
  exact ⟨(rawEquiv a ⟨u, hu⟩).val, (rawEquiv a ⟨u, hu⟩).property, rfl⟩

def code (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] {B : Base (M := M)} {k : ℕ} (a : RESChart B k) :
    RawCode a.domain := by
  letI := patterns_finite a
  let C := RVResidueCodes.code hc (typedSet a.toChart)
  exact ⟨C.chart, C.decode, (rvValues_bijective a.toChart).comp C.bijective, C.cover⟩

end DiamondIntegral.Section4.RVResidueChartCodes
