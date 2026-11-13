import «section 4».RVResidueIsomorphisms
import «section 4».FieldPointCharts
import «section 4».RESFibreObjects

/-! Residue-field codes assign one to actual singleton RES domains,
including the degree-one point, and zero to actual empty domains. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResiduePointValues
open RVResidueChartCodes RVResidueIsomorphisms RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem code_empty {n : ℕ} {A : Set (Fin n → M)} (C : RawCode A) (ha : A = ∅) :
    FieldDefinableRing.objectClass (ModelResidue M) C.chart = 0 := by
  apply FieldPointCharts.objectClass_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (Set.eq_empty_iff_forall_notMem.mp ha) _ (C.bijective.mapsTo hx)

theorem code_unique {n : ℕ} {A : Set (Fin n → M)} (C : RawCode A)
    (ha : ∃! u, u ∈ A) : FieldDefinableRing.objectClass (ModelResidue M) C.chart = 1 := by
  obtain ⟨u, hu, huniq⟩ := ha
  obtain ⟨x, hx, hcx⟩ := C.bijective.surjOn hu
  apply FieldPointCharts.objectClass_unique
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact C.bijective.injOn hy hx ((huniq _ (C.bijective.mapsTo hy)).trans hcx.symm)

theorem value_empty (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] {B : Base (M := M)} {k : ℕ} (a : RESChart B k)
    (ha : a.domain = ∅) : value hc a = 0 := code_empty (code hc a) ha

theorem value_unique (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] {B : Base (M := M)} {k : ℕ} (a : RESChart B k)
    (ha : ∃! u, u ∈ a.domain) : value hc a = 1 := code_unique (code hc a) ha

theorem value_weightedUnit (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : value hc (weightedRESUnit B γ hγ) = 1 := by
  apply value_unique hc
  exact ⟨Fin.elim0, Set.mem_univ _, fun _ _ => funext (fun i : Fin 0 => i.elim0)⟩

theorem value_point (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] (B : Base (M := M)) : value hc (RESFibreObjects.point B) = 1 := by
  apply value_unique hc
  exact ⟨_, Set.mem_singleton _, fun _ h => Set.mem_singleton_iff.mp h⟩

end DiamondIntegral.Section4.RVResiduePointValues
