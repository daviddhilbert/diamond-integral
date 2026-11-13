import «section 4».RVResidueRestrictedCodes
import «section 4».RVResidueCodeIndependence
import «section 4».FieldScissorClasses
import «section 4».RVOrdinaryScissorComponents

/-! Actual RES scissors are preserved by residue-field codes. A common
code for the union realizes all four sets in one field ambient space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueScissors
open RVMeasuredCharts RVChartDisjointUnion RVResidueChartCodes RVResidueIsomorphisms
open RVResidueCodeIndependence RVResidueRestrictedCodes
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem scissor_uniform (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] {B : Base (M := M)} {n k : ℕ} (a b c d : Data B n k)
    (ha : (Set.range a.toChart.valuePattern).Finite) (hb : (Set.range b.toChart.valuePattern).Finite)
    (hcf : (Set.range c.toChart.valuePattern).Finite) (hd : (Set.range d.toChart.valuePattern).Finite)
    (hU : RVForgetScissors.packedDomain c.toChart =
      RVForgetScissors.packedDomain a.toChart ∪ RVForgetScissors.packedDomain b.toChart)
    (hI : RVForgetScissors.packedDomain d.toChart =
      RVForgetScissors.packedDomain a.toChart ∩ RVForgetScissors.packedDomain b.toChart) :
    value hc ⟨c.toChart, hcf⟩ + value hc ⟨d.toChart, hd⟩ =
      value hc ⟨a.toChart, ha⟩ + value hc ⟨b.toChart, hb⟩ := by
  have hu := RVOrdinaryScissorComponents.domain_union a b c hU
  have hi := RVOrdinaryScissorComponents.domain_intersection a b d hI
  have hAC : a.domain ⊆ c.domain := by rw [hu]; exact Set.subset_union_left
  have hBC : b.domain ⊆ c.domain := by rw [hu]; exact Set.subset_union_right
  have hDC : d.domain ⊆ c.domain := by rw [hi]; exact Set.inter_subset_left.trans hAC
  let C : RawCode c.domain := code hc (⟨c.toChart, hcf⟩ : RESChart B k)
  let A := restrict hc C a.domain a.domain_definable hAC
  let B' := restrict hc C b.domain b.domain_definable hBC
  let D := restrict hc C d.domain d.domain_definable hDC
  have hUF : C.chart.domain = A.chart.domain ∪ B'.chart.domain := by
    ext x
    change x ∈ C.chart.domain ↔ (x ∈ C.chart.domain ∧ rvValues (C.decode x) ∈ a.domain) ∨
      (x ∈ C.chart.domain ∧ rvValues (C.decode x) ∈ b.domain)
    constructor
    · intro hx
      have hm : rvValues (C.decode x) ∈ c.domain := C.bijective.mapsTo hx
      have hm' : rvValues (C.decode x) ∈ a.domain ∪ b.domain :=
        (congrArg (fun U : Set (Fin n → M) => rvValues (C.decode x) ∈ U) hu).mp hm
      exact hm'.elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
    · exact fun h => h.elim And.left And.left
  have hIF : D.chart.domain = A.chart.domain ∩ B'.chart.domain := by
    ext x
    change (x ∈ C.chart.domain ∧ rvValues (C.decode x) ∈ d.domain) ↔
      ((x ∈ C.chart.domain ∧ rvValues (C.decode x) ∈ a.domain) ∧
        (x ∈ C.chart.domain ∧ rvValues (C.decode x) ∈ b.domain))
    have himem : rvValues (C.decode x) ∈ d.domain ↔
        rvValues (C.decode x) ∈ a.domain ∧ rvValues (C.decode x) ∈ b.domain :=
      (congrArg (fun U : Set (Fin n → M) => rvValues (C.decode x) ∈ U) hi).to_iff
    constructor
    · rintro ⟨hx, hd⟩
      exact ⟨⟨hx, (himem.mp hd).1⟩, hx, (himem.mp hd).2⟩
    · rintro ⟨⟨hx, ha⟩, _, hb⟩
      exact ⟨hx, himem.mpr ⟨ha, hb⟩⟩
  have hs := FieldScissorClasses.objectClass_scissor A.chart.domain B'.chart.domain
    C.chart.domain D.chart.domain A.chart.definable B'.chart.definable
    C.chart.definable D.chart.definable hUF hIF
  change FieldDefinableRing.objectClass (ModelResidue M) C.chart +
      FieldDefinableRing.objectClass (ModelResidue M) D.chart =
    FieldDefinableRing.objectClass (ModelResidue M) A.chart +
      FieldDefinableRing.objectClass (ModelResidue M) B'.chart at hs
  rw [code_class_value hc (⟨c.toChart, hcf⟩ : RESChart B k) C,
    code_class_value hc (⟨d.toChart, hd⟩ : RESChart B k) D,
    code_class_value hc (⟨a.toChart, ha⟩ : RESChart B k) A,
    code_class_value hc (⟨b.toChart, hb⟩ : RESChart B k) B'] at hs
  exact hs

theorem value_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] {B : Base (M := M)} {k : ℕ} (a b c d : RESChart B k)
    (h : RVForgetScissors.Scissor a.toChart b.toChart c.toChart d.toChart) :
    value hc c + value hc d = value hc a + value hc b := by
  rcases a with ⟨⟨aN, aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩, ha⟩
  rcases b with ⟨⟨bN, bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩, hb⟩
  rcases c with ⟨⟨cN, cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩, hcf⟩
  rcases d with ⟨⟨dN, dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩, hd⟩
  rcases h with ⟨hab, hac, had, hU, hI⟩
  change aN = bN at hab
  subst bN
  change aN = cN at hac
  subst cN
  change aN = dN at had
  subst dN
  exact scissor_uniform hc
    ⟨aD, aDef, aF, aGraph, aProper, aFinite, aV, aVGraph⟩
    ⟨bD, bDef, bF, bGraph, bProper, bFinite, bV, bVGraph⟩
    ⟨cD, cDef, cF, cGraph, cProper, cFinite, cV, cVGraph⟩
    ⟨dD, dDef, dF, dGraph, dProper, dFinite, dV, dVGraph⟩ ha hb hcf hd hU hI

end DiamondIntegral.Section4.RVResidueScissors
