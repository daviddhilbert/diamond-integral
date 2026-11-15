import «section 5».GammaValueSchemata
import «section 5».RESBijectionRealization
import «section 5».NativeBoundedRetraction

/-! The full-fibre schema realizes the actual native value torsor.
Its class equals the native residue torus without choosing an RV point. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

def GammaValueSchema.fibre (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) :
    RVMeasuredCharts.RESChart ⟨B.real ∪ Set.range z, B.gamma⟩ 1 :=
  RESFibreObjects.fibre _ (F.value hc z h) 1 (F.value_definable hc z h)
    (GammaGroupNames.one_definable_base _)

theorem GammaValueSchema.fibre_domain (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) :
    (F.fibre hc z h).domain = F.resSchema.rowDomain z := by
  ext x
  exact (F.value_row hc z h x).symm

def GammaValueSchema.fibreIso (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) :
    RVUnderlyingIsomorphisms.Iso (F.resSchema.chart hc z h.1).toChart (F.fibre hc z h).toChart := by
  refine RVUnderlyingIsomorphisms.ofMap (F.resSchema.chart hc z h.1).toChart
    (F.fibre hc z h).toChart (id : (Fin 1 → M) → (Fin 1 → M)) ?_ ?_
  · exact RVSharpCharts.identity_graph_definable _ _ (F.resSchema.chart hc z h.1).domain_definable
  change Set.BijOn id (F.resSchema.chart hc z h.1).domain (F.fibre hc z h).domain
  rw [F.resSchema.chart_domain hc z h.1, F.fibre_domain hc z h]
  exact Set.bijOn_id _

theorem GammaValueSchema.native_fibre_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) :
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass (F.resSchema.chart hc z h.1)) =
      nativeTorusClass ⟨B.real ∪ Set.range z, B.gamma⟩ := by
  have he := congrArg (RESDimensionFreeReduction.quotient ⟨B.real ∪ Set.range z, B.gamma⟩)
    (RESDimensionFreeRing.objectClass_iso _ _ (F.fibreIso hc z h))
  apply he.trans
  exact congrArg (RESDimensionFreeReduction.fromGradedReduced ⟨B.real ∪ Set.range z, B.gamma⟩)
    (RESOrdinaryReduction.fibre_class _ (F.value hc z h) 1 (F.value_definable hc z h)
      (GammaGroupNames.one_definable_base _))

end DiamondIntegral.Section5
