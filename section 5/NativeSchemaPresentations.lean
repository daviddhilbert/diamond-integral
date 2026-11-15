import «section 5».NativeSetBijections
import «section 5».RESSetChartPresentations

/-! Every actual native RES object at a mixed-sort parameter is presented
by an original-base row schema and an actual Gamma-ground bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

def nativeSchemaPresentation (z : Fin p → M)
    (U : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ k)
    (F : RESSetSchema B p U.obj.arity sp) (hF : F.Valid hc z)
    (hrow : F.rowDomain z = rawDomain U.obj.domain) :
    GammaGroundBijection (F.object hc z hF).obj.domain U.obj.domain :=
  gammaGroundBijectionOfRawDomainEq _ _
    ((rawDomain_ofRaw (F.rowDomain z) (F.row_domain_definable z)).trans hrow)

theorem native_res_schema_at_parameter (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (U : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ k) :
    ∃ F : RESSetSchema B p U.obj.arity sp, ∃ hF : F.Valid hc z,
      F.rowDomain z = rawDomain U.obj.domain ∧
      Nonempty (GammaGroundBijection (F.object hc z hF).obj.domain U.obj.domain) := by
  obtain ⟨F, hF, hrow⟩ := res_set_schema_at_parameter hc B sp z hz (Section3RVChartBridge.chartRES U)
  exact ⟨F, hF, hrow, ⟨nativeSchemaPresentation z U F hF hrow⟩⟩

end DiamondIntegral.Section5
