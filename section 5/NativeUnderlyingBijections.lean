import «section 4».Section3RVRoundtripBridge
import «section 4».Section3RVBasicClasses

/-! Arbitrary-degree underlying chart isomorphisms induce actual native
Gamma-ground bijections. No coordinate label survives in the domain map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
open Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeUnderlyingBijection {k l : ℕ} {A : RVMeasuredCharts.Chart B k} {C : RVMeasuredCharts.Chart B l}
    (F : RVUnderlyingIsomorphisms.Iso A C) :
    GammaGroundBijection (Section3RVChartBridge.native hc A).domain (Section3RVChartBridge.native hc C).domain :=
  bijectionOfRaw A.domain C.domain A.domain_definable C.domain_definable
    F.extension F.extension_graph F.extension_bijOn

end DiamondIntegral.Section5
