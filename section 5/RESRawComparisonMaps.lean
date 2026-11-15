import «section 5».NativeRESForwardRing
import «section 5».DiagonalRESRingMap

/-! The forward raw comparison descends through the actual forget-degree
ideal. Both directions are actual homomorphisms on the native ungraded RES
ring and the explicit diagonal constructible presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance resRawComparisonMapsStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

def chartToDiagonal : RESOrdinaryRing.Ring originalPuiseuxGround →+* DiagonalConstructible.Ring :=
  nativeForwardOrdinary.comp (Section3RESRingEquivalences.ordinary canonicalInterpret_isCanonical originalPuiseuxGround).toRingHom

theorem chartToDiagonal_objectClass {k : ℕ} (a : RVMeasuredCharts.RESChart originalPuiseuxGround k) :
    chartToDiagonal (RESOrdinaryRing.objectClass a) =
      nativeForwardValue (Section3RVChartBridge.nativeRES canonicalInterpret_isCanonical a) := by
  change nativeForwardOrdinary
    (Section3RESRingEquivalences.ordinary canonicalInterpret_isCanonical originalPuiseuxGround (RESOrdinaryRing.objectClass a)) = _
  rw [Section3RESRingEquivalences.ordinary_class, nativeForwardOrdinary_class]

def chartUnderlyingBijection {k l : ℕ}
    (a : RVMeasuredCharts.RESChart originalPuiseuxGround k) (b : RVMeasuredCharts.RESChart originalPuiseuxGround l)
    (f : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart) :
    GammaGroundBijection (Section3RVChartBridge.nativeRES canonicalInterpret_isCanonical a).obj.domain
      (Section3RVChartBridge.nativeRES canonicalInterpret_isCanonical b).obj.domain :=
  Section3RVCodeBridge.bijectionOfRaw a.domain b.domain a.domain_definable b.domain_definable
    f.extension f.extension_graph f.extension_bijOn

theorem chartToDiagonal_degreeIdeal :
    RESDimensionFreeRing.degreeIdeal originalPuiseuxGround ≤ RingHom.ker chartToDiagonal := by
  apply Ideal.span_le.mpr
  rintro x ⟨k, l, a, b, f, rfl⟩
  change chartToDiagonal (RESOrdinaryRing.objectClass a - RESOrdinaryRing.objectClass b) = 0
  rw [map_sub, chartToDiagonal_objectClass, chartToDiagonal_objectClass, sub_eq_zero]
  exact nativeForwardValue_bijection _ _ (chartUnderlyingBijection a b f)

def resToDiagonal : RESDimensionFreeRing.Ring originalPuiseuxGround →+* DiagonalConstructible.Ring :=
  Ideal.Quotient.lift (RESDimensionFreeRing.degreeIdeal originalPuiseuxGround) chartToDiagonal
    (fun _ hx => chartToDiagonal_degreeIdeal hx)

theorem resToDiagonal_objectClass {k : ℕ} (a : RVMeasuredCharts.RESChart originalPuiseuxGround k) :
    resToDiagonal (RESDimensionFreeRing.objectClass a) =
      nativeForwardValue (Section3RVChartBridge.nativeRES canonicalInterpret_isCanonical a) :=
  chartToDiagonal_objectClass a

theorem resToDiagonal_nativeClass {k : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k) :
    resToDiagonal (nativeUngradedClass canonicalInterpret_isCanonical U) = nativeForwardValue U := by
  rw [nativeUngradedClass, resToDiagonal_objectClass]
  exact nativeForwardValue_bijection _ _ (Section3RVRoundtripBridge.native_chart U.obj)

theorem resToDiagonal_resSetClass {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) :
    resToDiagonal (resSetClass canonicalInterpret_isCanonical A hA) = forwardRESValue A hA :=
  resToDiagonal_nativeClass (nativeRESObjectOfSet canonicalInterpret_isCanonical A hA)

end DiamondIntegral.Section5.PuiseuxOriginal
