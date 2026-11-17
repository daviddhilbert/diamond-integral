import «section 3».GammaRetainedContractionValues
import «section 3».GammaRelativeArbitraryMeasuredOrders

/-! Relatively unary full measured maps preserve the contraction value
of arbitrary retained-density mixed objects. The literal native bridges
fix every coordinate, so the saved relative comparison applies directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRetained_relative_contraction_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : GammaRetainedMeasuredVFData hc B (n+1)}
    (F : GammaFullMeasuredBijection U.toMeasured V.toMeasured)
    (i : Fin (n+1)) (hi : ∀ p, ∀ j, j ≠ i → (F.map.map p).val.1 j = p.val.1 j) :
    U.contractionValue C hBC hNames hGenerated = V.contractionValue C hBC hNames hGenerated := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let PU := U.nativeBridge C hNames hBC hv
  let PV := V.nativeBridge C hNames hBC hv
  let K := ((PU.symm C.uncountable.le C.saturated hr hv).comp C.uncountable.le C.saturated hr hv F).comp
    C.uncountable.le C.saturated hr hv PV
  have hInv (p : (U.nativeData C hNames).domain) : (PU.map.symm.map p).val = p.val := by
    have h := PU.map.map.apply_inverse PU.map.bijective p
    exact (U.nativeBridge_value C hNames hBC hv (PU.map.symm.map p)).symm.trans (congrArg Subtype.val h)
  have hK : ∀ p, ∀ j, j ≠ i → (K.map.map p).val.1 j = p.val.1 j := by
    intro p j hj
    change (PV.map.map (F.map.map (PU.map.symm.map p))).val.1 j = p.val.1 j
    have hV := V.nativeBridge_value C hNames hBC hv (F.map.map (PU.map.symm.map p))
    exact (congrArg (fun z => z.1 j) hV).trans
      ((hi (PU.map.symm.map p) j hj).trans (congrArg (fun z => z.1 j) (hInv p)))
  exact gammaRelative_arbitrary_measured_orders C hBC hv hg hNames hGenerated δ hδ hδ1
    (A := U.nativeSet C hNames) (D := V.nativeSet C hNames) U.point_definable V.point_definable U.finite V.finite U.form.extendByOne V.form.extendByOne K i hK
    (U.contraction C hBC hNames hGenerated) (V.contraction C hBC hNames hGenerated)
    (U.contraction_gamma C hBC hNames hGenerated) (V.contraction_gamma C hBC hNames hGenerated)

end DiamondIntegral.Section3
