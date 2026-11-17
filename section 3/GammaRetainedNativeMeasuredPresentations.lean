import «section 3».GammaRetainedHeadComparisons
import «section 3».GammaGroundFormExtensionByOne
import Integration7.GammaSpecialCommonNames

/-! A retained-density mixed object has a literal native presentation
in any containing common-name context. The actual VF and RV points and
the given Gamma form are unchanged by this internal presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

namespace GammaRetainedMeasuredVFData
variable (C : BaseContext M) (hNames : commonRealNames B ⊆ (C.base : Set M))
variable (U : GammaRetainedMeasuredVFData hc B (n+1))

def nativeSet : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) U.arity :=
  gammaNativePresentation U.pointSet U.point_definable hNames

def nativeData : GammaGroundMeasuredVFData hc B (n+1) :=
  gammaPointMeasuredData (U.nativeSet C hNames) U.point_definable U.finite
    (gammaPointRetainedForm (U.nativeSet C hNames) U.point_definable
      (GammaGroundDefSet.univ hc B (rawRVSpace U.arity)) id (fun _ => Set.mem_univ _) U.form.extendByOne)

def nativeBridge (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    GammaFullMeasuredBijection U.toMeasured (U.nativeData C hNames) :=
  gammaFullMeasuredFixedVF C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv
    (GammaGroundBijection.ofCarrierEq rfl) (fun _ => rfl) (by
      intro p
      have h := U.form.extendByOne_apply ⟨p.val.2,U.labels_mem p⟩
      exact congrArg (fun z : GammaGroundDefSet.univ hc B (volumeGammaSpace hc) =>
        (cast (gammaCarrier hc) z.val).val) h.symm)

theorem nativeBridge_value (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : U.toMeasured.domain) :
    ((U.nativeBridge C hNames hBC hv).map.map p).val = p.val := rfl

end GammaRetainedMeasuredVFData
end DiamondIntegral.Section3
