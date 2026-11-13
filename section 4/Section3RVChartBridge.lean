import «section 4».Section3RVCodeBridge
import «section 4».RVForgetScissors
import «section 3».GammaGroundRVCategories
import «section 3».GammaGroundBijections

/-! Actual RV object and isomorphism conversions, retaining the original
base, all domain coordinates (including zero), and the object degree. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVChartBridge
open RVMeasuredCharts Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def chart {k : ℕ} (U : GammaGroundRVObject hc B k) : Chart B k where
  arity := U.arity
  domain := rawDomain U.domain
  domain_definable := rawDomain_definable U.domain
  coordinate := rawMap U.volume
  coordinate_definable := rawMap_definable U.volume
  coordinate_proper x hx := by
    let a := (rawEquiv U.domain).symm ⟨x, hx⟩
    have ha : rvValues a.val = x := rawEquiv_symm_value U.domain ⟨x, hx⟩
    rw [← ha, rawMap_apply]
    intro i
    exact ⟨((U.volume a).val i).property, U.nonzero a i⟩
  finite_fibres := rawMap_finite U.volume U.finite
  volume := fun _ => 1
  volume_definable := constant_volume_definable B _ (rawDomain_definable U.domain) 1
    (GammaGroupNames.one_definable_base B)

def native (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (a : Chart B k) :
    GammaGroundRVObject hc B k where
  arity := a.arity
  domain := ofRaw a.domain a.domain_definable
  volume := mapOfRaw a.domain a.domain_definable a.coordinate a.coordinate_definable
    (fun x hx i => (a.coordinate_proper x hx i).1)
  finite t := by
    let D := ofRaw (hc := hc) a.domain a.domain_definable
    have hinj : Function.Injective (fun u : D => rvValues u.val) :=
      fun _ _ h => Subtype.ext (rvValues_injective h)
    apply ((a.finite_fibres (rvValues t.val)).preimage hinj.injOn).subset
    intro u hu
    refine ⟨u.property, ?_⟩
    exact congrArg (fun v : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k) => rvValues v.val) hu
  nonzero u i := (a.coordinate_proper _ u.property i).2

theorem native_coordinate {k : ℕ} (a : Chart B k) (u : (native hc a).domain) :
    rvValues ((native hc a).volume u).val = a.coordinate (rvValues u.val) := rfl

theorem chart_coordinate {k : ℕ} (U : GammaGroundRVObject hc B k) (u : U.domain) :
    (chart U).coordinate (rvValues u.val) = rvValues (U.volume u).val := rawMap_apply U.volume u

def chartRES {k : ℕ} (X : GammaGroundRESObject hc B k) : RESChart B k where
  toChart := chart X.obj
  finite_values := by
    apply X.property.subset
    rintro γ ⟨u, rfl⟩
    let a := (rawEquiv X.obj.domain).symm u
    have ha : rvValues a.val = u.val := rawEquiv_symm_value X.obj.domain u
    refine ⟨a.val, a.property, ?_⟩
    funext i
    apply congrArg Values.vrv
    apply Subtype.ext
    exact congrFun ha i

def nativeRES (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (a : RESChart B k) :
    GammaGroundRESObject hc B k :=
  ⟨native hc a.toChart, by
    apply a.finite_values.subset
    rintro γ ⟨t, ht, rfl⟩
    refine ⟨⟨rvValues t, ht⟩, ?_⟩
    rfl⟩

def chartIso {k : ℕ} {U V : GammaGroundRVObject hc B k}
    (f : GammaGroundBijection U.domain V.domain) : RVForgetScissors.UnderlyingIso (chart U) (chart V) :=
  RVForgetScissors.ofMap (chart U) (chart V) (rawMap f.map)
    (rawMap_definable f.map) (rawMap_bijective f.map f.bijective)

end DiamondIntegral.Section4.Section3RVChartBridge
