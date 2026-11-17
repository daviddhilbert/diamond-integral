import «section 3».MeasuredRealGroundContext
import «section 3».GammaGroundRealNamesElimination
import «section 3».MeasuredVFData
import «section 3».RVFormGraphs
import «section 3».GammaGroundMeasuredVFData

/-! Literal object and map adapters between the ordinary real base and
its redundant definable Gamma names. Structural coordinates, RV labels
and complete density functions are preserved pointwise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base) {k : ℕ}
local notation "hNames" => measuredRealGroundContext_gamma_names C B

def rvFromReal (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k :=
  ⟨GammaGroundRVObject.ofReal U.underlying,GammaGroundMap.ofReal (U.form.toGammaVolumeForm hc)⟩

def rvToRealUnderlying (U : GammaGroundRVObject hc (measuredRealGroundContext C B).base k) : RVObject (M := M) (C.base : Set M) k where
  arity := U.arity
  domain := U.domain.toRealNames hNames
  volume := U.volume.toRealNames hNames
  finite := U.finite
  nonzero := U.nonzero

def rvToReal (U : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k) : MeasuredRVObject (M := M) (C.base : Set M) k :=
  ⟨rvToRealUnderlying C hc B U.underlying,
    GammaVolumeForm.toRVVolumeForm hc (U := rvToRealUnderlying C hc B U.underlying) (U.form.toRealNames hNames)⟩

def rvHomFromReal {U V : MeasuredRVObject (M := M) (C.base : Set M) k} (f : MeasuredRVHom U V) :
    GammaGroundMeasuredRVHom (rvFromReal C hc B U) (rvFromReal C hc B V) :=
  ⟨⟨GammaGroundMap.ofReal f.bijection.map,f.bijection.bijective⟩,f.preserves⟩

def rvHomToReal {U V : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k} (f : GammaGroundMeasuredRVHom U V) :
    MeasuredRVHom (rvToReal C hc B U) (rvToReal C hc B V) :=
  ⟨⟨f.bijection.map.toRealNames hNames,f.bijection.bijective⟩,f.preserves⟩

def rvRealRoundTrip (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    MeasuredRVHom (rvToReal C hc B (rvFromReal C hc B U)) U :=
  ⟨DefinableBijection.id U.underlying.domain,fun _ => rfl⟩

def rvGroundRoundTrip (U : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k) :
    GammaGroundMeasuredRVHom (rvFromReal C hc B (rvToReal C hc B U)) U :=
  ⟨GammaGroundBijection.id U.underlying.domain,fun _ => rfl⟩

def vfFromReal (U : MeasuredVFData C hc k) : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k :=
  ⟨U.arity,GammaGroundDefSet.ofReal U.domain,U.finite,GammaGroundMap.ofReal U.form⟩

def vfToReal (U : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k) : MeasuredVFData C hc k :=
  ⟨U.arity,U.domain.toRealNames hNames,U.finite,U.form.toRealNames hNames⟩

theorem vfToReal_fromReal (U : MeasuredVFData C hc k) : vfToReal C hc B (vfFromReal C hc B U) = U := by
  cases U
  rfl

theorem vfFromReal_toReal (U : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k) : vfFromReal C hc B (vfToReal C hc B U) = U := by
  cases U
  rfl

end DiamondIntegral.Section3.MeasuredRealGround
