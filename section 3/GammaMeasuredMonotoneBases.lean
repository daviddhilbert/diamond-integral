import «section 3».GammaGroundMonotoneBases
import «section 3».GammaGroundRVBaseReduction
import «section 3».GammaMeasuredRealBaseExtension
import «section 3».GammaGroundMeasuredVFGerms
import «section 3».GammaNativeGroundHighRestriction

/-! Enlarging both parameter sets preserves actual mixed objects,
essential representatives, and native lift and normalization formulas.
Definable reduction recovers the original RV object literally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)} {n : ℕ}
variable (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma)

def GammaGroundMeasuredVFData.monoBase (U : GammaGroundMeasuredVFData hc B n) : GammaGroundMeasuredVFData hc C n :=
  ⟨U.arity,U.domain.monoBase hr hg,U.finite,U.form.monoBase hr hg⟩

theorem gammaMeasuredVF_monoBase_restrict (U : GammaGroundMeasuredVFData hc B n)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n U.arity)) (hA : A.carrier ⊆ U.domain.carrier) :
    (U.restrict A hA).monoBase hr hg = (U.monoBase hr hg).restrict (A.monoBase hr hg) hA := rfl

def GammaGroundRVObject.monoBase (U : GammaGroundRVObject hc B n) : GammaGroundRVObject hc C n :=
  ⟨U.arity,U.domain.monoBase hr hg,U.volume.monoBase hr hg,U.finite,U.nonzero⟩

def GammaGroundMeasuredRVObject.monoBase (U : GammaGroundMeasuredRVObject hc B n) : GammaGroundMeasuredRVObject hc C n :=
  ⟨U.underlying.monoBase hr hg,U.form.monoBase hr hg⟩

theorem gammaMeasuredRV_reduce_monoBase (H : GammaDefinableBaseReduction C B)
    (U : GammaGroundMeasuredRVObject hc B n) :
    gammaGroundMeasuredRVReduceObject H (U.monoBase hr hg) = U := by
  cases U
  rfl

def gammaNativeBaseExtend (U : GammaObjectAt B Set.univ n) : GammaObjectAt C Set.univ n where
  object := U.object
  real_contains := Set.subset_univ _
  domain_graph := U.domain_graph.mono hr hg
  volume_graph := U.volume_graph.mono hr hg

def gammaNativeBaseExtendForm (U : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundVolumeForm hc C (Section5.nativeRVGroundDomain (gammaNativeBaseExtend hr hg U)) :=
  ω.monoBase hr hg

theorem gammaNativeBaseExtend_lift (U : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    gammaNativeMeasuredLift (gammaNativeBaseExtend hr hg U) (gammaNativeBaseExtendForm hr hg U ω) =
      (gammaNativeMeasuredLift U ω).monoBase hr hg := rfl

theorem gammaNativeNormalization_monoBase (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    gammaNativeMeasuredNormalization (gammaNativeBaseExtend hr hg U) (gammaNativeBaseExtendForm hr hg U ω) =
      (gammaNativeMeasuredNormalization U ω).monoBase hr hg := rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def GammaGroundEssentialVFMap.monoBase {U V : GammaGroundMeasuredVFData hc B n}
    (f : GammaGroundEssentialVFMap U.domain V.domain) :
    GammaGroundEssentialVFMap (U.monoBase hr hg).domain (V.monoBase hr hg).domain where
  source := f.source.monoBase hr hg
  target := f.target.monoBase hr hg
  source_subset := f.source_subset
  target_subset := f.target_subset
  source_small := f.source_small
  target_small := f.target_small
  map := f.map.monoBase hr hg
  bijective := f.bijective

theorem GammaGroundEssentialVFMap.preserves_monoBase {U V : GammaGroundMeasuredVFData hc B n}
    (f : GammaGroundEssentialVFMap U.domain V.domain)
    (hf : f.Preserves Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V)) :
    (f.monoBase hr hg).Preserves Values.vfValueHom
      (gammaGroundMeasuredVFWeight (U.monoBase hr hg)) (gammaGroundMeasuredVFWeight (V.monoBase hr hg)) := hf

end DiamondIntegral.Section3
