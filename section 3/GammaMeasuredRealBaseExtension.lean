import «section 3».GammaFullMeasuredBijections
import «section 3».GammaGroundRealExtensions
import «section 3».GammaNativeMeasuredLifts
import Integration7.PreparedGenericRVCells

/-! Actual Gamma forms and full measured maps extend to a larger real
parameter set. Genericity is used only in the monotone direction. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {P Q : Space LRV M}

def GammaGroundBijection.monoReal {A : GammaGroundDefSet hc B P} {D : GammaGroundDefSet hc B Q}
    (f : GammaGroundBijection A D) {S : Set M} (h : B.real ⊆ S) :
    GammaGroundBijection (A.monoReal h) (D.monoReal h) := ⟨f.map.monoReal h,f.bijective⟩

def GammaGroundMeasuredVFData.monoReal (U : GammaGroundMeasuredVFData hc B n)
    {S : Set M} (h : B.real ⊆ S) : GammaGroundMeasuredVFData hc ⟨S,B.gamma⟩ n :=
  ⟨U.arity,U.domain.monoReal h,U.finite,U.form.monoReal h⟩

def gammaNativeRealBaseExtend (U : GammaObjectAt B Set.univ n) {S : Set M} (h : B.real ⊆ S) :
    GammaObjectAt ⟨S,B.gamma⟩ Set.univ n where
  object := U.object
  real_contains := Set.subset_univ _
  domain_graph := U.domain_graph.mono h (Set.Subset.refl _)
  volume_graph := U.volume_graph.mono h (Set.Subset.refl _)

def gammaNativeRealBaseExtendForm (U : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) {S : Set M} (h : B.real ⊆ S) :
    GammaGroundVolumeForm hc ⟨S,B.gamma⟩ (Section5.nativeRVGroundDomain (gammaNativeRealBaseExtend U h)) :=
  ω.monoReal h

theorem gammaNativeRealBaseExtend_lift (U : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) {S : Set M} (h : B.real ⊆ S) :
    gammaNativeMeasuredLift (gammaNativeRealBaseExtend U h) (gammaNativeRealBaseExtendForm U ω h) =
      (gammaNativeMeasuredLift U ω).monoReal h := by
  rfl

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def GammaFullMeasuredBijection.monoReal {U V : GammaGroundMeasuredVFData hc B n}
    (f : GammaFullMeasuredBijection U V) {S : Set M} (h : B.real ⊆ S) :
    GammaFullMeasuredBijection (U.monoReal h) (V.monoReal h) where
  map := f.map.monoReal h
  measure p hp := f.measure p (independent_over_smaller_real_base h hp)

end DiamondIntegral.Section3
