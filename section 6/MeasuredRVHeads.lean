import «section 6».UniformMixedDifferentiability
import Section9.RVFiniteHead

/-! Actual finite coordinate heads carry constructed Gamma forms that
retain the original total weight. The source and target may select
different coordinates, while all old labels and bounds are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n k : ℕ}

def measuredRVHead (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.object v).FiniteFibres) : MeasuredRVObject (M := M) S k where
  object := (rvFiniteHead ⟨U.object,U.finiteVolume⟩ v hv).obj
  finiteVolume := hv
  nonzero u i := U.nonzero u (v i)
  form := gammaMapDiv hc (gammaMapMul hc U.form (rvVolumeGammaMap hc U.object))
    (rvVolumeGammaMap hc (rvFiniteHead ⟨U.object,U.finiteVolume⟩ v hv).obj)

theorem measuredRVHead_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.object v).FiniteFibres) (u : U.object.domain) :
    (measuredRVHead hc U v hv).totalWeight u = U.totalWeight u := by
  let W := measuredRVHead hc U v hv
  change ((gammaMapValue U.form u * gammaMapValue (rvVolumeGammaMap hc U.object) u) /
    gammaMapValue (rvVolumeGammaMap hc W.object) u) * W.volumeGamma u = U.totalWeight u
  rw [rvVolumeGammaMap_value hc U.object U.nonzero,rvVolumeGammaMap_value hc W.object W.nonzero]
  exact div_mul_cancel _ _

def measuredRVHeadIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (v w : Fin k → Fin n) (hv : (rvHeadVolume U.object v).FiniteFibres)
    (hw : (rvHeadVolume V.object w).FiniteFibres) :
    MeasuredRVIso (measuredRVHead hc U v hv) (measuredRVHead hc V w hw) where
  iso := rvIsoOfFiniteVolumeNonzero e.iso.hom.map (rvIso_map_bijective e.iso) hv hw
    (fun u i => U.nonzero u (v i)) (fun u i => V.nonzero u (w i))
  balance u := (measuredRVHead_totalWeight hc U v hv u).trans
    ((e.balance u).trans (measuredRVHead_totalWeight hc V w hw (e.iso.hom.map u)).symm)

theorem measuredRVHead_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.object v).FiniteFibres) (hU : U.doublyBounded) :
    (measuredRVHead hc U v hv).doublyBounded := by
  refine ⟨hU.1,?_⟩
  obtain ⟨γ,hγ⟩ := hU.2
  refine ⟨γ,?_⟩
  rintro t ⟨u,rfl⟩ i
  exact hγ (U.object.value u) ⟨u,rfl⟩ (v i)

end DiamondIntegral.Section6
