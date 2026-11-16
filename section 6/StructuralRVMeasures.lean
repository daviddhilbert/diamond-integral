import «section 6».RVGammaVolumeMaps

/-! Constructed Gamma forms encoding the structural RV Jacobian of an
arbitrary finite-volume RV isomorphism. No measured balance hypothesis
is added to the unmeasured lifting problem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def structuralMeasuredRVTarget (hc : CanonicalStructure.IsCanonical (M := M))
    (V : RVObject (M := M) S n) (hVF : V.volume.FiniteFibres)
    (hV : ∀ v, ∀ i, (V.value v i).val ≠ iRVZero) : MeasuredRVObject (M := M) S n :=
  ⟨V,hVF,hV,gammaOneMap hc V.domain⟩

def structuralMeasuredRVSource (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : RVObject (M := M) S n} (e : U ≅ V) (hUF : U.volume.FiniteFibres)
    (hU : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero) : MeasuredRVObject (M := M) S n :=
  ⟨U,hUF,hU,gammaMapDiv hc ((rvVolumeGammaMap hc V).comp e.hom.map) (rvVolumeGammaMap hc U)⟩

def structuralMeasuredRVIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero)
    (hV : ∀ v, ∀ i, (V.value v i).val ≠ iRVZero) :
    MeasuredRVIso (structuralMeasuredRVSource hc e hUF hU) (structuralMeasuredRVTarget hc V hVF hV) := by
  refine ⟨e,fun u => ?_⟩
  change (gammaMapValue (rvVolumeGammaMap hc V) (e.hom.map u) /
    gammaMapValue (rvVolumeGammaMap hc U) u) * rvVolumeGamma (U.value u) (hU u) =
    1 * rvVolumeGamma (V.value (e.hom.map u)) (hV (e.hom.map u))
  rw [rvVolumeGammaMap_value hc V hV,rvVolumeGammaMap_value hc U hU,div_mul_cancel,one_mul]

end DiamondIntegral.Section6
