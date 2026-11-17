import «section 3».GammaMeasuredLabelUniformBounds
import «section 3».GammaRVParametersFromVF
import «section 3».GammaNativeMeasuredLifts
import IntegrationSection6.GammaVolumeSliceSchemata

/-! A native RV object with a Gamma form gives a measured family of
volume slices indexed by actual VF parameters. The parameters enter
through the language RV map; the original base is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ}

def gammaNativeVFSliceSchema (U : GammaObjectAt B Set.univ (p+k)) :
    GammaFiniteRVSchema B p (rvObjectArity U.object.obj) k (fun _ => .vf) :=
  (gammaRVParametersFromVF B p).object (gammaVolumeSliceSchema U.toGamma)

theorem gammaNativeVFSliceSchema_domain (U : GammaObjectAt B Set.univ (p+k))
    (x : Fin p → VF (M := M)) (r : Fin (rvObjectArity U.object.obj) → RV (M := M)) :
    r ∈ (gammaNativeVFSliceSchema U).rowDomain (vfValues x) ↔
      ∃ u : rvObjectDomain U.object.obj, u.val = r ∧
        (rvObjectVolume U.object.obj u).val ∘ Fin.castAdd k = fun j => @rv M sM hM (x j) := by
  have h := gammaRVParametersFromVF_rows (gammaVolumeSliceSchema U.toGamma) x
  exact ((Set.ext_iff.mp h.domains r).symm).trans
    (gammaVolumeSliceSchema_domain U.toGamma (fun j => @rv M sM hM (x j)) r)

theorem gammaNativeVFSliceSchema_volume (U : GammaObjectAt B Set.univ (p+k))
    (x : Fin p → VF (M := M)) (r : Fin (rvObjectArity U.object.obj) → RV (M := M))
    (v : Fin k → RV (M := M)) :
    (gammaNativeVFSliceSchema U).rowVolume (vfValues x) r v ↔
      ∃ u : rvObjectDomain U.object.obj, u.val = r ∧
        (rvObjectVolume U.object.obj u).val = Fin.append (fun j => @rv M sM hM (x j)) v := by
  have h := gammaRVParametersFromVF_rows (gammaVolumeSliceSchema U.toGamma) x
  have he := congrFun (congrFun h.volumes r) v
  exact (Iff.of_eq he).symm.trans (gammaVolumeSliceSchema_volume U.toGamma (fun j => @rv M sM hM (x j)) r v)

theorem gammaNativeVFSliceSchema_finiteRows (U : GammaObjectAt B Set.univ (p+k))
    (x : Fin p → VF (M := M)) : (gammaNativeVFSliceSchema U).finiteRow (vfValues x) := by
  have h := gammaRVParametersFromVF_rows (gammaVolumeSliceSchema U.toGamma) x
  have hfin := gammaVolumeSliceSchema_finiteRows U.toGamma (fun j => @rv M sM hM (x j))
  unfold gammaNativeVFSliceSchema
  unfold GammaFiniteRVSchema.finiteRow at hfin ⊢
  rw [← h.domains,← h.volumes]
  exact hfin

def gammaNativeMeasuredVFSliceSchema (U : GammaObjectAt B Set.univ (p+k))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (N : ℕ) :
    GammaMeasuredRVSchema hc B p (rvObjectArity U.object.obj) k (fun _ => .vf) :=
  gammaMeasuredLabelSchema ((gammaNativeVFSliceSchema U).withBound N) ω

theorem gammaNativeMeasuredVFSliceSchema_uniform_bound
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (U : GammaObjectAt B Set.univ (p+k))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    ∃ N : ℕ, ∀ x : Fin p → VF (M := M), (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x) := by
  obtain ⟨N,hN⟩ := gammaMeasuredLabelSchema_uniform_bound hκ hs hr hg (gammaNativeVFSliceSchema U) ω
    (by
      intro z hz
      exact gammaNativeVFSliceSchema_finiteRows U (fun j => ⟨z j,hz j⟩)) (by
      intro z hz r hr
      obtain ⟨u,hu,_⟩ := (gammaNativeVFSliceSchema_domain U (fun j => ⟨z j,hz j⟩) r).mp hr
      exact (Section5.nativeRVGroundDomain_carrier U).ge (hu ▸ u.property))
  exact ⟨N,fun x => hN (vfValues x) (fun j => (x j).property)⟩

end DiamondIntegral.Section3
