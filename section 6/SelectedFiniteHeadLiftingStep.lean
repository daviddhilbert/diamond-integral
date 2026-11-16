import «section 6».MeasuredFiniteHeadLiftingStep
import «section 6».MeasuredRVLiftingInductionStep
import «section 6».MeasuredRVReindexingTransfer
import Section9.FiniteHeadCover

/-! The smaller-rank hypothesis supplies the actual finite-head lift
and repairs its affine extension. Separate selected source and target
heads are placed first and then returned to the original coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k m : ℕ}

theorem exists_measured_rv_lift_of_selected_finite_heads_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    {U V : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (e : MeasuredRVIso U V)
    (v w : Fin (k+1) ↪ Fin ((k+1)+m))
    (hU : (rvHeadVolume U.object v).FiniteFibres)
    (hV : (rvHeadVolume V.object w).FiniteFibres) (j : Fin m)
    (hLower : ∀ {d : ℕ} (A B : MeasuredRVObject (M := M) (S : Set M) d)
      (f : MeasuredRVIso A B), rvDim A.object.domain < k+1 → Nonempty (EverywhereMeasuredRVLift f)) :
    Nonempty (EverywhereMeasuredRVLift e) := by
  obtain ⟨a,ha⟩ := exists_head_reindex v
  obtain ⟨b,hb⟩ := exists_head_reindex w
  let l := productLeft (k+1) m
  let UR := U.reindexVolume a
  let VR := V.reindexVolume b
  let eR := measuredRVReindexedIso e a b
  have hUR : (rvHeadVolume UR.object l).FiniteFibres := by
    have he : rvHeadVolume UR.object l = rvHeadVolume U.object v := by
      apply Map.ext
      intro u
      apply Subtype.ext
      funext i
      exact congrArg (U.object.value u) (ha i)
    rw [he]
    exact hU
  have hVR : (rvHeadVolume VR.object l).FiniteFibres := by
    have he : rvHeadVolume VR.object l = rvHeadVolume V.object w := by
      apply Map.ext
      intro u
      apply Subtype.ext
      funext i
      exact congrArg (V.object.value u) (hb i)
    rw [he]
    exact hV
  let eH := measuredRVHeadIso hc eR l l hUR hVR
  obtain ⟨F⟩ := exists_everywhere_measured_rv_lift_of_smaller_label_lifts_vfGenerated
    h00 hc hκ hs hv S B hsmall hΓ eH
    (fun D hD hDim => hLower _ _ (eH.restrict D hD) hDim)
  obtain ⟨H⟩ := exists_measured_rv_lift_of_finite_headLift_vfGenerated
    h00 hc hκ hs hv S B hsmall hΓ eR hUR hVR F j
    (fun D hD hDim => hLower _ _ (eR.restrict D hD) hDim)
  exact ⟨measuredRVUnreindexLift e a b H⟩

end DiamondIntegral.Section6
