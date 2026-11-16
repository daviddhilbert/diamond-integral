import «section 6».SelectedFiniteHeadLiftingStep
import «section 6».FiniteMeasuredRVLiftFieldBase

/-! Everywhere measured RV lifting in every degree, by strong
induction on the actual RV dimension of the original label domain.
The full-degree case repairs the generic lift. Smaller-degree heads
and constructed affine tails handle every positive codimension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_everywhere_measured_rv_lift_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {n : ℕ} {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V) :
    Nonempty (EverywhereMeasuredRVLift e) := by
  have hRank : ∀ r : ℕ,∀ {d : ℕ} (A B : MeasuredRVObject (M := M) (S : Set M) d)
      (f : MeasuredRVIso A B),rvDim A.object.domain = r → Nonempty (EverywhereMeasuredRVLift f) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro d A C f hDim
      cases r with
      | zero =>
        have hFin := (rvDim_eq_zero_iff_finite A.object.domain).mp hDim
        obtain ⟨g,hg,hLabel,_,hMeasure⟩ := exists_finite_measured_rv_lift_vfGenerated
          h00 hc hs hv S B hsmall hnt f hFin
        exact ⟨⟨g,hg,hLabel,hMeasure⟩⟩
      | succ k =>
        have hLower : ∀ {d : ℕ} (P Q : MeasuredRVObject (M := M) (S : Set M) d)
            (g : MeasuredRVIso P Q),rvDim P.object.domain < k+1 → Nonempty (EverywhereMeasuredRVLift g) := by
          intro d P Q g h
          exact ih (rvDim P.object.domain) h P Q g rfl
        have hkd : k+1 ≤ d := by
          have h := rvDim_mapImage_eq_of_finiteFibres hc (rvExchangeInput_of_earlier hκ.le hs h00)
            hs hsmall A.object.volume A.finiteVolume
          rw [← hDim,← h]
          exact rvDim_le_arity A.object.volume.image
        obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkd
        cases m with
        | zero =>
          exact exists_everywhere_measured_rv_lift_of_smaller_label_lifts_vfGenerated
            h00 hc hκ hs hv S B hsmall hΓ f
            (fun D hD hSmall => hLower _ _ (f.restrict D hD) hSmall)
        | succ m =>
          obtain ⟨a,b,P,hCover⟩ := exists_measured_rv_finite_head_cover hc h00 hκ.le hs hsmall
            (Nat.le_add_right (k+1) (m+1)) f hDim.le
          apply exists_everywhere_measured_lift_of_finite_cover f
            (fun i => (P i).domain) (fun i => (P i).subset) hCover
          intro i
          exact exists_measured_rv_lift_of_selected_finite_heads_vfGenerated
            h00 hc hκ hs hv S B hsmall hΓ (f.restrict (P i).domain (P i).subset)
            (P i).sourceSelect (P i).targetSelect (P i).sourceFinite (P i).targetFinite
            (0 : Fin (m+1)) hLower
  exact hRank (rvDim U.object.domain) U V e rfl

end DiamondIntegral.Section6
