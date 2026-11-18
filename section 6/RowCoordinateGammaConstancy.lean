import «section 6».RowArbitraryCoordinateBranches
import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
import «section 6».RowRVRefinementGammaForms
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowVFReindexedGammaForms
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».RowSemanticGammaBranchDescent
import «section 6».PermutedCoordinateBundles

/-! (Row-form version for Remark 6.20, translated from `CoordinateGammaConstancy`.)
 Semantic form constancy in an arbitrary VF coordinate gives an
actual original-base Gamma descent through that coordinate projection,
with inherited open levels. No radius or individual Gamma name is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def CoordinateGammaConstantRow (j : Fin (n+1))
    (ω : RowFormOn A qR) : Prop :=
  ∀ p q : A,(∀ i,i ≠ j → p.val.1 i=q.val.1 i) → p.val.2=q.val.2 → (ω p).val=(ω q).val

theorem CoordinateGammaConstantRow.reindexed_projection_constant_row
    {j : Fin (n+1)} {ω : RowFormOn A qR}
    (h : CoordinateGammaConstantRow j ω) (e : Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n)=j) :
    ∀ p ∈ (reindexedVFSet A e).carrier,∀ q ∈ (reindexedVFSet A e).carrier,
      Fin.init p.1=Fin.init q.1 → p.2=q.2 →
      rowFormExtension (reindexedGammaFormRow ω e) p=rowFormExtension (reindexedGammaFormRow ω e) q := by
  intro p hp q hq hInit hTags
  rw [rowFormExtension_at _ ⟨p,hp⟩,rowFormExtension_at _ ⟨q,hq⟩]
  apply h (reindexVFInverseMapRow A e ⟨p,hp⟩) (reindexVFInverseMapRow A e ⟨q,hq⟩) _ hTags
  intro i hi
  have hBefore : e.symm i ≠ Fin.last n := by
    intro hn
    apply hi
    exact (e.apply_symm_apply i).symm.trans ((congrArg e hn).trans he)
  exact Fin.lastCases (motive := fun k => k ≠ Fin.last n → p.1 k=q.1 k)
    (fun hn => False.elim (hn rfl)) (fun k _ => congrFun hInit k) (e.symm i) hBefore

theorem reindexedGammaForm_levels_open_row
    (ω : RowFormOn A qR) (e : Fin (n+1) ≃ Fin (n+1))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ (reindexedVFSet A e).carrier ∧
      rowFormExtension (reindexedGammaFormRow ω e) (x,u)=γ} := by
  intro u γ
  have he : {x : Fin (n+1) → VF M | (x,u) ∈ (reindexedVFSet A e).carrier ∧
      rowFormExtension (reindexedGammaFormRow ω e) (x,u)=γ}=
      (fun x : Fin (n+1) → VF M => x ∘ e.symm) ⁻¹'
        {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ} := by
    ext x
    constructor
    · rintro ⟨hx,hγ⟩
      have hOld := (mem_reindexedVFSet A e (x,u)).mp hx
      refine ⟨hOld,?_⟩
      rw [rowFormExtension_at _ ⟨_,hx⟩] at hγ
      exact (rowFormExtension_at ω ⟨_,hOld⟩).trans hγ
    · rintro ⟨hx,hγ⟩
      have hNew := (mem_reindexedVFSet A e (x,u)).mpr hx
      refine ⟨hNew,?_⟩
      rw [rowFormExtension_at _ ⟨_,hNew⟩]
      exact (rowFormExtension_at ω ⟨_,hx⟩).symm.trans hγ
  rw [he]
  exact (hLevels u γ).preimage (continuous_pi (fun i => continuous_apply (e.symm i)))

theorem CoordinateGammaConstantRow.exists_coordinate_descent_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier)
    {j : Fin (n+1)} {ω : RowFormOn A qR}
    (h : CoordinateGammaConstantRow j ω) (e : Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n)=j)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∃ η : RowFormOn (coordinateProjection A e) qR,
      (∀ q : reindexedVFSet A e,η ((vfDropLast (reindexedVFSet A e)).toImage q)=reindexedGammaFormRow ω e q) ∧
      ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (coordinateProjection A e).carrier ∧ rowFormExtension η (x,u)=γ} := by
  let hConst := h.reindexed_projection_constant_row e he
  let η := coordinateGammaDescentRow (reindexedGammaFormRow ω e) hConst
  have hη := coordinateGammaDescent_at_row (reindexedGammaFormRow ω e) hConst
  exact ⟨η,hη,descended_gamma_levels_open_row h00 hc linear hκ hs hv hsmall hΓ
    (reindexedVFSet_properInvariant A e hA) (reindexedGammaFormRow ω e)
    (reindexedGammaForm_levels_open_row ω e hLevels) η hη⟩

end DiamondIntegral.Section6
