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
import «section 6».RowFormCompatibleRVRefinement
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleTagBranchAssembly
import «section 6».RowFormCompatibleTagChainExtensions
import «section 6».RowFormCompatibleTagComponents
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredBranchFormConstancy
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredRVRefinementPreparation
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
import «section 6».FiniteTagPartitionPreparation
import «section 6».RowMeasuredComplementaryBranchPreparation
import «section 6».RowMeasuredPreparationSetTransport

/-! (Row-form version for Remark 6.20, translated from `MeasuredFiniteTagPartitionPreparation`.)
 A finite disjoint partition by retained RV labels assembles actual
measured preparations on its branches, preserving the full ambient form.
The empty ambient and empty partition are included. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_preparation_of_finite_tag_partition_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (m : ℕ) :
    ∀ (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
      (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier)
      (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
      (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
      (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
      (U : Fin m → DefSet (rawRVSpace (M := M) r) S),
      (∀ p ∈ A.carrier,∃ i,p.2 ∈ (U i).carrier) →
      (∀ i j u,u ∈ (U i).carrier → u ∈ (U j).carrier → i=j) →
      (ω : RowFormOn A qR) →
      (∀ i,∃ F : MeasuredCoordinatePreparationRow (G := G) (focusActive A (U i))
        (fun j => focusActive (P j) (U i)) (fun j _ hp => ⟨hPA j hp.1,hp.2⟩)
        (ω.comp (Map.inclusion (fun _ hp => hp.1))),
        FormCompatibleSynchronizedChainRow (G := G) (Fin k) (focusActive A (U i)) F.target F.map
          (fun j => focusActive (P j) (U i)) (ω.comp (Map.inclusion (fun _ hp => hp.1)))) →
      ∃ F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω,
        FormCompatibleSynchronizedChainRow (G := G) (Fin k) A F.target F.map P ω := by
  induction m with
  | zero =>
    intro A hA hD hRP hTag P hPA hP U hCover hDisjoint ω hPrep
    have hEmpty : ∀ p ∈ A.carrier,False := by
      intro p hp
      obtain ⟨i,hi⟩ := hCover p hp
      exact i.elim0
    have hPrepared (i) : IsRVPullback (P i).carrier := by
      apply Set.Subset.antisymm _ (subset_rvHull _)
      intro q hq
      obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
      exact False.elim (hEmpty p (hPA i hp))
    let J := PreparedSynchronizedFamily.identity (G := G) hA hD hRP P hPA hP hPrepared
    have hPhi : FormCompatibleSynchronizedChainRow (G := G) (Fin k) A J.target J.map P ω :=
      .identity A hA P hPA hP ω
    exact J.measured_form_compatible_target_row h00 hc hκ hs hv ω hPhi
      (fun p _ _ => False.elim (hEmpty p.val p.property))
  | succ m ih =>
    intro A hA hD hRP hTag P hPA hP U hCover hDisjoint ω hPrep
    obtain ⟨F,hF⟩ := hPrep 0
    let A' := focusActive A (rvTagComplement (U 0))
    let P' (i) := focusActive (P i) (rvTagComplement (U 0))
    have hP' (i) : (P' i).carrier ⊆ A'.carrier := fun _ hp => ⟨hPA i hp.1,hp.2⟩
    let Ω := ω.comp (Map.inclusion (fun p (hp : p ∈ A'.carrier) => hp.1))
    have hCover' : ∀ p ∈ A'.carrier,∃ i : Fin m,p.2 ∈ (U i.succ).carrier := by
      intro p hp
      obtain ⟨j,hj⟩ := hCover p hp.1
      have hTail : ∀ j : Fin (m+1),p.2 ∈ (U j).carrier → ∃ i : Fin m,p.2 ∈ (U i.succ).carrier :=
        Fin.cases (fun h => False.elim (hp.2 h)) (fun i h => ⟨i,h⟩)
      exact hTail j hj
    have hPrep' (i : Fin m) :
        ∃ J : MeasuredCoordinatePreparationRow (G := G) (focusActive A' (U i.succ))
          (fun j => focusActive (P' j) (U i.succ)) (fun j _ hp => ⟨hP' j hp.1,hp.2⟩)
          (Ω.comp (Map.inclusion (fun _ hp => hp.1))),
          FormCompatibleSynchronizedChainRow (G := G) (Fin k) (focusActive A' (U i.succ)) J.target J.map
            (fun j => focusActive (P' j) (U i.succ)) (Ω.comp (Map.inclusion (fun _ hp => hp.1))) := by
      obtain ⟨J,hJ⟩ := hPrep i.succ
      have hOut : ∀ u ∈ (U i.succ).carrier,u ∉ (U 0).carrier := by
        intro u hi hZero
        exact Fin.succ_ne_zero i (hDisjoint i.succ 0 u hi hZero)
      exact J.transport_sets_form_compatible_row hJ (focusActive_disjoint_complement A (U 0) (U i.succ) hOut).symm
        (fun j => (focusActive_disjoint_complement (P j) (U 0) (U i.succ) hOut).symm)
        (Ω.comp (Map.inclusion (fun _ hp => hp.1))) (fun _ => rfl)
    obtain ⟨J,hJ⟩ := ih A' (focusActive_properInvariant A hA _) (hD.mono (fun _ hp => hp.1))
      (focusActive_rvPullback A _ hRP) (fun p hp z hz => hTag p hp.1 z hz.1)
      P' hP' (fun i => focusActive_properInvariant (P i) (hP i) _) (fun i => U i.succ) hCover'
      (fun i j u hi hj => Fin.succ_injective _ (hDisjoint i.succ j.succ u hi hj)) Ω hPrep'
    exact measured_form_compatible_preparation_glue_complementary_tags_row h00 hc hκ hs hv
      A hA hD hRP hTag P hPA hP (U 0) ω F hF J hJ

end DiamondIntegral.Section6
