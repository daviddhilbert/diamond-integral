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
import «section 6».RowExactGammaTransport
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedVariableRelease
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
import «section 6».RowPreparedCoverGammaForms

/-! (Row-form version for Remark 6.20, translated from `MeasuredSynchronizedTargets`.)
 An actual synchronized prepared map with Gamma constancy can
finish by regularization, retaining its common chain and every protected
restriction while giving the full tagged measured-preparation witness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem PreparedSynchronizedFamily.measured_target_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA)
    (ω : RowFormOn A qR)
    (hConst : ∀ p q : A,(F.map p).val.2=(F.map q).val.2 → (ω p).val=(ω q).val) :
    ∃ T : MeasuredCoordinatePreparationRow (G := G) A P hPA ω,
      SynchronizedCentripetalChain (G := G) (Fin k) A T.target T.map P := by
  let U := F.taggedTarget h00 hc hκ hs hv
  have hSpecial := U.chain.toChain.toSpecial
  let η := ω.comp (U.map.inverse (hSpecial.bijective h00))
  have hConstU (p q : A) (hpq : (U.map p).val.2=(U.map q).val.2) : (ω p).val=(ω q).val := by
    apply hConst p q
    funext j
    apply Subtype.ext
    have h := congrArg (fun v => (v (Fin.natAdd (n+1) j)).val) hpq
    change ((regularize (F.map p).val).2 (Fin.natAdd (n+1) j)).val=
      ((regularize (F.map q).val).2 (Fin.natAdd (n+1) j)).val at h
    simpa only [regularize,Fin.append_right] using h
  refine ⟨{
    arity := U.arity
    target := U.target
    map := U.map
    special := hSpecial
    proper := U.proper
    doublyBounded := U.doublyBounded
    prepared := U.pullback
    tagged := F.taggedTarget_tagged h00 hc hκ hs hv
    form := η
    transportRow := ?_
    constant := ?_
    pieces := fun i => ⟨(U.chain.atPiece i).literal_restriction h00 (hPA i),U.prepared i⟩ },U.chain⟩
  · intro p
    change (ω (U.map.inverse _ (U.map p))).val=(ω p).val
    rw [Map.inverse_apply]
  · intro x hx y hy hxy
    rw [rowFormExtension_at η ⟨x,hx⟩,rowFormExtension_at η ⟨y,hy⟩]
    apply hConstU (U.map.inverse _ ⟨x,hx⟩) (U.map.inverse _ ⟨y,hy⟩)
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hxy

end DiamondIntegral.Section6
