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
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
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
import «section 6».UnaryBaseFocusFreezing
import «section 6».RowGammaFormFreezing
import «section 6».TailContinuousFullFocusGraphs

/-! (Row-form version for Remark 6.20, translated from `MeasuredUnaryBaseFocusFreezing`.)
 Repair a current joint focus while preserving both its protected
joint domains and the unary domain of the actual parameter map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.TailContinuousFullFocusGraphData
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem exists_measured_frozen_full_graph_with_unary_base_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (F : TailContinuousFullFocusGraphData (G := G) A)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hP : ∀ i,ProperInvariant S (P i).carrier)
    (B : DefSet (rawMixedSpace (M := M) 1 t) S) (hB : ProperInvariant S B.carrier)
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∃ D : FMT.FocusFreezingData (focusActive A F.activeTags),
      (∀ u,Continuous (FMT.focusFibre (D.frozenMap F.map) u)) ∧
      (∀ E : D.balls,FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) ∧
      (∀ i,∀ E : D.balls,FMT.CoordinateProductDomain (P i).carrier (FMT.vfOpenBall E.val) (D.centers E) 0) ∧
      (∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) ∧
      ∀ γ,∀ E : D.balls,FMT.CoordinateProductDomain
        {p | p ∈ A.carrier ∧ rowFormExtension ω p=γ} (FMT.vfOpenBall E.val) (D.centers E) 0 := by
  let H : Fin (k+1) → Set (Mixed M (n+1) r) := Fin.cons A.carrier (fun i => (P i).carrier)
  have hH : ∀ i,ProperInvariant S (H i) := Fin.cases F.proper hP
  obtain ⟨δ₀,hδ₀,hδ₀1,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  obtain ⟨δB,hδB,hδB1,hInvB⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hB
  obtain ⟨ε,hε,hε1,hInvA,hInvLevels⟩ := gamma_form_all_levels_uniform_invariant_row h00 hc linear hκ hs hv hsmall hΓ
    F.proper (rowFormExtension ω) (rowFormExtension_graph_definable ω) hLevels
  let δ := max (max δ₀ δB) ε
  have hδ := gamma_max_named (max δ₀ δB) ε (gamma_max_named δ₀ δB hδ₀ hδB) hε
  have hδ₀δ : δ₀ ≤ δ := (le_max_left δ₀ δB).trans (le_max_left (max δ₀ δB) ε)
  have hδBδ : δB ≤ δ := (le_max_right δ₀ δB).trans (le_max_left (max δ₀ δB) ε)
  have hδ1 : 1 ≤ δ := hδ₀1.trans hδ₀δ
  have hJoint (i) (u) : AlphaInvariant (fun _ => δ) (vfFibre (H i) u) :=
    (hInv i u).larger_radius (fun _ => hδ₀δ)
  have hBase (u) : AlphaInvariant (fun _ => δ) (vfFibre B.carrier u) :=
    (hInvB u).larger_radius (fun _ => hδBδ)
  have hForm (γ) (u) : AlphaInvariant (fun _ => δ) (vfFibre {p | p ∈ A.carrier ∧ rowFormExtension ω p=γ} u) :=
    (hInvLevels γ u).larger_radius (fun _ => le_max_right _ _)
  have hActive (u) : AlphaInvariant (fun _ => δ) (vfFibre (focusActive A F.activeTags).carrier u) := by
    intro a b hab
    exact and_congr (hJoint 0 u a b hab) Iff.rfl
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00
    V S hV hVS hSV hnt δ hδ1 hδ
  obtain ⟨D,hCont,hDomains⟩ := FMT.exists_continuous_focus_freezing_with_all_domains
    h00 hc hκ hs hsmall hv δ hActive s hs0 hsdef hδs.le F.map F.continuousTail
  exact ⟨D,hCont,hDomains (n+1) r A.carrier (hJoint 0) 0,
    (fun i => hDomains (n+1) r (P i).carrier (hJoint i.succ) 0),hDomains 1 t B.carrier hBase 0,
    fun γ => hDomains (n+1) r _ (hForm γ) 0⟩

end DiamondIntegral.Section6.TailContinuousFullFocusGraphData
