import «section 3».GammaFrozenHeadSelectedPresentations

/-! The specified global traced head preparation gives an actual full
measured bridge on each generic frozen tail, with every selected VF tail
fixed. Its base adds only the frozen VF parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a}

theorem gammaFrozenSelectedHead_native_measured_bridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation U) (W : UniformRelativeTrace Set.univ (n+1) U T.target)
    (hW : GammaUniformTrace (G := B) W) (hWT : ∀ u, W.toMap u = T.map u)
    (ρ : Fin k → Fin a) (hfin : ∀ y t, {r | (y,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x) :
    let Ux := extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)
    let H := gammaFrozenHeadPreparation T x
    let hAx := gammaFrozenHeadPreparation_source hW.source x
    let hfinx : ∀ z t, {r | (z,r) ∈ carrier Ux ∧ r ∘ ρ = t}.Finite := headFibre_selected_finite U ρ hfin x
    let Qx := Q.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left
    let hL := gammaFrozenHeadLabels (hc := hc) (x := x) hW.source Q hLabels
    let ωx := ω.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left
    let P' := gammaFrozenHeadSelectedPresentation T x ρ P
    ∃ F : GammaFullMeasuredBijection
      (gammaSelectedVFTailMeasuredData Ux ρ hAx hfinx (gammaPointRetainedForm Ux hAx Qx id (fun p => hL p) ωx))
      (gammaNativeMeasuredLift (gammaUniversalObject P'.toGamma) (gammaHeadSelectedNativeForm H ρ P' Qx hL ωx)),
      ∀ p, (F.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1 := by
  intro Ux H hAx hfinx Qx hL ωx P'
  let hTarget := (gammaUniformTraceIso W hW).target_definable (gammaLogicInput B)
  let hHx := gammaFrozenHeadPreparation_target T hTarget x
  let hTx := gammaFrozenHeadPreparation_graph T (gammaTracedHead_map_graph_any_base T W hW hWT) x
  exact gammaSelectedHead_native_measured_bridge hκ hs (small_union_range hκ B.real hr (vfValues x)) hv
    H hAx hHx hTx (gammaFrozenHeadPreparation_jacobian_one hκ hs hr hv T W hW hWT x hx)
    ρ hfinx P' Qx hL ωx

end DiamondIntegral.Section3
