import «section 3».GammaFrozenHeadSelectedPresentations
import «section 3».GammaFrozenHeadGenericJacobians

/-! The specified generic head preparation gives an actual full
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
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a}

theorem gammaFrozenSelectedHead_native_measured_bridge_general
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation U)
    (hU : GammaSetDefinable B (carrier U))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hJac : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hU
        (gamma_coordinateCanonicalImage T.target hTarget 0)
        (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,
          gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hT
            (gamma_coordinateCanonical_graph T.target hTarget 0)⟩ : GammaIso B (carrier U) (carrier T.liftSet))).map p 1)
    (ρ : Fin k → Fin a) (hfin : ∀ y t, {r | (y,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x) :
    let Ux := extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)
    let H := gammaFrozenHeadPreparation T x
    let hAx := gammaFrozenHeadPreparation_source hU x
    let hfinx : ∀ z t, {r | (z,r) ∈ carrier Ux ∧ r ∘ ρ = t}.Finite := headFibre_selected_finite U ρ hfin x
    let Qx := Q.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left
    let hL := gammaFrozenHeadLabels (hc := hc) (x := x) hU Q hLabels
    let ωx := ω.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left
    let P' := gammaFrozenHeadSelectedPresentation T x ρ P
    ∃ F : GammaFullMeasuredBijection
      (gammaSelectedVFTailMeasuredData Ux ρ hAx hfinx (gammaPointRetainedForm Ux hAx Qx id (fun p => hL p) ωx))
      (gammaNativeMeasuredLift (gammaUniversalObject P'.toGamma) (gammaHeadSelectedNativeForm H ρ P' Qx hL ωx)),
      ∀ p, (F.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1 := by
  intro Ux H hAx hfinx Qx hL ωx P'
  let hHx := gammaFrozenHeadPreparation_target T hTarget x
  let hTx := gammaFrozenHeadPreparation_graph T hT x
  exact gammaSelectedHead_native_measured_bridge hκ hs (small_union_range hκ B.real hr (vfValues x)) hv
    H hAx hHx hTx (gammaFrozenHeadPreparation_jacobian_one_general hκ hs hr hv T hU hTarget hT hJac x hx)
    ρ hfinx P' Qx hL ωx

end DiamondIntegral.Section3
