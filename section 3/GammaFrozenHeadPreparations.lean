import «section 3».GammaTracedHeadFibreJacobians
import Integration7.HeadCoordinateFibrePreparation
import IntegrationSection5.HeadPreparationExtension

/-! Freeze a generic complementary VF tuple in the specified traced
head preparation. Its actual unary canonical map has Jacobian one over
exactly the original base together with that tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a}

def gammaFrozenHeadPreparation (T : HeadPreparation U) (x : Fin n → VF (M := M)) :
    HeadPreparation (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)) :=
  (headCoordinateFibrePreparation T x).extendBase (Set.subset_univ _)

theorem gammaFrozenHeadPreparation_source
    (hU : GammaSetDefinable B (carrier U)) (x : Fin n → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
      (carrier (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _))) :=
  gamma_head_fibre U hU x

theorem gammaFrozenHeadPreparation_target (T : HeadPreparation U)
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
      (carrier (gammaFrozenHeadPreparation T x).target) :=
  gamma_head_coordinate_fibre_preparation_target T hTarget x

theorem gammaFrozenHeadPreparation_graph (T : HeadPreparation U)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (x : Fin n → VF (M := M)) :
    GammaGraphDefinable ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
      (pointMapGraph (gammaFrozenHeadPreparation T x).map) :=
  gamma_head_coordinate_fibre_preparation_map T hT x

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaFrozenHeadPreparation_jacobian_one
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation U) (W : UniformRelativeTrace Set.univ (n+1) U T.target)
    (hW : GammaUniformTrace (G := B) W) (hWT : ∀ u, W.toMap u = T.map u)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x) :
    let H := gammaFrozenHeadPreparation T x
    let hA := gammaFrozenHeadPreparation_source hW.source x
    let hTarget := (gammaUniformTraceIso W hW).target_definable (gammaLogicInput B)
    let hX := gammaFrozenHeadPreparation_target T hTarget x
    let hMap := gammaFrozenHeadPreparation_graph T (gammaTracedHead_map_graph_any_base T W hW hWT) x
    ∀ p, AlgebraicIndependent (vfParameterField (B.real ∪ Set.range (vfValues x))) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hA
        (gamma_coordinateCanonicalImage H.target hX 0)
        (⟨Equiv.ofBijective H.liftMap H.liftMap_bijective,
          gamma_composition_graph H.map (coordinateCanonicalBijection H.target 0) hMap
            (gamma_coordinateCanonical_graph H.target hX 0)⟩ : GammaIso _ _ _)).map p 1 := by
  intro H hA hTarget hX hMap p hp
  let hD := gamma_coordinateCanonicalImage T.target hTarget 0
  let hΓ := gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0)
    (gammaTracedHead_map_graph_any_base T W hW hWT) (gamma_coordinateCanonical_graph T.target hTarget 0)
  have hi : UnaryRelative T.liftMap 0 := by
    intro u j hj
    exact specialRelative_unaryRelative T.special u j hj
  let f := gammaHeadFibreBijection (hc := hc) hW.source hD T.liftMap T.liftMap_bijective hΓ hi x
  let hL := gamma_coordinateCanonicalImage H.target hX 0
  let hG := gamma_composition_graph H.map (coordinateCanonicalBijection H.target 0) hMap
    (gamma_coordinateCanonical_graph H.target hX 0)
  let g := Section5.nativeGammaPointBijection (hc := hc) hA hL
    (⟨Equiv.ofBijective H.liftMap H.liftMap_bijective,hG⟩ : GammaIso _ _ _)
  have hJ : HasMixedVFJacobianAt f.map p 1 := gammaHeadFibre_jacobian_one hW.source hD
    T.liftMap T.liftMap_bijective hΓ hi (gammaTracedHeadLift_jacobian_one hκ hs hr hv T W hW hWT) x hx p hp
  apply gammaGroundJacobian_transfer_VF hκ hs (small_union_range hκ B.real hr (vfValues x)) hv f.map g.map ?_ p hp 1 hJ
  intro q
  rw [gammaHeadFibreBijection_value,Section5.nativeGammaPointBijection_apply]
  rfl

end DiamondIntegral.Section3
