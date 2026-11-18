import «section 3».GammaUniformTraceJacobians
import «section 3».GammaGroundJacobianVFTransfer
import «section 3».GammaHeadMeasuredFibres
import «section 3».GammaTracedHeadMeasuredFibres

/-! A traced head map has Jacobian one on a generic frozen tail without
requiring finite RV fibres before the selected labels are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaHeadFibre_jacobian_one
    {A : DefSet (M := M) S (n+1) a} {D : DefSet (M := M) S (n+1) b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (f : Map A D) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0)
    (hJac : ∀ q, AlgebraicIndependent (vfParameterField B.real) q.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hA hD
        (⟨Equiv.ofBijective f hf,hΓ⟩ : GammaIso B (carrier A) (carrier D))).map q 1)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (p : gammaHeadFibreDomain (hc := hc) A hA x)
    (hp : AlgebraicIndependent (vfParameterField (B.real ∪ Set.range (vfValues x))) p.val.1) :
    HasMixedVFJacobianAt (gammaHeadFibreBijection hA hD f hf hΓ hi x).map p 1 := by
  have hp' : AlgebraicIndependent (tupleField (vfParameterField B.real) x) p.val.1 :=
    Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) => AlgebraicIndependent E p.val.1)
      (vfParameterField_union_tuple B.real x)) hp
  let q := gammaHeadFibreInclusion A hA x p
  have hq : AlgebraicIndependent (vfParameterField B.real) q.val.1 :=
    independent_cons_over_tuple_field (vfParameterField B.real) x p.val.1 hx hp'
  have hJ := hJac q hq
  have hJf : HasMixedVFJacobianAt (rawSpecialMap hc f) ⟨q.val,q.property⟩ 1 := by
    obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hJ
    refine ⟨H,⟨ρ,fun z hz => ?_⟩,hH⟩
    obtain ⟨hzA,hzF⟩ := hρ z hz
    refine ⟨hzA,?_⟩
    rw [Section5.nativeGammaPointBijection_apply,Section5.nativeGammaPointBijection_apply] at hzF
    exact hzF
  have hqInsert : (⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩ : rawSpecialSet hc A) = ⟨q.val,q.property⟩ :=
    Subtype.ext (coordinateInsert_head x p.val)
  have hJf' : HasMixedVFJacobianAt (rawSpecialMap hc f)
      ⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩ 1 := hqInsert.symm ▸ hJf
  have hJF := relative_mixed_vf_jacobian_on_coordinate_fibre hc f 0 hi (headFrozenTuple x)
    ⟨p.val,p.property⟩ 1 hJf'
  obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hJF
  refine ⟨H,⟨ρ,fun z hz => ?_⟩,hH⟩
  obtain ⟨hzA,hzF⟩ := hρ z hz
  refine ⟨hzA,?_⟩
  rw [gammaHeadFibreBijection_value,gammaHeadFibreBijection_value]
  exact hzF

theorem gammaTracedHead_map_graph_any_base
    {U : DefSet (M := M) S (n+1) a}
    (T : HeadPreparation U) (W : UniformRelativeTrace S (n+1) U T.target)
    (hW : GammaUniformTrace (G := B) W) (hWT : ∀ u, W.toMap u = T.map u) :
    GammaGraphDefinable B (pointMapGraph T.map) := by
  apply GammaGraphDefinable.congr (GammaUniformTrace.graph W hW)
  intro x y
  constructor
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(congrArg Subtype.val (hWT u)).symm.trans he⟩
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(congrArg Subtype.val (hWT u)).trans he⟩

theorem gammaTracedHeadLift_jacobian_one
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : DefSet (M := M) S (n+1) a}
    (T : HeadPreparation U) (W : UniformRelativeTrace S (n+1) U T.target)
    (hW : GammaUniformTrace (G := B) W) (hWT : ∀ u, W.toMap u = T.map u)
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hW.source)
    (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    let hTarget := (gammaUniformTraceIso W hW).target_definable (gammaLogicInput B)
    let hLift := gamma_coordinateCanonicalImage T.target hTarget 0
    let hΓ := gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0)
      (gammaTracedHead_map_graph_any_base T W hW hWT) (gamma_coordinateCanonical_graph T.target hTarget 0)
    HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hW.source hLift
      (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,hΓ⟩ : GammaIso B (carrier U) (carrier T.liftSet))).map p 1 := by
  intro hTarget hLift hΓ
  let f := Section5.nativeGammaPointBijection (hc := hc) hW.source hTarget (gammaUniformTraceIso W hW)
  let g := Section5.nativeGammaPointBijection (hc := hc) hW.source hLift
    (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,hΓ⟩ : GammaIso B (carrier U) (carrier T.liftSet))
  apply gammaGroundJacobian_transfer_VF hκ hs hr hv f.map g.map ?_ p hp 1
    (gammaUniformTrace_jacobian_one hκ hs hr hv W hW p hp)
  intro q
  rw [Section5.nativeGammaPointBijection_apply,Section5.nativeGammaPointBijection_apply]
  exact congrArg (fun z => z.val.1) (hWT ⟨q.val,q.property⟩)

end DiamondIntegral.Section3
