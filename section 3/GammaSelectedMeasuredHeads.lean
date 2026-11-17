import «section 3».GammaGenericGeneralHeadWitnesses
import «section 3».GammaGenericSelectedHeadPropagation

/-! The selected head induction accepts any specified original-ground head with its actual generic Jacobian, including the rectangle preparations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n k : ℕ}

structure GammaSelectedMeasuredHead (U : GammaSelectedRetainedData hc B (n+1) k) where
  head : HeadPreparation U.set
  targetGamma : GammaSetDefinable B (carrier head.target)
  mapGamma : GammaGraphDefinable B (pointMapGraph head.map)
  jacobian : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
    HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) U.gamma
      (gamma_coordinateCanonicalImage head.target targetGamma 0)
      (⟨Equiv.ofBijective head.liftMap head.liftMap_bijective,
        gamma_composition_graph head.map (coordinateCanonicalBijection head.target 0) mapGamma
          (gamma_coordinateCanonical_graph head.target targetGamma 0)⟩ : GammaIso B (carrier U.set) (carrier head.liftSet))).map p 1

namespace GammaSelectedMeasuredHead
variable {U : GammaSelectedRetainedData hc B (n+1) k}

def next {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (T : GammaSelectedMeasuredHead U) : GammaSelectedRetainedData hc B n (1+k) where
  arity := 1+T.head.arity
  set := T.head.contractedSet
  gamma := gamma_headImage T.head.target T.targetGamma
  select := headVolumeIndex T.head U.select
  finite := head_selected_fibres_finite hκ hs hr T.head
    T.mapGamma T.targetGamma U.select U.finite
  labels := gammaPointRVImage T.head.contractedSet (gamma_headImage T.head.target T.targetGamma)
  labels_mem := gammaPointRVImage_mem T.head.contractedSet (gamma_headImage T.head.target T.targetGamma)
  form := gammaPointRVImageForm T.head.contractedSet (gamma_headImage T.head.target T.targetGamma)
    U.labels (headSelectedLabelIndex T.head id) (gammaHeadContractedLabels_mem T.head U.labels U.labels_mem) U.form

theorem next_pointForm {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (T : GammaSelectedMeasuredHead U) :
    (T.next hκ hs hr).pointForm = gammaHeadContractedForm T.head T.targetGamma U.labels U.labels_mem U.form :=
  gammaPointRVImageForm_pointForm T.head.contractedSet (gamma_headImage T.head.target T.targetGamma)
    U.labels (headSelectedLabelIndex T.head id) (gammaHeadContractedLabels_mem T.head U.labels U.labels_mem) U.form

theorem next_schema {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    {U : GammaSelectedRetainedData hc B (n+1) (k+1)} (T : GammaSelectedMeasuredHead U) (N : ℕ) :
    (T.next hκ hs hr).schema N = gammaSelectedHeadSchema T.head T.targetGamma U.select U.labels U.labels_mem U.form N := by
  change gammaMeasuredBoundedSelectedSchema _ _ _ (T.next hκ hs hr).pointForm N = _
  rw [T.next_pointForm hκ hs hr]
  rfl

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def ofTraced {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : GammaSelectedTracedHead U) : GammaSelectedMeasuredHead U :=
  ⟨T.head,T.targetGamma,T.mapGamma,gammaTracedHeadLift_jacobian_one hκ hs hr hv T.head T.trace T.gamma T.agrees⟩

end GammaSelectedMeasuredHead

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem GammaGenericSelectedRelated.measured_head
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : GammaSelectedRetainedData hc B (n+1) (k+1)}
    (h : GammaGenericSelectedRelated U V) (T : GammaSelectedMeasuredHead U) (E : GammaSelectedMeasuredHead V) :
    GammaGenericSelectedRelated (k := 1+k) (T.next hκ.le hs hr) (E.next hκ.le hs hr) := by
  obtain ⟨N,L,hN,hL,hWitness⟩ := h
  obtain ⟨NT,hNT⟩ := (T.next hκ.le hs hr).uniform_bound hκ.le hs hr hg
  obtain ⟨NE,hNE⟩ := (E.next hκ.le hs hr).uniform_bound hκ.le hs hr hg
  refine ⟨NT,NE,hNT,hNE,?_⟩
  intro x hx
  have hFT := Eq.mp (congrArg (fun F => F.valid (vfValues x)) (T.next_schema hκ.le hs hr NT)) (hNT x)
  have hFE := Eq.mp (congrArg (fun F => F.valid (vfValues x)) (E.next_schema hκ.le hs hr NE)) (hNE x)
  have H := gammaGeneric_selected_general_head_formula_witness hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1
    T.head E.head U.gamma V.gamma T.targetGamma E.targetGamma T.mapGamma E.mapGamma T.jacobian E.jacobian
    U.select V.select U.finite V.finite U.labels V.labels U.labels_mem V.labels_mem U.form V.form
    N L hWitness NT NE x hx hFT hFE
  rw [T.next_schema hκ.le hs hr NT,E.next_schema hκ.le hs hr NE]
  exact H

end DiamondIntegral.Section3
