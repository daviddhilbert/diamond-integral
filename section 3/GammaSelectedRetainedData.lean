import «section 3».GammaGenericSelectedHeadWitnesses
import «section 3».GammaRetainedFormRVImages
import «section 3».GammaOriginalBaseHeadTraces

/-! The selected-family induction keeps an actual mixed domain, finite
fibres after fixing its selected RV coordinates, and a Gamma form on its
retained RV labels. A traced head contraction stays in this same class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n k : ℕ}

structure GammaSelectedRetainedData
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (n k : ℕ) where
  arity : ℕ
  set : DefSet (M := M) Set.univ n arity
  gamma : GammaSetDefinable B (carrier set)
  select : Fin k → Fin arity
  finite : ∀ x t, {r | (x,r) ∈ carrier set ∧ r ∘ select = t}.Finite
  labels : GammaGroundDefSet hc B (rawRVSpace (M := M) arity)
  labels_mem : ∀ p : set, p.val.2 ∈ labels.carrier
  form : GammaGroundVolumeForm hc B labels

def GammaSelectedRetainedData.pointForm (U : GammaSelectedRetainedData hc B n k) :=
  gammaPointRetainedForm U.set U.gamma U.labels id (fun p => U.labels_mem p) U.form

def GammaSelectedRetainedData.schema (U : GammaSelectedRetainedData hc B n k) (N : ℕ) :=
  gammaMeasuredBoundedSelectedSchema U.set U.gamma U.select U.pointForm N

theorem GammaSelectedRetainedData.uniform_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (U : GammaSelectedRetainedData hc B n k) : ∃ N : ℕ, ∀ x : Fin n → VF (M := M), (U.schema N).valid (vfValues x) :=
  gammaMeasuredSelectedSchema_uniform_bound hκ hs hr hg U.set U.gamma U.select U.pointForm U.finite

structure GammaSelectedTracedHead (U : GammaSelectedRetainedData hc B (n+1) k) where
  head : HeadPreparation U.set
  trace : UniformRelativeTrace Set.univ (n+1) U.set head.target
  gamma : GammaUniformTrace (G := B) trace
  agrees : ∀ p, trace.toMap p = head.map p

namespace GammaSelectedTracedHead
variable {U : GammaSelectedRetainedData hc B (n+1) k}

theorem targetGamma (T : GammaSelectedTracedHead U) : GammaSetDefinable B (carrier T.head.target) :=
  (gammaUniformTraceIso T.trace T.gamma).target_definable (gammaLogicInput B)

theorem exists_original_base {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaSelectedRetainedData hc B (n+1) k) : Nonempty (GammaSelectedTracedHead U) := by
  obtain ⟨T,_,_,_,_,W,hW,hEq⟩ := gamma_original_base_head_preparation_traced hκ hs h00 hr U.set U.gamma
  exact ⟨⟨T,W,hW,hEq⟩⟩

theorem mapGamma (T : GammaSelectedTracedHead U) : GammaGraphDefinable B (pointMapGraph T.head.map) := by
  apply GammaGraphDefinable.congr (GammaUniformTrace.graph T.trace T.gamma)
  intro x y
  constructor
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(congrArg Subtype.val (T.agrees u)).symm.trans he⟩
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(congrArg Subtype.val (T.agrees u)).trans he⟩

def next {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (T : GammaSelectedTracedHead U) : GammaSelectedRetainedData hc B n (1+k) where
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
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (T : GammaSelectedTracedHead U) :
    (T.next hκ hs hr).pointForm = gammaHeadContractedForm T.head T.targetGamma U.labels U.labels_mem U.form :=
  gammaPointRVImageForm_pointForm T.head.contractedSet (gamma_headImage T.head.target T.targetGamma)
    U.labels (headSelectedLabelIndex T.head id) (gammaHeadContractedLabels_mem T.head U.labels U.labels_mem) U.form

theorem next_schema {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    {U : GammaSelectedRetainedData hc B (n+1) (k+1)} (T : GammaSelectedTracedHead U) (N : ℕ) :
    (T.next hκ hs hr).schema N = gammaSelectedHeadSchema T.head T.targetGamma U.select U.labels U.labels_mem U.form N := by
  change gammaMeasuredBoundedSelectedSchema _ _ _ (T.next hκ hs hr).pointForm N = _
  rw [T.next_pointForm hκ hs hr]
  rfl

end GammaSelectedTracedHead

def GammaGenericSelectedRelated (U V : GammaSelectedRetainedData hc B n (k+1)) : Prop :=
  ∃ N L : ℕ, (∀ x : Fin n → VF (M := M), (U.schema N).valid (vfValues x)) ∧
    (∀ x : Fin n → VF (M := M), (V.schema L).valid (vfValues x)) ∧
    ∀ x : Fin n → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaMeasuredRelationSchema (U.schema N).essential (V.schema L).essential, H.valid (vfValues x)

end DiamondIntegral.Section3
