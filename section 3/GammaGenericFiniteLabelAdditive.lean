import «section 3».GammaPreparedMeasuredFamilies
import «section 3».GammaAdditiveIndexedFamilyComparison
import «section 3».GammaNativeTypedMeasuredBridge

/-! Generic constrained finite-label witnesses preserve every additive
elementary invariant. This is the existing finite-row preparation proof
with its finite-derivation information retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {W : Type*} [AddCommMonoid W]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaGeneric_finite_label_additive_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (F : GammaFiniteRVSchema B (n+1) (rvObjectArity U.object.obj) 0)
    (G : GammaFiniteRVSchema B (n+1) (rvObjectArity V.object.obj) 0)
    (hF : ∀ x : Fin (n+1) → VF (M := M), F.valid (vfValues x))
    (hG : ∀ x : Fin (n+1) → VF (M := M), G.valid (vfValues x))
    (hSourceU : carrier (typedLift U.object.obj) = vfSchemaSource Set.univ F)
    (hSourceV : carrier (typedLift V.object.obj) = vfSchemaSource Set.univ G)
    (hWitness : ∀ x : Fin (n+1) → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaRelationFormula B (n+1) (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) (fun _ => .vf),
        H.val ⊆ gammaParametricFormConstraint (Section5.nativeRVGroundDomain U)
          (Section5.nativeRVGroundDomain V) ω π (fun _ => .vf) ∧
            (gammaFiniteRowChartSchema F G H).valid (vfValues x)) :
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V π := by
  let X := PresentedSet.univ (pointSpace (M := M) (n+1) 0) (C.base : Set M)
  have hX : GammaSetDefinable B (carrier X) :=
    (gammaLogicInput B).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) (n+1) 0) B.real))
  have hAF : ∀ x : X, F.rowDomain (rawVFParameter x.val) ⊆
      (Section5.nativeRVGroundDomain (hc := hc) U).carrier := by
    intro x r hr'
    have hx : (x.val.1,r) ∈ carrier (typedLift U.object.obj) := hSourceU.ge ⟨Set.mem_univ _,hr'⟩
    exact (gammaPresentationLabelAt (hc := hc) U (normalizedTypedLift_presents U.object.obj) ⟨(x.val.1,r),hx⟩).property
  have hDG : ∀ x : X, G.rowDomain (rawVFParameter x.val) ⊆
      (Section5.nativeRVGroundDomain (hc := hc) V).carrier := by
    intro x r hr'
    have hx : (x.val.1,r) ∈ carrier (typedLift V.object.obj) := hSourceV.ge ⟨Set.mem_univ _,hr'⟩
    exact (gammaPresentationLabelAt (hc := hc) V (normalizedTypedLift_presents V.object.obj) ⟨(x.val.1,r),hx⟩).property
  obtain ⟨C',hCC',l,Z,T,hT,hZ,BP,hFA,hGA,hAF',hDG',hPrepared⟩ :=
    gammaGeneric_measured_family_preparation hκ hs hr hg C hBC X hX F G
      (fun x => hF x.val.1) (fun x => hG x.val.1)
      (Section5.nativeRVGroundDomain U) (Section5.nativeRVGroundDomain V) ω π hAF hDG hWitness
  let K := GammaParameterRecode.prepared T hT
  have hDF : ∀ t ∈ preparedKeyDomain Z, (K.object F).valid (rvValues t) := by
    rintro t ⟨q,rfl⟩
    exact K.object_valid F _ _ (fun j => ((flatKey q.val).2 j).property) (hFA q) (hF (T.inverseMap q).val.1)
  have hDGv : ∀ t ∈ preparedKeyDomain Z, (K.object G).valid (rvValues t) := by
    rintro t ⟨q,rfl⟩
    exact K.object_valid G _ _ (fun j => ((flatKey q.val).2 j).property) (hGA q) (hG (T.inverseMap q).val.1)
  let P := (K.object F).indexedPresentation BP hDF
  let Q := (K.object G).indexedPresentation BP hDGv
  obtain ⟨E⟩ := hPrepared P Q
  let hCU : (C'.base : Set M) ⊆ Set.univ := Set.subset_univ _
  let TU := T.extendBase hCU
  have hTU := GammaChainDefinable.extendBase B T.chain hCU hT
  have hHXU : ∀ q ∈ carrier (typedLift U.object.obj), (q.1,Fin.elim0) ∈ carrier (extendBase (extendBase X hCC') hCU) :=
    fun _ _ => Set.mem_univ _
  have hHXV : ∀ q ∈ carrier (typedLift V.object.obj), (q.1,Fin.elim0) ∈ carrier (extendBase (extendBase X hCC') hCU) :=
    fun _ _ => Set.mem_univ _
  obtain ⟨LU⟩ := gammaSpecialFamilyLift_exists TU hTU (typedLift U.object.obj) (gammaNativeTypedLift_definable U) hHXU
  obtain ⟨LV⟩ := gammaSpecialFamilyLift_exists TU hTU (typedLift V.object.obj) (gammaNativeTypedLift_definable V) hHXV
  have hRowsF : ∀ q : extendBase Z hCU, GammaSchemaRowAgreement F
      (rawVFParameter (TU.inverseMap q).val) (K.object F) (rawPreparedKey q.val) := by
    intro q
    have he := congrArg rawVFParameter (T.extendBase_inverse hCU q)
    exact Eq.mp (congrArg (fun z => GammaSchemaRowAgreement F z (K.object F) (rawPreparedKey q.val)) he.symm)
      (hFA ⟨q.val,q.property⟩)
  have hRowsG : ∀ q : extendBase Z hCU, GammaSchemaRowAgreement G
      (rawVFParameter (TU.inverseMap q).val) (K.object G) (rawPreparedKey q.val) := by
    intro q
    have he := congrArg rawVFParameter (T.extendBase_inverse hCU q)
    exact Eq.mp (congrArg (fun z => GammaSchemaRowAgreement G z (K.object G) (rawPreparedKey q.val)) he.symm)
      (hGA ⟨q.val,q.property⟩)
  have HU := gammaSpecial_indexed_family_additive_comparison hκ hs h00 hr χ hχ U
    (normalizedTypedLift_presents U.object.obj) TU hHXU LU F (K.object F) hSourceU hRowsF BP P ω hAF'
  have HV := gammaSpecial_indexed_family_additive_comparison hκ hs h00 hr χ hχ V
    (normalizedTypedLift_presents V.object.obj) TU hHXV LV G (K.object G) hSourceV hRowsG BP Q π hDG'
  exact HU.trans ((gammaNativeAdditiveValue_hom χ _ _ _ _ E).trans HV.symm)

end DiamondIntegral.Section3
