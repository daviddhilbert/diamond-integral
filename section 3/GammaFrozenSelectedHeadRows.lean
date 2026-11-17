import «section 3».GammaFrozenSelectedHeadMeasuredBridge
import «section 3».GammaMeasuredSelectedBounds

/-! Frozen selected head objects have exactly the full structural-volume
and Gamma-density rows of the original contracted family. Zero-volume
rows are present until the existing normalization is applied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a k : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a}
variable (T : HeadPreparation U) (hU : GammaSetDefinable B (carrier U))
variable (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M))
variable (ρ : Fin k → Fin a)
variable (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x)
variable (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q)

def gammaFrozenSelectedHeadForm :=
  gammaHeadSelectedNativeForm (gammaFrozenHeadPreparation T x) ρ (gammaFrozenHeadSelectedPresentation T x ρ P)
    (Q.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left)
    (gammaFrozenHeadLabels (hc := hc) (x := x) hU Q hLabels)
    (ω.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left)

theorem gammaFrozenSelectedHead_volume (N : ℕ) (r : Fin (1+T.arity) → RV (M := M)) (v : Fin (1+k) → RV (M := M)) :
    (gammaMeasuredBoundedSelectedSchema T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T ρ) (gammaHeadContractedForm T hTarget Q hLabels ω) N).object.rowVolume (vfValues x) r v ↔
    ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject (gammaFrozenHeadSelectedPresentation T x ρ P).toGamma),
      u.val = r ∧ (Section5.nativeRVGroundVolume (gammaUniversalObject (gammaFrozenHeadSelectedPresentation T x ρ P).toGamma) u).val = v := by
  let P' := gammaFrozenHeadSelectedPresentation T x ρ P
  change (gammaSelectedLabelSchema T.contractedSet (gamma_headImage T.target hTarget) (headVolumeIndex T ρ)).rowVolume (vfValues x) r v ↔ _
  refine (gammaSelectedLabelSchema_volume T.contractedSet (gamma_headImage T.target hTarget) (headVolumeIndex T ρ) x r v).trans ?_
  constructor
  · intro h
    have hm := (gammaFrozenHeadPreparation_contracted_mem T x r).mpr h.1
    obtain ⟨q,hq,hv⟩ := (P'.graph_iff r v).mpr ⟨hm,hm,h.2⟩
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P'.toGamma) :=
      ⟨q.val,(Section5.nativeRVGroundDomain_carrier _).ge q.property⟩
    exact ⟨u,hq,(gammaNativeRVGroundVolume_value (gammaUniversalObject P'.toGamma) u).trans hv⟩
  · rintro ⟨u,hu,hv⟩
    let q : P'.domain := ⟨u.val,(Section5.nativeRVGroundDomain_carrier _).le u.property⟩
    have hqv : (P'.volume q).val = v := (gammaNativeRVGroundVolume_value (gammaUniversalObject P'.toGamma) u).symm.trans hv
    have h := ((P'.graph_iff r v).mp ⟨q,hu,hqv⟩).2
    exact ⟨(gammaFrozenHeadPreparation_contracted_mem T x r).mp h.1,h.2⟩

theorem gammaFrozenSelectedHead_density (N : ℕ) (r : Fin (1+T.arity) → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
    (gammaMeasuredBoundedSelectedSchema T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T ρ) (gammaHeadContractedForm T hTarget Q hLabels ω) N).rowDensity (vfValues x) r c ↔
    ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject (gammaFrozenHeadSelectedPresentation T x ρ P).toGamma),
      u.val = r ∧ (gammaFrozenSelectedHeadForm T hU x ρ P Q hLabels ω u).val = (volumeGammaSpace hc).decode c := by
  let P' := gammaFrozenHeadSelectedPresentation T x ρ P
  let σ := gammaHeadContractedForm T hTarget Q hLabels ω
  change (gammaMeasuredSelectedSchema T.contractedSet (gamma_headImage T.target hTarget) (headVolumeIndex T ρ) σ).rowDensity (vfValues x) r c ↔ _
  rw [gammaMeasuredSelectedSchema_fibre_density]
  constructor
  · rintro ⟨q,rfl,hq⟩
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P'.toGamma) :=
      ⟨q.val,(Section5.nativeRVGroundDomain_carrier _).ge
        (P'.domain_eq.ge ((gammaFrozenHeadPreparation_contracted_mem T x q.val).mpr q.property))⟩
    refine ⟨u,rfl,?_⟩
    have he : (gammaFrozenSelectedHeadForm T hU x ρ P Q hLabels ω u).val = (gammaMixedRVFibreForm σ x q).val := rfl
    exact he.trans hq
  · rintro ⟨u,rfl,hu⟩
    let q : gammaMixedRVFibreDomain (Section5.nativeGammaPointDomain (hc := hc) (carrier T.contractedSet)
        (gamma_headImage T.target hTarget)) x :=
      ⟨u.val,(gammaFrozenHeadPreparation_contracted_mem T x u.val).mp
        (P'.domain_eq.le ((Section5.nativeRVGroundDomain_carrier _).le u.property))⟩
    exact ⟨q,rfl,hu⟩

end DiamondIntegral.Section3
