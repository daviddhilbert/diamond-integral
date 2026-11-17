import «section 3».GammaHeadRawRowMeasuredBridge
import «section 3».GammaMeasuredSelectedBounds

/-! The head row's actual native structural volume and Gamma form have
exactly the bounded selected schema's complete graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
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
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a}
variable (T : HeadPreparation U) (hTarget : GammaSetDefinable B (carrier T.target))
variable (x : Fin n → VF (M := M))
variable (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x)
variable (σ : GammaGroundVolumeForm hc B
  (Section5.nativeGammaPointDomain (carrier T.contractedSet) (gamma_headImage T.target hTarget))) (N : ℕ)

theorem gammaHeadRawRowSchema_volume (r : Fin (1+T.arity) → RV (M := M)) (v : Fin 1 → RV (M := M)) :
    (gammaMeasuredBoundedSelectedSchema T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) σ N).object.rowVolume (vfValues x) r v ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma),
        u.val = r ∧ (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val = v := by
  change (gammaSelectedLabelSchema T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))).rowVolume (vfValues x) r v ↔ _
  refine (gammaSelectedLabelSchema_volume T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x r v).trans ?_
  constructor
  · intro h
    obtain ⟨q,hq,hv⟩ := (P.graph_iff r v).mpr ⟨h.1,h⟩
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma) :=
      ⟨q.val,(Section5.nativeRVGroundDomain_carrier _).ge q.property⟩
    refine ⟨u,hq,?_⟩
    rw [gammaNativeRVGroundVolume_value]
    exact hv
  · rintro ⟨u,hu,hv⟩
    let q : P.domain := ⟨u.val,(Section5.nativeRVGroundDomain_carrier _).le u.property⟩
    have hqv : (P.volume q).val = v := by
      rw [gammaNativeRVGroundVolume_value] at hv
      exact hv
    exact ((P.graph_iff r v).mp ⟨q,hu,hqv⟩).2

theorem gammaHeadRawRowSchema_density (r : Fin (1+T.arity) → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
    (gammaMeasuredBoundedSelectedSchema T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) σ N).rowDensity (vfValues x) r c ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma),
        u.val = r ∧ (gammaHeadRawRowForm T hTarget x P σ u).val = (volumeGammaSpace hc).decode c := by
  change (gammaMeasuredSelectedSchema T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) σ).rowDensity (vfValues x) r c ↔ _
  rw [gammaMeasuredSelectedSchema_fibre_density]
  constructor
  · rintro ⟨q,rfl,hq⟩
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma) :=
      ⟨q.val,(Section5.nativeRVGroundDomain_carrier _).ge (P.domain_eq.ge q.property)⟩
    have he : gammaHeadRawRowLabels T hTarget x P u = q := Subtype.ext rfl
    refine ⟨u,rfl,?_⟩
    change (gammaMixedRVFibreForm σ x (gammaHeadRawRowLabels T hTarget x P u)).val = _
    rw [he]
    exact hq
  · rintro ⟨u,rfl,hu⟩
    exact ⟨gammaHeadRawRowLabels T hTarget x P u,rfl,hu⟩

end DiamondIntegral.Section3
