import «section 3».GammaIndexedConstrainedRowBijections
import «section 3».GammaParametricFormConstraints
import «section 3».GammaIndexedOriginalLabels
import «section 3».GammaUniversalIsomorphismMaps
import «section 3».GammaNativeMeasuredIsomorphisms

/-! The existing indexed ordinary RV isomorphism, with the Gamma equality
constraint retained, is an isomorphism of the measured Gamma objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b n : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin (n+1) → RV (M := M)) → Prop}

theorem gammaIndexed_measured_row_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (BP : GammaFiniteGraphPresentation B p (n+1) T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)
    (hA : ∀ t ∈ T, F.rowDomain (rvValues t) ⊆ A.carrier)
    (hD : ∀ t ∈ T, G.rowDomain (rvValues t) ⊆ D.carrier)
    (hWitness : ∀ t ∈ T, ∃ H : GammaRelationFormula B p a b (fun _ => .rv),
      H.val ⊆ gammaParametricFormConstraint A D ω π (fun _ => .rv) ∧
        (gammaFiniteRowChartSchema F G H).valid (rvValues t)) :
    Nonempty (GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma)
        (ω.comp (gammaIndexedOriginalLabelMap BP F P A hA)))
      (gammaNativeMeasuredNormalization (gammaUniversalObject Q.toGamma)
        (π.comp (gammaIndexedOriginalLabelMap BP G Q D hD)))) := by
  obtain ⟨e,he,hConstraint⟩ := gammaIndexed_constrained_row_bijection hκ hs hreal hgamma BP F G
    (gammaParametricFormConstraint A D ω π (fun _ => .rv)) hWitness
  let E := indexedOrdinaryGammaIso BP F G P Q e he
  let EI := gammaUniversalIsoAt P.toGamma Q.toGamma E
  refine ⟨gammaNativeMeasuredNormalizationHom _ _ EI (fun u => ?_)⟩
  let v := (Section5.nativeRVGroundIso EI).map u
  let u0 := gammaIndexedOriginalLabelMap BP F P A hA u
  let v0 := gammaIndexedOriginalLabelMap BP G Q D hD v
  let q := (pureRVLabelPointEquiv _) (P.domainEquiv
    (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u))
  have hq : q.val.2 = u.val := rfl
  have hv : (e.equiv q).val.2 = v.val := rfl
  have hK := (hConstraint q).1
  have hidx :
      Fin.append (rvValues q.val.2) (rvValues ((e.equiv q).val.2 ∘ Fin.natAdd p)) ∘
        gammaFormConstraintIndices p a b = Fin.append (rvValues u0.val) (rvValues v0.val) := by
    rw [hq,hv]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [gammaFormConstraintIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right]
    · rfl
    · rfl
  rw [hidx] at hK
  have hw : ω u0 = π v0 := (gammaRVFormRawConstraint_mem A D ω π u0 v0).mp hK
  have hform : gammaGroundFormValue (ω.comp (gammaIndexedOriginalLabelMap BP F P A hA)) u =
      gammaGroundFormValue (π.comp (gammaIndexedOriginalLabelMap BP G Q D hD)) v := by
    exact congrArg (fun z => cast (gammaCarrier hc) z.val) hw
  have hvol : (Section5.nativeRVGroundVolume (gammaUniversalObject Q.toGamma) v).val =
      (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val := by
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    exact indexed_ordinary_gamma_iso_volume BP F G P Q e he
      (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u)
  unfold gammaNativeCombinedWeight
  change (gammaGroundFormValue (ω.comp (gammaIndexedOriginalLabelMap BP F P A hA)) u).val * _ =
    (gammaGroundFormValue (π.comp (gammaIndexedOriginalLabelMap BP G Q D hD)) v).val * _
  rw [hform,hvol]

end DiamondIntegral.Section3
