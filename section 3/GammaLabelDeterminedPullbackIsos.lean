import «section 3».GammaNativeFullLabelMeasuredDescent
import «section 3».GammaNativePullbackFullComparison
import Integration7.LabelDeterminedPullbackDescent
import IntegrationSection5.RVContractionGamma

/-! The actual shared-label map of two full pullbacks induces an
original-ground RV isomorphism. Only nonzero structural coordinates
are used for its degree; no volume-form representative is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b d : ℕ}
variable (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
variable (D : SpecialTransformations.Section5.DefSet (M := M) Set.univ n b)
variable (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
variable (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
variable (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))

theorem gammaPullbackAt_full_of_nonzero
    (hNZ : ∀ p : A, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero) :
    GammaFullWeightAt (gammaPullbackAt (Set.subset_univ _) A hA hAF) := by
  intro u
  obtain ⟨p,rfl⟩ := rawKeyImage_surjective A u
  change @rvWeight M (CanonicalStructure.normalize (M := M)) n
    ((rvObjectVolume (pullbackObject A) (SpecialTransformations.Section5.Map.toImage (rawKeyMap A) p)).val) = n
  rw [pullbackObject_value_key]
  rw [← rawWeight_eq_normalized_weight]
  simp only [rawWeight,if_pos (hNZ p _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

def gammaLabelDeterminedPullbackIso
    (f : SpecialTransformations.Section5.Map A D) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hSource : ∀ p q : A, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SameRV p.val q.val)
    (hTarget : ∀ p q : D, p.val.2 ∘ τ = q.val.2 ∘ τ → SameRV p.val q.val)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ)
    (hNZA : ∀ p : A, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero)
    (hNZD : ∀ p : D, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero) :
    GammaIsoAt (gammaPullbackAt (Set.subset_univ _) A hA hAF)
      (gammaPullbackAt (Set.subset_univ _) D hD hDF) := by
  let hC := shared_labels_contractible f ρ τ hTarget hLabels
  let hBack := shared_labels_inverse_contractible f hf ρ τ hSource hLabels
  exact Section5.fullWeightIsoAtOfEquiv _ _
    (gammaPullbackAt_full_of_nonzero A hA hAF hNZA)
    (gammaPullbackAt_full_of_nonzero D hD hDF hNZD)
    (Equiv.ofBijective (rvContractionMap f hC) (rvContractionMap_bijective f hf hC hBack))
    (gamma_rvContractionMap_graph f hC hF)

theorem gammaLabelDeterminedPullbackIso_key
    (f : SpecialTransformations.Section5.Map A D) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hSource : ∀ p q : A, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SameRV p.val q.val)
    (hTarget : ∀ p q : D, p.val.2 ∘ τ = q.val.2 ∘ τ → SameRV p.val q.val)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ)
    (hNZA : ∀ p : A, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero)
    (hNZD : ∀ p : D, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero)
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA) :
    (Section5.nativeRVGroundIso (hc := hc)
      (gammaLabelDeterminedPullbackIso A D hA hD hAF hDF f hf hF ρ τ hSource hTarget hLabels hNZA hNZD)).map
        (gammaNativePullbackKeyMap A hA hAF p) =
      gammaNativePullbackKeyMap D hD hDF ⟨(f ⟨p.val,p.property⟩).val,(f ⟨p.val,p.property⟩).property⟩ := by
  apply Subtype.ext
  have he := rvContractionMap_spec f (shared_labels_contractible f ρ τ hTarget hLabels) ⟨p.val,p.property⟩
  have hev := congrArg (fun z : rvObjectDomain (pullbackObject D) => z.val) he
  exact hev

end DiamondIntegral.Section3
