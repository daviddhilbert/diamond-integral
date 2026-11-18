import «section 3».GammaIndexedMeasuredRowComparison
import «section 3».GammaIndexedEssentialMeasuredRestriction

/-! Constrained finite-row witnesses on the essential indices give the
measured comparison in every positive degree. -/
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
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b n : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin (n+1) → RV (M := M)) → Prop}

theorem gammaMeasured_essential_row_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (BP : GammaFiniteGraphPresentation B p (n+1) T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)
    (hA : ∀ t ∈ T, F.rowDomain (rvValues t) ⊆ A.carrier)
    (hD : ∀ t ∈ T, G.rowDomain (rvValues t) ⊆ D.carrier)
    (hWitness : ∀ t ∈ T, (∀ i, (BP.totalVolume t i).val ≠ iRVZero) →
      ∃ H : GammaRelationFormula B p a b (fun _ => .rv),
        H.val ⊆ gammaParametricFormConstraint A D ω π (fun _ => .rv) ∧
          (gammaFiniteRowChartSchema F G H).valid (rvValues t)) :
    Nonempty (GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma)
        (ω.comp (gammaIndexedOriginalLabelMap BP F P A hA)))
      (gammaNativeMeasuredNormalization (gammaUniversalObject Q.toGamma)
        (π.comp (gammaIndexedOriginalLabelMap BP G Q D hD)))) := by
  let BE := essentialIndexPresentation BP
  let PE := F.indexedPresentation BE (fun t ht => hF t ht.1)
  let QE := G.indexedPresentation BE (fun t ht => hG t ht.1)
  obtain ⟨e⟩ := gammaIndexed_measured_row_comparison hκ hs hr hg BE F G PE QE A D ω π
    (fun t ht => hA t ht.1) (fun t ht => hD t ht.1) (fun t ht => hWitness t ht.1 ht.2)
  let eP := gammaIndexedEssential_measured_restriction BP F P PE A ω hA
  let eQ := gammaIndexedEssential_measured_restriction BP G Q QE D π hD
  exact ⟨eQ.comp (e.comp eP.symm)⟩

end DiamondIntegral.Section3
