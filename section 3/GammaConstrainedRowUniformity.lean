import Integration7.HKConstrainedBijectionRealization
import Integration7.GammaFiniteRowIsomorphismWitnesses

/-! Finite formula charts with an arbitrary fixed Gamma graph constraint
assemble into one parameter-preserving original-ground bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem gammaFinite_constrained_row_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (K : Set (Fin ((p+a)+b) → M))
    (hrow : ∀ z ∈ A, ∃ H : GammaRelationFormula B p a b sp,
      H.val ⊆ K ∧ (gammaFiniteRowChartSchema F G H).valid z) :
    ∃ e : GammaSortedIso B (Fin.append sp (fun _ : Fin a => .rv))
      (Fin.append sp (fun _ : Fin b => .rv)) (rawRowTotal A F.domain) (rawRowTotal A G.domain),
      (∀ u, (e.equiv u).val ∘ Fin.castAdd b = u.val ∘ Fin.castAdd a) ∧
      ∀ u, Fin.append u.val ((e.equiv u).val ∘ Fin.natAdd p) ∈ K := by
  obtain ⟨C,hCK,hC⟩ := IntegrationInACVF.Section7.HK.uniform_bijection_chart_within hκ hs hr hg A hA
    F.domain_definable G.domain_definable K (by
      intro z hz
      obtain ⟨H,hHK,hH⟩ := hrow z hz
      exact ⟨⟨H.val,H.property⟩,hHK,hH.2.2.1⟩)
  exact ⟨gammaSortedTotalIso C hA G.domain_definable hC,
    gammaSortedTotalEquiv_prefix C G.domain_definable hC,
    IntegrationInACVF.Section7.HK.constrained_total_graph C hA G.domain_definable hC K hCK⟩

end DiamondIntegral.Section3
