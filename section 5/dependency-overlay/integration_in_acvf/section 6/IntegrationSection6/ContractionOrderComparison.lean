import IntegrationSection6.SelectedCoordinateExchange
import IntegrationSection6.GammaGraphPresentationIsomorphisms

/-! The exact arbitrary-order comparison property and its checked
same-order case. The separate input is the universally quantified
Section5.8 result, authorized while Section5 is being formalized. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Section5TwoOrderInputAll {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) : Prop :=
  ∀ (B : Base (M := M)) (hreal : Cardinal.mk B.real < κ),
    Cardinal.aleph0 < κ → M ⊨ Axioms.ACVF00 →
    ∀ δ : Values.Gamma (M := M), δ ∈ B.gamma → 1 < δ →
      Section5TwoOrderInput B hκ hs hreal

namespace FiniteRV
variable {B : Base (M := M)} {n a k : ℕ}

def ContractionOrderIndependent {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (n : ℕ) : Prop :=
  ∀ {a k : ℕ} (U : DefSet (M := M) Set.univ n a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (σ υ : Equiv.Perm (Fin n)) (C : StandardContraction U σ) (E : StandardContraction U υ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program)
    (P : GammaSelectedRVPresentation B C.target (orderedSelectedIndex C.program ρ))
    (Q : GammaSelectedRVPresentation B E.target (orderedSelectedIndex E.program ρ)),
    GammaIsp hκ hs h00 hreal P.toGamma Q.toGamma

theorem gamma_same_order_recursive_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : DefSet (M := M) Set.univ n a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (σ : Equiv.Perm (Fin n)) (C E : StandardContraction U σ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program)
    (P : GammaSelectedRVPresentation B C.target (orderedSelectedIndex C.program ρ))
    (Q : GammaSelectedRVPresentation B E.target (orderedSelectedIndex E.program ρ)) :
    GammaIsp hκ.le hs h00 hreal P.toGamma Q.toGamma := by
  apply lemma_6_14_ordered hκ hs h00 hreal hgamma δ hδ hδ1
    (vfPermutationImage U σ) (vfPermutationImage U σ)
    (gamma_vfPermutationImage U hU σ) (gamma_vfPermutationImage U hU σ) ρ ρ
    (vfPermutation_selected_finite U σ ρ hfin) (vfPermutation_selected_finite U σ ρ hfin)
    _ C.program E.program hC hE P Q
  intro x LP LQ
  exact GammaIsp.of_iso (gammaGraphPresentationIso LP LQ)

end FiniteRV
end IntegrationInACVF.Section6
