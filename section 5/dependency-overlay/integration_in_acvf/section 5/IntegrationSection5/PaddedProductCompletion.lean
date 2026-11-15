import IntegrationSection5.ProjectionPaddingProductRefinement
import IntegrationSection5.ProductRVBranchHead
import IntegrationSection5.GammaBranchBoundaryPrefix
import IntegrationSection5.CanonicalHeadGeometry
import IntegrationSection5.CanonicalRVSliceGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l c : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {H D : DefSet (M := M) S 1 l} {C : DefSet (M := M) S 1 c}

structure PaddedProductCompletion (u : SpecialBijection A B) (H : DefSet (M := M) S 1 l)
    (ρ : Fin a → Fin l) (E : Set (Fin a → RV (M := M))) (previous : Option Bool) where
  prefixTarget : DefSet (M := M) S 1 (1+l)
  preMap : Map H prefixTarget
  start : Option Bool
  prefix_special : SpecialRelativeBoundary preMap 0 previous start
  prefix_graph : GammaGraphDefinable G (pointMapGraph preMap)
  prefix_formula : ∀ p : H, (preMap p).val = coordinateCanonical 0 p.val
  head : ProductRVBranchHead (G := G) u prefixTarget (Fin.natAdd 1 ∘ ρ) E start

namespace PaddedProductCompletion
variable {u : SpecialBijection A B} {ρ : Fin a → Fin l} {E : Set (Fin a → RV (M := M))} {previous : Option Bool}
def preparation (C : PaddedProductCompletion (G := G) u H ρ E previous) : HeadPreparation H where
  arity := C.head.preparation.arity
  target := C.head.preparation.target
  map := Map.comp C.head.preparation.map C.preMap
  special := specialRelativeBoundary_forget (specialRelativeBoundary_comp C.preMap C.head.preparation.map 0 C.prefix_special C.head.special)
  saturated := C.head.preparation.saturated

theorem boundary (C : PaddedProductCompletion (G := G) u H ρ E previous) :
    SpecialRelativeBoundary C.preparation.map 0 previous (u.chain.lastKind C.start) :=
  specialRelativeBoundary_comp C.preMap C.head.preparation.map 0 C.prefix_special C.head.special

theorem graph (C : PaddedProductCompletion (G := G) u H ρ E previous) : GammaGraphDefinable G (pointMapGraph C.preparation.map) :=
  gamma_composition_graph C.preMap C.head.preparation.map C.prefix_graph C.head.graph
end PaddedProductCompletion

theorem padded_product_completion (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B)) (hH : GammaSetDefinable G (carrier H))
    (ρ : Fin c → Fin l) (σ : Fin a → Fin c) (E : Set (Fin a → RV (M := M)))
    (P : RVProjectionPadding (G := G) D C ρ)
    (Q : Point (M := M) 1 c → Prop) (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hC : carrier C = {p | activeUnaryProjection 0 σ p ∈ carrier A ∧ Q p})
    (hClass : ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0))
    (hD : carrier D = {p | p ∈ carrier H ∧ p.2 ∘ (ρ ∘ σ) ∈ E})
    (hFlag : ∀ p ∈ carrier A, p.2 ∈ E)
    (hInactive : HeadSaturated {p | p ∈ carrier H ∧ p.2 ∘ (ρ ∘ σ) ∉ E})
    (previous : Option Bool) (hTag : previous = some false → ∃ kH, Tagged (carrier H) 0 kH) :
    Nonempty (PaddedProductCompletion (G := G) u H (ρ ∘ σ) E previous) := by
  obtain ⟨K,pre,start,hPre,hAlt,hK,hPreG,hForm,hTagK⟩ :=
    gamma_branch_boundary_prefix u.chain u.alternating hH 0 previous hTag
  have hKeq := canonical_form_target 0 pre (specialRelative_bijective (specialRelativeBoundary_forget hPre)) hForm
  have hDC : carrier (coordinateCanonicalImage D 0) =
      {p | p ∈ carrier K ∧ p.2 ∘ (Fin.natAdd 1 ∘ (ρ ∘ σ)) ∈ E} := by
    rw [hKeq]
    exact coordinateCanonical_rvSlice 0 {s | s ∘ (ρ ∘ σ) ∈ E} hD
  have hProd := P.canonical.refined_product_source σ Q hC hClass
  have hOff : HeadSaturated {p | p ∈ carrier K ∧ p.2 ∘ (Fin.natAdd 1 ∘ (ρ ∘ σ)) ∉ E} := by
    have he : carrier K = coordinateCanonical 0 '' carrier H := by
      rw [hKeq]
      ext p
      exact ⟨fun ⟨a,ha⟩ => ⟨a.val,a.property,ha⟩,fun ⟨a,ha,he⟩ => ⟨⟨a,ha⟩,he⟩⟩
    rw [he]
    exact headSaturated_coordinateCanonical_slice (carrier H) {s | s ∘ (ρ ∘ σ) ∉ E} hInactive
  obtain ⟨L⟩ := product_rv_branch_head u hu hB hK (Fin.natAdd 1 ∘ (ρ ∘ σ)) E hDC
    (RVProjectionPadding.refinedPassive (coordinateCanonicalImage D 0) (Fin.natAdd 1 ∘ ρ) Q)
    (RVProjectionPadding.refinedPassive_independent Q hQ) hProd hFlag hOff start hTagK hAlt
  exact ⟨⟨K,pre,start,hPre,hPreG,hForm,L⟩⟩

end IntegrationInACVF.Section5
