import IntegrationSection5.CanonicalProductClassSource
import IntegrationSection5.ProductRVBranchHead
import IntegrationSection5.GammaBranchBoundaryPrefix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m b : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {R : DefSet (M := M) S (n+1) m} {H : DefSet (M := M) S (n+1) (1+m)}

def doubleCanonicalClassPassive (A : DefSet (M := M) S 1 m)
    (Q : Point (M := M) (n+1) m → Prop) : Point (M := M) (n+1) (1+(1+m)) → Prop :=
  canonicalClassPassive A (Fin.natAdd 1 ∘ id) (canonicalClassPassive A id Q)

theorem doubleCanonical_class_product_source (Q : Point (M := M) (n+1) m → Prop)
    (hR : carrier R = {p | activeUnaryProjection 0 id p ∈ carrier A ∧ Q p})
    (hClass : ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    carrier (coordinateCanonicalImage (coordinateCanonicalImage R 0) 0) =
      {p | activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) p ∈ carrier A ∧ doubleCanonicalClassPassive A Q p} := by
  exact coordinateCanonical_class_product_source (Fin.natAdd 1 ∘ id) (canonicalClassPassive A id Q)
    (coordinateCanonical_class_product_source id Q hR hClass) hClass

theorem doubleCanonicalClassPassive_independent (Q : Point (M := M) (n+1) m → Prop)
    (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p) :
    ∀ p x, doubleCanonicalClassPassive A Q (replace 0 p x) ↔ doubleCanonicalClassPassive A Q p :=
  canonicalClassPassive_independent (Fin.natAdd 1 ∘ id) (canonicalClassPassive A id Q)
    (canonicalClassPassive_independent id Q hQ)

structure CanonicalProductBranchCompletion (u : SpecialBijection A B)
    (H : DefSet (M := M) S (n+1) (1+m)) (E : Set (Fin m → RV (M := M))) where
  prefixTarget : DefSet (M := M) S (n+1) (1+(1+m))
  preMap : Map H prefixTarget
  start : Option Bool
  prefix_special : SpecialRelativeBoundary preMap 0 (some true) start
  prefix_graph : GammaGraphDefinable G (pointMapGraph preMap)
  prefix_formula : ∀ p : H, (preMap p).val = coordinateCanonical 0 p.val
  head : ProductRVBranchHead (G := G) u prefixTarget (Fin.natAdd 1 ∘ Fin.natAdd 1) E start

namespace CanonicalProductBranchCompletion
variable {u : SpecialBijection A B} {E : Set (Fin m → RV (M := M))}
def preparation (C : CanonicalProductBranchCompletion (G := G) u H E) : HeadPreparation H where
  arity := C.head.preparation.arity
  target := C.head.preparation.target
  map := Map.comp C.head.preparation.map C.preMap
  special := specialRelativeBoundary_forget (specialRelativeBoundary_comp C.preMap C.head.preparation.map 0
    C.prefix_special C.head.special)
  saturated := C.head.preparation.saturated

theorem graph (C : CanonicalProductBranchCompletion (G := G) u H E) :
    GammaGraphDefinable G (pointMapGraph C.preparation.map) :=
  gamma_composition_graph C.preMap C.head.preparation.map C.prefix_graph C.head.graph
end CanonicalProductBranchCompletion

theorem canonical_product_branch_completion (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B)) (hH : GammaSetDefinable G (carrier H))
    (E : Set (Fin m → RV (M := M)))
    (hR : carrier (coordinateCanonicalImage R 0) = {p | p ∈ carrier H ∧ p.2 ∘ Fin.natAdd 1 ∈ E})
    (Q : Point (M := M) (n+1) m → Prop) (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hProduct : carrier R = {p | activeUnaryProjection 0 id p ∈ carrier A ∧ Q p})
    (hClass : ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0))
    (hFlag : ∀ p ∈ carrier A, p.2 ∈ E)
    (hInactive : HeadSaturated {p | p ∈ carrier H ∧ p.2 ∘ Fin.natAdd 1 ∉ E}) :
    Nonempty (CanonicalProductBranchCompletion (G := G) u H E) := by
  obtain ⟨C,pre,start,hPre,hAlt,hC,hPreG,hForm,hTagC⟩ :=
    gamma_branch_boundary_prefix u.chain u.alternating hH 0 (some true) (fun h => by cases h)
  have hCeq := canonical_form_target 0 pre
    (specialRelative_bijective (specialRelativeBoundary_forget hPre)) hForm
  have hD : carrier (coordinateCanonicalImage (coordinateCanonicalImage R 0) 0) =
      {p | p ∈ carrier C ∧ p.2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) ∈ E} := by
    rw [hCeq]
    exact coordinateCanonical_rvSlice 0 {s | s ∘ Fin.natAdd 1 ∈ E} hR
  have hCimage : carrier C = coordinateCanonical 0 '' carrier H := by
    rw [hCeq]
    ext p
    exact ⟨fun ⟨a,ha⟩ => ⟨a.val,a.property,ha⟩,fun ⟨a,ha,hp⟩ => ⟨⟨a,ha⟩,hp⟩⟩
  have hOff : HeadSaturated {p | p ∈ carrier C ∧ p.2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) ∉ E} := by
    rw [hCimage]
    exact headSaturated_coordinateCanonical_slice (carrier H) {s | s ∘ Fin.natAdd 1 ∉ E} hInactive
  obtain ⟨L⟩ := product_rv_branch_head u hu hB hC (Fin.natAdd 1 ∘ Fin.natAdd 1) E hD
    (doubleCanonicalClassPassive A Q) (doubleCanonicalClassPassive_independent Q hQ)
    (doubleCanonical_class_product_source Q hProduct hClass) hFlag hOff start hTagC hAlt
  exact ⟨⟨C,pre,start,hPre,hPreG,hForm,L⟩⟩

end IntegrationInACVF.Section5
