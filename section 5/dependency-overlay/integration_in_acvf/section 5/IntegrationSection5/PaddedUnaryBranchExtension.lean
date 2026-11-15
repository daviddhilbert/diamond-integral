import IntegrationSection5.PaddedUnaryBranchLift
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {H D : DefSet (M := M) S 1 l}

structure PaddedUnaryBranchExtension (u : SpecialBijection A B) (H : DefSet (M := M) S 1 l)
    (ρ : Fin a → Fin l) (E : Set (Fin a → RV (M := M))) (previous : Option Bool) where
  prefixTarget : DefSet (M := M) S 1 (1+l)
  preMap : Map H prefixTarget
  start : Option Bool
  prefix_special : SpecialRelativeBoundary preMap 0 previous start
  prefix_graph : GammaGraphDefinable G (pointMapGraph preMap)
  prefix_formula : ∀ p : H, (preMap p).val = coordinateCanonical 0 p.val
  lift : PaddedUnaryBranchLift (G := G) u prefixTarget (Fin.natAdd 1 ∘ ρ) E start

namespace PaddedUnaryBranchExtension
variable {u : SpecialBijection A B} {ρ : Fin a → Fin l}
variable {E : Set (Fin a → RV (M := M))} {previous : Option Bool}
def map (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous) : Map H C.lift.target :=
  Map.comp C.lift.map C.preMap

theorem special (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous) :
    SpecialRelativeBoundary C.map 0 previous (u.chain.lastKind C.start) :=
  specialRelativeBoundary_comp C.preMap C.lift.map 0 C.prefix_special C.lift.special

theorem graph (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous) :
    GammaGraphDefinable G (pointMapGraph C.map) :=
  gamma_composition_graph C.preMap C.lift.map C.prefix_graph C.lift.graph

theorem inactive_vf (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous)
    (p : H) (hp : p.val.2 ∘ ρ ∉ E) : vfAt (C.map p).val 0 = vfAt p.val 0 := by
  have hFlag : (C.preMap p).val.2 ∘ (Fin.natAdd 1 ∘ ρ) ∉ E := by
    rw [C.prefix_formula]
    have he : (coordinateCanonical 0 p.val).2 ∘ (Fin.natAdd 1 ∘ ρ) = p.val.2 ∘ ρ :=
      congrArg (fun s => s ∘ ρ) (coordinateCanonical_oldRV 0 p.val)
    rwa [he]
  exact (C.lift.inactive_vf (C.preMap p) hFlag).trans
    (congrArg (fun q : Point (M := M) 1 (1+l) => vfAt q 0) (C.prefix_formula p))
end PaddedUnaryBranchExtension

theorem padded_unary_branch_extension (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B)) (hH : GammaSetDefinable G (carrier H))
    (ρ : Fin a → Fin l) (E : Set (Fin a → RV (M := M)))
    (hD : carrier D = {p | p ∈ carrier H ∧ p.2 ∘ ρ ∈ E})
    (P : RVProjectionPadding (G := G) D A ρ)
    (hClass : ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0))
    (previous : Option Bool) (hTag : previous = some false → ∃ kH, Tagged (carrier H) 0 kH) :
    Nonempty (PaddedUnaryBranchExtension (G := G) u H ρ E previous) := by
  obtain ⟨C,pre,start,hPre,hAlt,hC,hPreG,hForm,hTagC⟩ :=
    gamma_branch_boundary_prefix u.chain u.alternating hH 0 previous hTag
  have hCeq := canonical_form_target 0 pre
    (specialRelative_bijective (specialRelativeBoundary_forget hPre)) hForm
  have hDC : carrier (coordinateCanonicalImage D 0) =
      {p | p ∈ carrier C ∧ p.2 ∘ (Fin.natAdd 1 ∘ ρ) ∈ E} := by
    rw [hCeq]
    exact coordinateCanonical_rvSlice 0 {s | s ∘ ρ ∈ E} hD
  obtain ⟨L⟩ := padded_unary_branch_lift u hu hB hC (Fin.natAdd 1 ∘ ρ) E hDC
    P.canonical hClass start hTagC hAlt
  exact ⟨⟨C,pre,start,hPre,hPreG,hForm,L⟩⟩

end IntegrationInACVF.Section5
