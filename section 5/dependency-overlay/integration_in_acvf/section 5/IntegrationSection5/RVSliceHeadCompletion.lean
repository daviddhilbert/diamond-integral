import IntegrationSection5.RVProductBranchCompletion
import IntegrationSection5.MixedUnaryPreparationOver
import IntegrationSection5.TranslationExtension
import IntegrationSection5.InactiveRectangleFamily
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {E : Set (Fin m → RV (M := M))}
variable {c : Point (M := M) 2 m → VF (M := M)}

structure RVSliceHeadCompletion (U : RVSliceTranslationPreparation (G := G) A E 0 c) where
  rectangle : MixedUnaryPreparations (G := G) U.inactiveSet
  contains_codes : U.branch.codes ⊆ rectangle.codes
  completion : RVProductBranchCompletion (G := G) rectangle.specialD
    (U.extendBase contains_codes).target {s | s ∘ Fin.natAdd 1 ∉ E}

namespace RVSliceHeadCompletion
variable {U : RVSliceTranslationPreparation (G := G) A E 0 c}

def preparation (C : RVSliceHeadCompletion U) : HeadPreparation (U.extendBase C.contains_codes).source where
  arity := C.completion.arity
  target := C.completion.target
  map := Map.comp C.completion.preparation.map (U.extendBase C.contains_codes).map
  special := specialRelativeBoundary_forget (specialRelativeBoundary_comp
    (U.extendBase C.contains_codes).map C.completion.preparation.map 0
      (U.extendBase C.contains_codes).special C.completion.preparation_special)
  saturated := C.completion.saturated

theorem preparation_gamma (C : RVSliceHeadCompletion U) :
    GammaGraphDefinable G (pointMapGraph C.preparation.map) :=
  gamma_composition_graph (U.extendBase C.contains_codes).map C.completion.preparation.map
    (U.extendBase C.contains_codes).graph C.completion.preparation_gamma

theorem preparation_target_gamma (C : RVSliceHeadCompletion U) :
    GammaSetDefinable G (carrier C.preparation.target) := C.completion.target_gamma

theorem preparation_source_eq (C : RVSliceHeadCompletion U) :
    carrier (U.extendBase C.contains_codes).source = A := U.source_eq

end RVSliceHeadCompletion

theorem rv_slice_head_completion {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (U : RVSliceTranslationPreparation (G := G) A E 0 c)
    (hN : HeadSaturated (carrier U.branch.target))
    (hRΓ : GammaSetDefinable G U.inactiveSet) (hRect : RVFibreRectangles U.inactiveSet) :
    Nonempty (RVSliceHeadCompletion U) := by
  obtain ⟨P,hCodes⟩ := mixed_unary_preparations_over hs h00 hsmall F U.branch.codes U.inactiveSet hRΓ
  let V := U.extendBase hCodes
  let ER : Set (Fin (1+m) → RV (M := M)) := {s | s ∘ Fin.natAdd 1 ∉ E}
  have hR : carrier P.source = {p | p ∈ carrier V.target ∧ p.2 ∈ ER} := P.source_eq
  have hProduct : carrier P.source = {p | activeUnaryProjection 0 id p ∈ carrier P.sourceD ∧
      activeUnaryProjection 1 id p ∈ carrier P.sourceE} := by
    rw [P.source_eq,P.sourceD_eq,P.sourceE_eq]
    exact mixed_rectangle_projection_eq U.inactiveSet hRect
  have hFlag : ∀ p ∈ carrier P.sourceD, p.2 ∈ ER := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := (Set.ext_iff.mp P.sourceD_eq p).mp hp
    have hl : q.2 = p.2 := congrArg (fun z : Point (M := M) 1 (1+m) => z.2) hqp
    exact hl ▸ hq.2
  have hTagR : Tagged U.inactiveSet 0 (0 : Fin (1+m)) := by
    rw [U.inactive_image]
    exact coordinateCanonical_image_tagged 0 _
  have hTagD : Tagged (carrier P.sourceD) 0 (0 : Fin (1+m)) := by
    rw [P.sourceD_eq]
    exact mixed_first_projection_tagged U.inactiveSet 0 hTagR
  have hInactive : HeadSaturated {p | p ∈ carrier V.target ∧ p.2 ∉ ER} := by
    have he : {p | p ∈ carrier V.target ∧ p.2 ∉ ER} = carrier U.branch.target := by
      rw [U.active_image]
      ext p
      change (p ∈ carrier U.target ∧ ¬ ¬ p.2 ∘ Fin.natAdd 1 ∈ E) ↔
        (p ∈ carrier U.target ∧ p.2 ∘ Fin.natAdd 1 ∈ E)
      exact and_congr_right (fun _ => not_not)
    exact he.symm ▸ hN
  obtain ⟨C⟩ := rv_product_branch_completion P.specialD P.gammaD P.pullbackD V.target_gamma ER
    hR hProduct hFlag 0 hTagD hInactive
  exact ⟨⟨P,hCodes,C⟩⟩

end IntegrationInACVF.Section5
