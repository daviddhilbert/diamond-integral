import IntegrationSection5.CanonicalUnaryBranchExtension
import IntegrationSection5.InactiveHeadSaturation
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
variable {S : Set M} {m b : ℕ}
variable {R H : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {u : SpecialBijection (coordinateCanonicalImage R 0) B}
variable {E : Set (Fin m → RV (M := M))} {previous : Option Bool}

theorem unary_headSaturated_iff_pullback (D : Set (Point (M := M) 1 m)) : HeadSaturated D ↔ IsRVPullback D := by
  constructor
  · intro h
    apply (isRVPullback_iff _).mpr
    intro p hp q he
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
    have hx : rv (vfAt q 0) = rv (vfAt p 0) := (hv 0).symm
    have hm := h p hp (vfAt q 0) hx
    have hEq : replace 0 p (vfAt q 0) = q := by
      refine Prod.ext ?_ hl
      funext i; fin_cases i
      change Function.update p.1 (0 : Fin 1) (q.1 0) (0 : Fin 1) = q.1 0
      exact Function.update_self 0 (q.1 0) p.1
    exact hEq ▸ hm
  · exact headSaturated_of_pullback

namespace CanonicalUnaryBranchExtension

theorem target_headSaturated (C : CanonicalUnaryBranchExtension (G := G) u H E previous)
    (hOff : HeadSaturated {p | p ∈ carrier H ∧ p.2 ∉ E}) : HeadSaturated (carrier C.target) := by
  have hCeq := canonical_form_target 0 C.preMap
    (specialRelative_bijective (specialRelativeBoundary_forget C.prefix_special)) C.prefix_formula
  have hCimage : carrier C.prefixTarget = coordinateCanonical 0 '' carrier H := by
    rw [hCeq]
    ext p
    exact ⟨fun ⟨a,ha⟩ => ⟨a.val,a.property,ha⟩,fun ⟨a,ha,hp⟩ => ⟨⟨a,ha⟩,hp⟩⟩
  have hOffC : HeadSaturated {p | p ∈ carrier C.prefixTarget ∧ p.2 ∘ Fin.natAdd 1 ∉ E} := by
    rw [hCimage]
    exact headSaturated_coordinateCanonical_slice (carrier H) Eᶜ hOff
  have hSatOff := headSaturated_unary_fixed_image C.step
    (specialRelative_unaryRelative (specialRelativeBoundary_forget C.step_special))
    {p | p ∈ carrier C.prefixTarget ∧ p.2 ∘ Fin.natAdd 1 ∉ E} (fun _ hp => hp.1) hOffC
    (fun p hp => C.inactive_vf p hp.2) (fun p q hp hq he => C.inactive_sameRV p q hp.2 hq.2 he)
  rintro p hp x hx
  obtain ⟨a,ha⟩ := (specialRelative_bijective (specialRelativeBoundary_forget C.step_special)).2 ⟨p,hp⟩
  have hav : (C.step a).val = p := congrArg (fun z : C.target => z.val) ha
  by_cases he : a.val.2 ∘ Fin.natAdd 1 ∈ E
  · have hActive : p ∈ carrier C.active_image := (Set.ext_iff.mp C.active_image_eq p).mpr ⟨a,he,hav⟩
    have hNew := C.active_saturated p hActive x hx
    obtain ⟨b,_,hb⟩ := (Set.ext_iff.mp C.active_image_eq _).mp hNew
    exact hb ▸ (C.step b).property
  · have hInactive : p ∈ {q | ∃ a : C.prefixTarget,
        a.val ∈ {p | p ∈ carrier C.prefixTarget ∧ p.2 ∘ Fin.natAdd 1 ∉ E} ∧ (C.step a).val = q} :=
      ⟨a,⟨a.property,he⟩,hav⟩
    obtain ⟨b,_,hb⟩ := hSatOff p hInactive x hx
    exact hb ▸ (C.step b).property

theorem target_pullback (C : CanonicalUnaryBranchExtension (G := G) u H E previous)
    (hOff : HeadSaturated {p | p ∈ carrier H ∧ p.2 ∉ E}) : IsRVPullback (carrier C.target) :=
  (unary_headSaturated_iff_pullback _).mp (C.target_headSaturated hOff)

end CanonicalUnaryBranchExtension
end IntegrationInACVF.Section5
