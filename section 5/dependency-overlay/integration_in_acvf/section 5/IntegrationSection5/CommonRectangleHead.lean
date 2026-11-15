import IntegrationSection5.CanonicalProductBranchCompletion
import IntegrationSection5.TranslationExtension
import IntegrationSection5.RVSliceTranslationImages
import IntegrationSection5.GammaRectangleFamilyComparison
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
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {E : Set (Fin m → RV (M := M))}
variable {c : Point (M := M) 2 m → VF (M := M)}

theorem coordinateCanonicalImage_carrier_eq {S : Set M} {n m : ℕ} (H : DefSet (M := M) S n m) (i : Fin n) :
    carrier (coordinateCanonicalImage H i) = coordinateCanonical i '' carrier H := by
  ext q
  exact ⟨fun ⟨p,hp⟩ => ⟨p.val,p.property,hp⟩,fun ⟨p,hp,hpq⟩ => ⟨⟨p,hp⟩,hpq⟩⟩

theorem passive_projection_independent {S : Set M} (Z : DefSet (M := M) S 1 m) :
    ∀ (p : Point (M := M) 2 m) x, activeUnaryProjection 1 id (replace 0 p x) ∈ carrier Z ↔
      activeUnaryProjection 1 id p ∈ carrier Z := by
  intro p x
  have he : activeUnaryProjection 1 id (replace 0 p x) = activeUnaryProjection 1 id p := by
    refine Prod.ext ?_ rfl
    funext j; fin_cases j
    simp only [activeUnaryProjection,replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [he]

theorem rv_slice_common_product_head
    (U : RVSliceTranslationPreparation (G := G) A E 0 c)
    (hN : HeadSaturated (carrier U.branch.target))
    (P : MixedUnaryPreparations (G := G) {p | p ∈ A ∧ p.2 ∉ E})
    (hCodes : U.branch.codes ⊆ P.codes)
    (hRect : RVFibreRectangles {p | p ∈ A ∧ p.2 ∉ E})
    (hClass : ∀ p ∈ carrier P.sourceD, ∀ q ∈ carrier P.sourceD,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    Nonempty (CanonicalProductBranchCompletion (G := G) P.specialD (U.extendBase hCodes).target Eᶜ) := by
  let V := U.extendBase hCodes
  have hR : carrier (coordinateCanonicalImage P.source 0) =
      {p | p ∈ carrier V.target ∧ p.2 ∘ Fin.natAdd 1 ∈ Eᶜ} := by
    rw [coordinateCanonicalImage_carrier_eq,P.source_eq]
    exact U.inactive_image.symm
  have hProduct : carrier P.source = {p | activeUnaryProjection 0 id p ∈ carrier P.sourceD ∧
      activeUnaryProjection 1 id p ∈ carrier P.sourceE} := by
    rw [P.source_eq,P.sourceD_eq,P.sourceE_eq]
    exact mixed_rectangle_projection_eq _ hRect
  have hFlag : ∀ p ∈ carrier P.sourceD, p.2 ∈ Eᶜ := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := (Set.ext_iff.mp P.sourceD_eq p).mp hp
    exact (congrArg (fun z : Point (M := M) 1 m => z.2) hqp) ▸ hq.2
  have hOff : HeadSaturated {p | p ∈ carrier V.target ∧ p.2 ∘ Fin.natAdd 1 ∉ Eᶜ} := by
    have he : {p | p ∈ carrier V.target ∧ p.2 ∘ Fin.natAdd 1 ∉ Eᶜ} = carrier U.branch.target := by
      rw [U.active_image]
      ext p
      change (p ∈ carrier U.target ∧ ¬ ¬ p.2 ∘ Fin.natAdd 1 ∈ E) ↔
        (p ∈ carrier U.target ∧ p.2 ∘ Fin.natAdd 1 ∈ E)
      exact and_congr_right (fun _ => not_not)
    exact he.symm ▸ hN
  exact canonical_product_branch_completion P.specialD P.gammaD P.pullbackD V.target_gamma Eᶜ hR
    (fun p => activeUnaryProjection 1 id p ∈ carrier P.sourceE) (passive_projection_independent P.sourceE)
    hProduct hClass hFlag hOff

end IntegrationInACVF.Section5
