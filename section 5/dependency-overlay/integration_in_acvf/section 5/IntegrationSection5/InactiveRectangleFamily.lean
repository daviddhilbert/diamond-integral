import IntegrationSection5.RVSliceTranslationImages
import IntegrationSection5.CanonicalHeadGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}

theorem rvFibreRectangles_vfSwap (A : Set (Point (M := M) 2 m)) (hA : RVFibreRectangles A) :
    RVFibreRectangles {p | vfPermutation (Equiv.swap 0 1) p ∈ A} := by
  intro p hp q hq hLabels
  have h := hA (vfPermutation (Equiv.swap 0 1) q) hq (vfPermutation (Equiv.swap 0 1) p) hp hLabels.symm
  change (![vfAt q 1,vfAt p 0],q.2) ∈ A at h
  rw [← hLabels] at h
  have he : vfPermutation (Equiv.swap (0 : Fin 2) 1) (![vfAt p 0,vfAt q 1],p.2) =
      (![vfAt q 1,vfAt p 0],p.2) := by
    apply Prod.ext
    · funext j; fin_cases j <;> simp [vfPermutation,vfAt]
    · rfl
  change vfPermutation (Equiv.swap 0 1) (![vfAt p 0,vfAt q 1],p.2) ∈ A
  rw [he]
  exact h

namespace RVSliceTranslationPreparation
variable {A : Set (Point (M := M) 2 m)} {E : Set (Fin m → RV (M := M))}
variable {c : Point (M := M) 2 m → VF (M := M)}

theorem inactive_rectangles (U : RVSliceTranslationPreparation (G := G) A E 0 c)
    (hRect : RVFibreRectangles {p | p ∈ A ∧ p.2 ∉ E}) : RVFibreRectangles U.inactiveSet := by
  rw [U.inactive_image]
  exact rvFibreRectangles_coordinateCanonical _ hRect

end RVSliceTranslationPreparation
namespace PositionedCellLabelInjection
variable {A : Set (Point (M := M) 2 m)}

theorem horizontal_inactive_rectangles (T : PositionedCellLabelInjection G A)
    {c : Point (M := M) 2 T.arity → VF (M := M)}
    (U : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 c) :
    RVFibreRectangles U.inactiveSet :=
  U.inactive_rectangles (rectangleFamilyBranch_rectangles T.target)

theorem vertical_inactive_rectangles (T : PositionedCellLabelInjection G A)
    {c : Point (M := M) 2 T.arity → VF (M := M)}
    (U : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 c) :
    RVFibreRectangles U.inactiveSet :=
  U.inactive_rectangles (rvFibreRectangles_vfSwap _ (rectangleFamilyBranch_rectangles T.target))

theorem horizontal_inactive_gamma (T : PositionedCellLabelInjection G A)
    {c : Point (M := M) 2 T.arity → VF (M := M)}
    (U : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 c) :
    GammaSetDefinable G U.inactiveSet :=
  U.inactive_gamma (rectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G)))

theorem vertical_inactive_gamma (T : PositionedCellLabelInjection G A)
    {c : Point (M := M) 2 T.arity → VF (M := M)}
    (U : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 c) :
    GammaSetDefinable G U.inactiveSet :=
  U.inactive_gamma (gamma_mixedVFSelect_preimage (Equiv.swap 0 1) _
    (rectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G))))

end PositionedCellLabelInjection
end IntegrationInACVF.Section5
