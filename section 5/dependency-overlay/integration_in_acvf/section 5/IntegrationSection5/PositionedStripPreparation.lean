import IntegrationSection5.CellHeadSaturation
import IntegrationSection5.PositionCoordinateGraph
import IntegrationSection5.HeadPreparation

/-! Constructed actual head preparation of a positioned strip, including
its source tag, focus, full Gamma graphs and RV-saturated target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}

def CanonicalTranslationPreparation.toHead {n m : ℕ}
    {A : Set (Point (M := M) (n+1) m)} {c : Point (M := M) (n+1) m → VF (M := M)}
    (T : CanonicalTranslationPreparation (G := G) A 0 c)
    (hT : HeadSaturated (carrier T.target)) : HeadPreparation T.source :=
  ⟨1+m,T.target,T.map,specialRelativeBoundary_forget T.special,hT⟩

theorem positioned_strip_translation (R : Set (VF (M := M) × VF (M := M)))
    (D : Set (VF (M := M))) (c : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (hR : R = {p | p.2 ∈ D ∧ rv (p.1-c p.2) = t})
    (hOldRV : ∀ p ∈ R, ∀ q ∈ R, rv p.1 = rv q.1)
    (hCentre : ∀ p ∈ R, rv (c p.2) = rv p.1)
    (hGamma : GammaSetDefinable G (cellPointSet R))
    (hc : GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes D c)) :
    ∃ T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0 (fun p => c (vfAt p 1)),
      HeadSaturated (carrier T.target) := by
  have hScalar := position_coordinate_scalar_gamma (cellPointSet R) hGamma (1 : Fin 2) D
    (fun p hp => by have h := hR ▸ hp; exact h.1) c hc
  have hInd : ∀ p ∈ cellPointSet R, ∀ q ∈ cellPointSet R,
      erase 0 p = erase 0 q → c (vfAt p 1) = c (vfAt q 1) := by
    intro p hp q hq he
    apply congrArg c
    have h := congrArg (fun p : Point (M := M) 2 0 => vfAt p 1) he
    simpa [erase,replace,vfAt] using h
  obtain ⟨T⟩ := canonical_translation_preparation (cellPointSet R) hGamma (0 : Fin 2)
    (fun p => c (vfAt p 1)) hInd (fun p hp => hCentre (pointCell p) hp) hScalar
  exact ⟨T,cell_translation_headSaturated R D c t hR hOldRV T⟩

end IntegrationInACVF.Section5
