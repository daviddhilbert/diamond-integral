import IntegrationSection5.MixedVerticalPullbackCells
import IntegrationSection4.PositionRowDefinability
noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace IntegrationInACVF.Section5.MixedVerticalPresentation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

def scalarPosition (V : MixedVerticalPresentation G A)
    (u : GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) : VF (M := M) :=
  V.position ⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp u.property⟩

theorem scalarPosition_graph (V : MixedVerticalPresentation G A) :
    GammaScalarGraphDefinable G (fun p y =>
      ∃ u : GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain), u.val = p ∧ V.scalarPosition u = y) := by
  apply GammaScalarGraphDefinable.congr V.position_graph
  intro p y
  constructor
  · rintro ⟨u,hu,hy⟩
    exact ⟨⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mpr u.property⟩,hu,hy⟩
  · rintro ⟨u,hu,hy⟩
    exact ⟨⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp u.property⟩,hu,hy⟩

theorem scalarPosition_value (V : MixedVerticalPresentation G A)
    (u : GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) :
    (V.scalarPosition u).val = GammaScalarFamilies.value V.position
      (GammaFamilySyntax.labels u.val) (vfAt u.val 0).val :=
  (GammaScalarFamilies.value_on V.position
    ⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp u.property⟩).symm

theorem position_definable {d : ℕ} (V : MixedVerticalPresentation G A)
    (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d) (a₀ : A)
    (row : PositionRow Q (V.scalarProjection a₀) (GammaScalarFamilies.value V.position) V.paradigm_index) :
    DefinableOverBase (RVLabelSlices.labelBase G ((V.pullback Q).toFun a₀)) (fun _ : Fin 2 => .vf)
      (Cells.positionCodes (Cells.first (mixedPairFibre (V.pullback Q) a₀)) row.position) := by
  have h := PositionRowDefinability.definable Q V.scalarPosition V.scalarPosition_graph
    (GammaScalarFamilies.value V.position) V.scalarPosition_value row
  have hFirst : Cells.first (mixedPairFibre (V.pullback Q) a₀) = row.domain := by
    rw [V.pullback_fibre Q a₀ row,CellsFromFibres.first_eq]
  rwa [← hFirst] at h

end IntegrationInACVF.Section5.MixedVerticalPresentation
