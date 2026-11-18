import «section 6».RowCoordinateGammaObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowCoordinateFormRootControl

/-! (Row-form version for Remark 6.20, translated from `CoordinateMeasuredObstacles`.)
 Actual common bounded coordinate roots for all protected pieces
and every Gamma level. Every root lies in the original ambient set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_coordinate_measured_controlling_roots_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (ω : RowFormOn A qR) :
    ∃ R : CoordinateRootFamily A, ∃ N : ℕ, R.Bound N ∧
      (∀ i, CoordinateRootControl (G := G) R (C i).carrier) ∧
      CoordinateFormRootControlRow (G := G) R (rowFormExtension ω) := by
  obtain ⟨R,N,hR,hForm⟩ := exists_coordinate_form_controlling_roots_row hc hs hsmall hv A hARV
    (rowFormExtension ω) (rowFormExtension_graph_definable ω)
  obtain ⟨Q,L,hQ,hControl⟩ := exists_finite_controlling_coordinate_roots hc hs hsmall hv A hARV C
  exact ⟨R.union Q,N+L,R.union_bound Q N L hR hQ,
    fun i => (hControl i).mono (fun _ hp => Or.inr hp),hForm.mono (fun _ hp => Or.inl hp)⟩

end DiamondIntegral.Section6
