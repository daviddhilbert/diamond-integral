import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowCarriedFormRootControl

/-! (Row-form version for Remark 6.20, translated from `CoordinateGammaDescent`.)
 Actual original-base descent of a Gamma form through deletion of
the controlled coordinate. The complete graph is constructed by definable
surjective descent; empty coordinate roots supply its compatibility. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def coordinateGammaDescentRow
    (ω : RowFormOn A qR)
    (hConst : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, Fin.init p.1 = Fin.init q.1 → p.2 = q.2 →
      rowFormExtension ω p = rowFormExtension ω q) :
    RowFormOn (vfDropLast A).image qR :=
  RowFormOn.descent (vfDropLast A).toImage (map_toImage_surjective _) ω (by
    intro p q he
    have hpq : (Fin.init p.val.1,p.val.2) = (Fin.init q.val.1,q.val.2) := congrArg Subtype.val he
    have hInit : Fin.init p.val.1 = Fin.init q.val.1 := congrArg (fun z : Mixed M n r => z.1) hpq
    have hTags : p.val.2 = q.val.2 := congrArg (fun z : Mixed M n r => z.2) hpq
    have h := hConst p.val p.property q.val q.property hInit hTags
    rw [rowFormExtension_at,rowFormExtension_at] at h
    exact Subtype.ext h)

theorem coordinateGammaDescent_at_row
    (ω : RowFormOn A qR)
    (hConst : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, Fin.init p.1 = Fin.init q.1 → p.2 = q.2 →
      rowFormExtension ω p = rowFormExtension ω q) (p : A) :
    coordinateGammaDescentRow ω hConst ((vfDropLast A).toImage p) = ω p :=
  RowFormOn.descent_apply _ _ _ _ _

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem empty_coordinate_roots_gamma_descent_row
    (R : CoordinateRootFamily A)
    (ω : RowFormOn A qR)
    (hControl : CoordinateFormRootControlRow (G := G) R (rowFormExtension ω))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEmpty : R.roots.carrier = ∅) (hA : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ η : RowFormOn (vfDropLast A).image qR,
      ∀ p : A, η ((vfDropLast A).toImage p) = ω p := by
  let hConst := hControl.empty_roots_projection_constant_row hv hEmpty hA hD hTag
  exact ⟨coordinateGammaDescentRow ω hConst,coordinateGammaDescent_at_row ω hConst⟩

end DiamondIntegral.Section6
