import «section 6».UnaryLabelCenters
import «section 6».PairedDiscOffsets
import «section 6».VFTupleArithmeticMaps
import «section 6».AbsentFocusCentripetal

/-! Actual label-definable boundary foci. Their full scalar graph is
formed from the center and offset maps, and their leading terms agree
with the surrounding source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable (F : UnaryFocusData A) (d : (Fin r → RVInfinity M) → VF M)
variable (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
variable (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)

def boundaryFocusMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (vfTupleBinaryMap S .sub).comp ((Map.inclusion (fun _ _ => Set.mem_univ _)).comp (F.focusMap.pair dMap))

include hdMap in
theorem boundaryFocusMap_value (p : focusActive A F.activeTags) :
    (F.boundaryFocusMap dMap p).val 0=F.focus p.val.2-d p.val.2 := by
  change (F.focusMap p).val 0-(dMap p).val 0=_
  rw [F.focusMap_eq,hdMap]

def boundaryFocusData
    (hSmall : ∀ p ∈ A.carrier,p.2 ∈ F.activeTags.carrier → vfValue (F.focus p.2) < vfValue (d p.2)) :
    UnaryFocusData A where
  activeTags := F.activeTags
  focus := fun u => F.focus u-d u
  focusMap := F.boundaryFocusMap dMap
  focusMap_eq := F.boundaryFocusMap_value d dMap hdMap
  sourceProper := F.sourceProper
  sourceDoublyBounded := F.sourceDoublyBounded
  tagged := F.tagged
  focusRV p hp hu := by
    have hf0 : F.focus p.2 ≠ 0 := F.focusImage_nonzero _ ⟨⟨p,hp,hu⟩,F.focusMap_eq _⟩
    exact (centered_disc_boundary_focus_leading_term (F.focus p.2) (d p.2) hf0 (hSmall p hp hu)).trans
      (F.focusRV p hp hu)

end DiamondIntegral.Section6.UnaryFocusData
