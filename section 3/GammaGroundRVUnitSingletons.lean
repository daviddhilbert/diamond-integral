import «section 3».GammaGroundRVUnitCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Every coordinate of a point in an actual definable singleton RV-unit
tuple set is definable over exactly the original mixed ground. -/
theorem gammaGroundRVUnit_subsingleton_point_definable
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) [Subsingleton R] (r : R) :
    ∀ i, DefinableClosureAtBase B .rv (rvUnitValues r.val i) := by
  intro i
  have he : rvUnitRawCoordinateImage R.carrier i = {rvUnitValues r.val i} := by
    ext t
    constructor
    · rintro ⟨z,⟨s,hs,rfl⟩,he⟩
      have hsr : s = r.val := congrArg Subtype.val (Subsingleton.elim (⟨s,hs⟩ : R) r)
      exact he.symm.trans (congrFun (congrArg rvUnitValues hsr) i)
    · intro ht
      have ht' : t = rvUnitValues r.val i := ht
      subst t
      exact ⟨rvUnitValues r.val,⟨r.val,r.property,rfl⟩,rfl⟩
  change DefinableAtBase B .rv {rvUnitValues r.val i}
  rw [← he]
  exact gammaGroundRVUnitCoordinate_definable R i
end DiamondIntegral.Section3
