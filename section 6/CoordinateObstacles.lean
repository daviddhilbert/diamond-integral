import «section 6».CoordinateRootFamilies

/-! The actual original-base uniformly bounded finite root family
controlling a definable predicate in one VF coordinate. The earlier
checked obstacle export is used with its genuine saturation/smallness
hypotheses and with an exact original-base coordinate/presentation bridge. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_controlling_coordinate_roots
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (P : DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    ∃ R : CoordinateRootFamily A, ∃ N : ℕ, R.Bound N ∧ CoordinateRootControl (G := G) R P.carrier := by
  let e := lastHeadIndices n
  let A' := toOrdinarySet hc (reindexedVFSet A e)
  let P' := toOrdinarySet hc (reindexedVFSet P e)
  have hA' : SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier A') :=
    (ordinary_pullback_iff _).mpr (reindexedVFSet_rvPullback A e hARV)
  obtain ⟨R,N,hN,hControl⟩ := SpecialTransformations.Section5.uniformVerticalObstacles hs hsmall Valued.v hv n P' A' hA'
  refine ⟨CoordinateRootFamily.fromHead hc R,N+1,CoordinateRootFamily.fromHead_bound hc R N hN,?_⟩
  intro b u a ρ hAmbient hAvoid x hx y hy
  have hAmbient' (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) :
      SpecialTransformations.Section5.insertHead z (b,u) ∈ SpecialTransformations.Section5.carrier A' := by
    apply (mem_reindexedVFSet A e _).mpr
    change reindexVFPoint e.symm (Fin.cons z b,u) ∈ A.carrier
    rw [← reindexVFPoint_lastHead_snoc,reindexVFPoint_inverse]
    exact hAmbient z hz
  have hAvoid' (z : VF M) (hz : z ∈ R.fibre (b,u)) : z ∉ Balls.openDisc Valued.v a ρ :=
    hAvoid z (by rw [CoordinateRootFamily.fromHead_fibre]; exact hz)
  have h := hControl (b,u) a ρ hAmbient' hAvoid' x hx y hy u
  have hMem (z : VF M) :
      ((SpecialTransformations.Section5.insertHead z (b,u)).1,u) ∈ SpecialTransformations.Section5.carrier P' ↔
        (Fin.snoc b z,u) ∈ P.carrier := by
    change (Fin.cons z b,u) ∈ (reindexedVFSet P e).carrier ↔ (Fin.snoc b z,u) ∈ P.carrier
    rw [mem_reindexedVFSet]
    rw [← reindexVFPoint_lastHead_snoc,reindexVFPoint_inverse]
  exact (hMem x).symm.trans (h.trans (hMem y))

end DiamondIntegral.Section6
