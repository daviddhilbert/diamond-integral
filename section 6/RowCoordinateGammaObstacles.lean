import «section 6».RowForms
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».CoordinateObstacles
import «section 6».RowGammaCodeLocus

/-! (Row-form version for Remark 6.20, translated from `CoordinateGammaObstacles`.)
 A single bounded original-base coordinate-root family controls every
Gamma level. The checked obstacle theorem permits independent RV arities
for its ambient and predicate: the extra Gamma code is never a parameter
of the root family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {q : ℕ}

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_coordinate_gamma_controlling_roots_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (ω : Mixed M (n+1) r → Set (rawRVSpace (M := M) q).Carrier)
    (hGraph : MixedRowGraphDefinable S A.carrier ω) :
    ∃ R : CoordinateRootFamily A, ∃ N : ℕ, R.Bound N ∧
      ∀ γ : Set (rawRVSpace (M := M) q).Carrier, CoordinateRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ} := by
  let e := lastHeadIndices n
  let A' := toOrdinarySet hc (reindexedVFSet A e)
  let P := gammaCodeLocusRow A ω hGraph
  let P' := toOrdinarySet hc (reindexedVFSet P e)
  have hA' : SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier A') :=
    (ordinary_pullback_iff _).mpr (reindexedVFSet_rvPullback A e hARV)
  obtain ⟨R,N,hN,hControl⟩ := SpecialTransformations.Section5.uniformVerticalObstacles hs hsmall Valued.v hv n P' A' hA'
  refine ⟨CoordinateRootFamily.fromHead hc R,N+1,CoordinateRootFamily.fromHead_bound hc R N hN,?_⟩
  intro γ b u a ρ hAmbient hAvoid x hx y hy
  have hAmbient' (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) :
      SpecialTransformations.Section5.insertHead z (b,u) ∈ SpecialTransformations.Section5.carrier A' := by
    apply (mem_reindexedVFSet A e _).mpr
    change reindexVFPoint e.symm (Fin.cons z b,u) ∈ A.carrier
    rw [← reindexVFPoint_lastHead_snoc,reindexVFPoint_inverse]
    exact hAmbient z hz
  have hAvoid' (z : VF M) (hz : z ∈ R.fibre (b,u)) : z ∉ Balls.openDisc Valued.v a ρ :=
    hAvoid z (by rw [CoordinateRootFamily.fromHead_fibre]; exact hz)
  have hMem (z : VF M) (v : Fin q → RVInfinity M) :
      ((SpecialTransformations.Section5.insertHead z (b,u)).1,Fin.append u v) ∈
          SpecialTransformations.Section5.carrier P' ↔
        (Fin.snoc b z,u) ∈ A.carrier ∧ v ∈ ω (Fin.snoc b z,u) := by
    change (Fin.cons z b,Fin.append u v) ∈ (reindexedVFSet P e).carrier ↔ _
    rw [mem_reindexedVFSet]
    rw [← reindexVFPoint_lastHead_snoc,reindexVFPoint_inverse]
    rw [gammaCodeLocus_at_row]
  have hEq : ω (Fin.snoc b x,u) = ω (Fin.snoc b y,u) := by
    ext v
    have h := hControl (b,u) a ρ hAmbient' hAvoid' x hx y hy (Fin.append u v)
    constructor
    · intro hv
      exact ((hMem y v).mp (h.mp ((hMem x v).mpr ⟨hAmbient x hx,hv⟩))).2
    · intro hv
      exact ((hMem x v).mp (h.mpr ((hMem y v).mpr ⟨hAmbient y hy,hv⟩))).2
  constructor
  · rintro ⟨_,hγ⟩
    exact ⟨hAmbient y hy,hEq.symm.trans hγ⟩
  · rintro ⟨_,hγ⟩
    exact ⟨hAmbient x hx,hEq.trans hγ⟩

end DiamondIntegral.Section6
