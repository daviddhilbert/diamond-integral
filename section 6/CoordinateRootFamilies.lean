import «section 6».VFCoordinateReindexing
import Section5.VerticalObstacles

/-! Original-base finite root families in the targeted last coordinate.
The checked vertical-obstacle construction is transported by an actual
coordinate relabeling, retaining its exact source and fiber bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

structure CoordinateRootFamily (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) where
  roots : DefSet (rawMixedSpace (M := M) (n+1) r) S
  subset : roots.carrier ⊆ A.carrier
  finite : ∀ (b : Fin n → VF M) (u : Fin r → RVInfinity M),
    {x : VF M | (Fin.snoc b x,u) ∈ roots.carrier}.Finite

namespace CoordinateRootFamily

variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def fibre (R : CoordinateRootFamily A) (b : Fin n → VF M) (u : Fin r → RVInfinity M) : Finset (VF M) :=
  (R.finite b u).toFinset

theorem mem_fibre (R : CoordinateRootFamily A) (b : Fin n → VF M) (u : Fin r → RVInfinity M) (x : VF M) :
    x ∈ R.fibre b u ↔ (Fin.snoc b x,u) ∈ R.roots.carrier := (R.finite b u).mem_toFinset

def Bound (R : CoordinateRootFamily A) (N : ℕ) : Prop := ∀ b u, (R.fibre b u).card ≤ N

def fromHead (hc : CanonicalStructure.IsCanonical (M := M))
    (R : SpecialTransformations.Section5.VerticalRootFamily (toOrdinarySet hc (reindexedVFSet A (lastHeadIndices n)))) :
    CoordinateRootFamily A where
  roots := reindexedVFSet (fromOrdinarySet hc R.set) (lastHeadIndices n).symm
  subset := by
    intro p hp
    have hm := (mem_reindexedVFSet (fromOrdinarySet hc R.set) (lastHeadIndices n).symm p).mp hp
    have hA := R.subset hm
    have h := (mem_reindexedVFSet A (lastHeadIndices n) (reindexVFPoint (lastHeadIndices n) p)).mp hA
    rwa [reindexVFPoint_inverse] at h
  finite := by
    intro b u
    convert R.finite (b,u) using 1
    ext x
    change (Fin.snoc b x,u) ∈ (reindexedVFSet (fromOrdinarySet hc R.set) (lastHeadIndices n).symm).carrier ↔
      SpecialTransformations.Section5.insertHead x (b,u) ∈ SpecialTransformations.Section5.carrier R.set
    rw [mem_reindexedVFSet]
    rw [show ((lastHeadIndices n).symm).symm = lastHeadIndices n from Equiv.symm_symm _]
    rw [reindexVFPoint_lastHead_snoc]
    rfl

theorem fromHead_fibre (hc : CanonicalStructure.IsCanonical (M := M))
    (R : SpecialTransformations.Section5.VerticalRootFamily (toOrdinarySet hc (reindexedVFSet A (lastHeadIndices n))))
    (b : Fin n → VF M) (u : Fin r → RVInfinity M) :
    (fromHead hc R).fibre b u = R.fibre (b,u) := by
  ext x
  rw [mem_fibre,SpecialTransformations.Section5.VerticalRootFamily.mem_fibre]
  change (Fin.snoc b x,u) ∈ (reindexedVFSet (fromOrdinarySet hc R.set) (lastHeadIndices n).symm).carrier ↔ _
  rw [mem_reindexedVFSet]
  rw [show ((lastHeadIndices n).symm).symm = lastHeadIndices n from Equiv.symm_symm _]
  rw [reindexVFPoint_lastHead_snoc]
  rfl

theorem fromHead_bound (hc : CanonicalStructure.IsCanonical (M := M))
    (R : SpecialTransformations.Section5.VerticalRootFamily (toOrdinarySet hc (reindexedVFSet A (lastHeadIndices n))))
    (N : ℕ) (hN : R.Bound N) : (fromHead hc R).Bound (N+1) := by
  intro b u
  rw [fromHead_fibre]
  exact R.card_bound N hN (b,u)

end CoordinateRootFamily

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CoordinateRootControl {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (R : CoordinateRootFamily A) (P : Set (Mixed M (n+1) r)) : Prop :=
  ∀ (b : Fin n → VF M) (u : Fin r → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G),
    (∀ x ∈ Balls.openDisc Valued.v a ρ, (Fin.snoc b x,u) ∈ A.carrier) →
    (∀ x ∈ R.fibre b u, x ∉ Balls.openDisc Valued.v a ρ) →
    ∀ x ∈ Balls.openDisc Valued.v a ρ, ∀ y ∈ Balls.openDisc Valued.v a ρ,
      ((Fin.snoc b x,u) ∈ P ↔ (Fin.snoc b y,u) ∈ P)

end DiamondIntegral.Section6
