import «section 6».CoordinateObstacles

/-! One actual original-base uniformly bounded coordinate-root family
controls every member of a finite definable family. The finite union
retains exact source inclusion and an explicit total fiber bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def CoordinateRootFamily.union (R Q : CoordinateRootFamily A) : CoordinateRootFamily A where
  roots := ⟨R.roots.carrier ∪ Q.roots.carrier,R.roots.definable.union _ Q.roots.definable⟩
  subset := fun _ h => h.elim (fun hp => R.subset hp) (fun hp => Q.subset hp)
  finite := fun b u => (R.finite b u).union (Q.finite b u)

theorem CoordinateRootFamily.fibre_union (R Q : CoordinateRootFamily A)
    (b : Fin n → VF M) (u : Fin r → RVInfinity M) :
    (R.union Q).fibre b u = R.fibre b u ∪ Q.fibre b u := by
  ext x
  rw [Finset.mem_union,CoordinateRootFamily.mem_fibre,CoordinateRootFamily.mem_fibre,CoordinateRootFamily.mem_fibre]
  rfl

theorem CoordinateRootFamily.union_bound (R Q : CoordinateRootFamily A) (d e : ℕ)
    (hR : R.Bound d) (hQ : Q.Bound e) : (R.union Q).Bound (d+e) := by
  intro b u
  rw [CoordinateRootFamily.fibre_union]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hR b u) (hQ b u))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CoordinateRootControl.mono {R Q : CoordinateRootFamily A}
    {P : Set (Mixed M (n+1) r)} (hR : CoordinateRootControl (G := G) R P)
    (hRQ : R.roots.carrier ⊆ Q.roots.carrier) : CoordinateRootControl (G := G) Q P := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  exact hR b u a ρ hAmbient (fun z hz => hAvoid z
    ((Q.mem_fibre b u z).mpr (hRQ ((R.mem_fibre b u z).mp hz)))) x hx y hy

theorem exists_finite_controlling_coordinate_roots {k : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    ∃ R : CoordinateRootFamily A, ∃ N : ℕ, R.Bound N ∧
      ∀ i, CoordinateRootControl (G := G) R (P i).carrier := by
  induction k with
  | zero =>
    obtain ⟨R,N,hN,hControl⟩ := exists_controlling_coordinate_roots hc hs hsmall hv A hARV A
    exact ⟨R,N,hN,fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨R,N,hN,hR⟩ := exists_controlling_coordinate_roots hc hs hsmall hv A hARV (P 0)
    obtain ⟨Q,L,hL,hQ⟩ := ih (Fin.tail P)
    refine ⟨R.union Q,N+L,R.union_bound Q N L hN hL,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hR.mono (fun _ h => Or.inl h)
    · exact (hQ j).mono (fun _ h => Or.inr h)

end DiamondIntegral.Section6
