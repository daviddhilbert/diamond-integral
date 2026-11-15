import IntegrationSection5.GammaCoordinateCanonical

/-! The actual projection recovering the source of a coordinate canonical map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def forgetCoordinateLabel (q : Point (M := M) n (1+m)) : Point (M := M) n m :=
  (q.1,fun j => q.2 (Fin.natAdd 1 j))

theorem forgetCoordinateLabel_canonical (i : Fin n) (q : Point (M := M) n m) :
    forgetCoordinateLabel (coordinateCanonical i q) = q := by
  refine Prod.ext rfl ?_
  funext j
  change Fin.append (fun _ : Fin 1 => rv (vfAt q i)) q.2 (Fin.natAdd 1 j) = q.2 j
  exact Fin.append_right _ _ j

def forgetCoordinateLabelMap (A : DefSet (M := M) S n (1+m)) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A forgetCoordinateLabel
    (fun z => Sum.elim (fun i => z (.inl i)) (fun j => z (.inr (Fin.natAdd 1 j))))
    (by intro j; cases j with
        | inl j => exact rawProj S (.inl j : Fin n ⊕ Fin (1+m))
        | inr j => exact rawProj S (.inr (Fin.natAdd 1 j) : Fin n ⊕ Fin (1+m)))
    (by intro c; exact ⟨c.property.1,fun j => c.property.2 (Fin.natAdd 1 j)⟩)
    (by intro c; rfl)

theorem coordinateCanonical_inverse_val (A : DefSet (M := M) S n m) (i : Fin n)
    (q : coordinateCanonicalImage A i) :
    (Map.inverse (coordinateCanonicalBijection A i) (coordinateCanonicalBijection_bijective A i) q).val =
      forgetCoordinateLabel q.val := by
  have h := congrArg (fun z : coordinateCanonicalImage A i => forgetCoordinateLabel z.val)
    (Map.apply_inverse (coordinateCanonicalBijection A i) (coordinateCanonicalBijection_bijective A i) q)
  exact (forgetCoordinateLabel_canonical i _).symm.trans h

theorem forgetCoordinateLabel_mem (A : DefSet (M := M) S n m) (i : Fin n)
    (q : coordinateCanonicalImage A i) : forgetCoordinateLabel q.val ∈ carrier A := by
  obtain ⟨a,ha⟩ := q.property
  have h := (congrArg forgetCoordinateLabel ha).symm.trans (forgetCoordinateLabel_canonical i a.val)
  exact h.symm ▸ a.property

theorem forgetCoordinateLabel_erase (i : Fin n) (q : Point (M := M) n (1+m)) :
    forgetCoordinateLabel (erase i q) = erase i (forgetCoordinateLabel q) := rfl

end IntegrationInACVF.Section5
