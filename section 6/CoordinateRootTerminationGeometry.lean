import «section 6».CoordinateRootControlStep

/-! When the actual coordinate-root family is empty, every controlled
piece contains each whole last-coordinate RV disc that it meets. With
its retained leading-term tag this is an equality of actual full bundles. -/

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
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} {R : CoordinateRootFamily A}
variable {P : Set (Mixed M (n+1) r)}

theorem CoordinateRootControl.empty_roots_coordinate_saturated
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hControl : CoordinateRootControl (G := G) R P) (hEmpty : R.roots.carrier = ∅)
    (hA : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) (hPA : P ⊆ A.carrier) :
    ∀ p ∈ P, ∀ y : VF M, rv M y = rv M (p.1 (Fin.last n)) →
      (Function.update p.1 (Fin.last n) y,p.2) ∈ P := by
  intro p hp y hy
  have hpA := hPA hp
  have hp0 : p.1 (Fin.last n) ≠ 0 := hD.nonzero hpA (Fin.last n)
  let ρ : Balls.OpenRadius G := Balls.openRadius (Valued.v (p.1 (Fin.last n)))
    ((map_ne_zero (Valued.v : Valuation (VF M) G)).mpr hp0)
  have hDisc := Balls.rvFibre_eq_openDisc Valued.v hv (p.1 (Fin.last n)) hp0
  have hRV (x : VF M) : x ∈ Balls.openDisc Valued.v (p.1 (Fin.last n)) ρ ↔ rv M x = rv M (p.1 (Fin.last n)) := by
    rw [← hDisc]
    change iRv x.val = iRv (p.1 (Fin.last n)).val ↔ rv M x = rv M (p.1 (Fin.last n))
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  have hAmbient (x : VF M) (hx : x ∈ Balls.openDisc Valued.v (p.1 (Fin.last n)) ρ) :
      (Fin.snoc (Fin.init p.1) x,p.2) ∈ A.carrier := by
    apply rvPullback_mem_of_sameRV (q := (Fin.snoc (Fin.init p.1) x,p.2)) hA hpA ?_ rfl
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change rv M (p.1 (Fin.last n)) = rv M ((Fin.snoc (Fin.init p.1) x : Fin (n+1) → VF M) (Fin.last n))
      simpa only [Fin.snoc_last] using ((hRV x).mp hx).symm
    · change rv M (p.1 j.castSucc) = rv M ((Fin.snoc (Fin.init p.1) x : Fin (n+1) → VF M) j.castSucc)
      simp only [Fin.snoc_castSucc,Fin.init]
  have hAvoid (x : VF M) (hx : x ∈ R.fibre (Fin.init p.1) p.2) : x ∉ Balls.openDisc Valued.v (p.1 (Fin.last n)) ρ := by
    have hh := (R.mem_fibre _ _ _).mp hx
    rw [hEmpty] at hh
    exact False.elim hh
  have h := hControl (Fin.init p.1) p.2 (p.1 (Fin.last n)) ρ hAmbient hAvoid
    (p.1 (Fin.last n)) (Balls.centre_mem_openDisc Valued.v _ ρ) y ((hRV y).mpr hy)
  have hOld : (Fin.snoc (Fin.init p.1) (p.1 (Fin.last n)),p.2) = p := by rw [Fin.snoc_init_self]
  have hNew : (Fin.snoc (Fin.init p.1) y,p.2) = (Function.update p.1 (Fin.last n) y,p.2) := by
    apply Prod.ext
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last,Function.update_self]
      · simp only [Fin.snoc_castSucc,Function.update_of_ne (Fin.castSucc_ne_last j),Fin.init]
    · rfl
  rw [hOld,hNew] at h
  exact h.mp hp

theorem CoordinateRootControl.empty_roots_bundle
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hControl : CoordinateRootControl (G := G) R C.carrier) (hEmpty : R.roots.carrier = ∅)
    (hA : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) (hCA : C.carrier ⊆ A.carrier)
    (j : Fin r) (htag : ∀ p ∈ C.carrier, rv M (p.1 (Fin.last n)) = p.2 j) :
    C.carrier = (rvCoordinateBundle (vfDropLast C).image j).carrier :=
  coordinate_bundle_of_replacement C j htag
    (hControl.empty_roots_coordinate_saturated hv hEmpty hA hD hCA)

end DiamondIntegral.Section6
