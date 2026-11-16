import «section 6».CoordinateRootStep

/-! The actual noncore root family after a permitted last-coordinate
step is uniformly finite, and its uniform bound decreases by one.
All source and mean-compatibility obligations are explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def stepFamily (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (hActive : ∀ p ∈ R.roots.carrier, p.2 ∈ D.activeTags.carrier)
    (hMean : ∀ p ∈ R.roots.carrier, D.extendedFocus p = Barycentre.mean (R.fibre (Fin.init p.1) p.2)) :
    CoordinateRootFamily (regularizeMap D.map.image).image where
  roots := R.remainingRoots D
  subset := by
    intro q hq
    obtain ⟨a,ha,hCore,he⟩ := (R.remainingRoots_iff D h00 q).mp hq
    exact he ▸ (centripetalStepMap D a).property
  finite := fun b u =>
    ((noncoreRootChild (R.fibre b (coordinateStepOldTags u)) (R.cutoff D b (coordinateStepOldTags u))
      (u (Fin.castAdd (1+r) (Fin.last n)))).finite_toSet).subset
        (fun x hx => R.remainingRoots_child_subset D h00 hj hActive hMean b u x hx)

theorem stepFamily_bound (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (hActive : ∀ p ∈ R.roots.carrier, p.2 ∈ D.activeTags.carrier)
    (hMean : ∀ p ∈ R.roots.carrier, D.extendedFocus p = Barycentre.mean (R.fibre (Fin.init p.1) p.2))
    (N : ℕ) (hN : R.Bound (N+1)) : (R.stepFamily D h00 hj hActive hMean).Bound N := by
  intro b u
  apply noncoreRootChild_bound h00 _ _ _ N (hN b (coordinateStepOldTags u))
  intro x hx
  exact R.remainingRoots_child_subset D h00 hj hActive hMean b u x
    (((R.stepFamily D h00 hj hActive hMean).mem_fibre b u x).mp hx)

end DiamondIntegral.Section6.CoordinateRootFamily
