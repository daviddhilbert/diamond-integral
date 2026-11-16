import «section 6».AttainableRadii

/-! The zero-centered preliminary operation retains the chosen uniform
invariance radius, as required by the manuscript's preparation remark. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem AlphaInvariant.image_translation {α : Fin n → Gamma M} {D : Set (Fin n → VF M)}
    (hD : AlphaInvariant α D) (b : Fin n → VF M) : AlphaInvariant α ((fun x => x + b) '' D) := by
  have step (y z : Fin n → VF M) (hyz : Congruent α y z)
      (hy : y ∈ (fun x => x + b) '' D) : z ∈ (fun x => x + b) '' D := by
    obtain ⟨x,hx,rfl⟩ := hy
    have hc : Congruent α x (z-b) := by
      intro i
      change (α i).val < vfValue (x i - (z i - b i))
      rw [show x i - (z i - b i) = (x i + b i) - z i by abel]
      exact hyz i
    exact ⟨z-b,(hD x (z-b) hc).mp hx,sub_add_cancel _ _⟩
  exact fun y z hyz => ⟨step y z hyz,step z y hyz.symm⟩

namespace ZeroCenteredData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem core_eq_of_congruent (D : ZeroCenteredData A) {a b : Fin n → VF M}
    (hab : Congruent (fun _ => finiteValue D.center D.center_nonzero) a b)
    (u : Fin r → RVInfinity M) : D.core (a,u) = D.core (b,u) := by
  have step (x y : VF M) (hxy : vfValue D.center < vfValue (x-y))
      (hx : vfValue D.center < vfValue x) : vfValue D.center < vfValue y := by
    have h := vfValue_min_le_sub x (x-y)
    rw [show x - (x-y) = y by abel] at h
    exact (lt_min hx hxy).trans_le h
  funext i
  change decide (vfValue D.center < vfValue (a i)) = decide (vfValue D.center < vfValue (b i))
  apply decide_eq_decide.mpr
  exact ⟨step _ _ (hab i),step _ _ (hab.symm i)⟩

theorem branch_invariant (D : ZeroCenteredData A) (u : Fin r → RVInfinity M) (b : Fin n → Bool) :
    AlphaInvariant (fun _ => finiteValue D.center D.center_nonzero) (D.branch u b) := by
  intro x y hxy
  exact and_congr (D.invariant u x y hxy)
    (by rw [D.core_eq_of_congruent hxy u])

theorem image_fibres_invariant (D : ZeroCenteredData A) (h00 : M ⊨ Axioms.ACVF00)
    (v : Fin (n+r) → RVInfinity M) :
    AlphaInvariant (fun _ => finiteValue D.center D.center_nonzero) (vfFibre D.map.image.carrier v) := by
  classical
  rw [D.image_fibre]
  let u := v ∘ Fin.natAdd n
  by_cases he : ∃ b, D.tags u b = v
  · obtain ⟨b,hb⟩ := he
    change AlphaInvariant _ (graphFibreRange D.bijection u v)
    rw [← hb,D.graphRange_tags h00]
    exact (D.branch_invariant u b).image_translation (D.shift b)
  · rw [graphFibreRange_eq_image,D.graphSource_empty u v he,Set.image_empty]
    exact fun _ _ _ => Iff.rfl

end ZeroCenteredData
end DiamondIntegral.Section6
