import «section 6».RVCoordinateBundleGeometry

/-! A carried RV-disc needs its own named radius only in the carried
coordinate. All old radii, including the aperture-dominated target
radius of a centripetal focus, can be retained unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem init_update_castSucc (a : Fin (n+1) → VF M) (j : Fin n) (c : VF M) :
    Fin.init (Function.update a j.castSucc c) = Function.update (Fin.init a) j c := by
  funext i
  by_cases hi : i = j
  · subst i
    simp only [Fin.init,Function.update_self]
  · have hij : i.castSucc ≠ j.castSucc := fun h => hi (Fin.castSucc_inj.mp h)
    simp only [Fin.init,Function.update_of_ne hi,Function.update_of_ne hij]

theorem snoc_coordinate_radii (j : Fin n) (α : Gamma M) (β : Fin n → Gamma M) (ε : Gamma M) :
    Fin.snoc (fun i => if i = j then α else β i) ε =
      (fun i : Fin (n+1) => if i = j.castSucc then α else (Fin.snoc β ε : Fin (n+1) → Gamma M) i) := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Fin.snoc_last,Ne.symm (Fin.castSucc_ne_last j),ite_false]
  · simp only [Fin.snoc_castSucc,Fin.castSucc_inj]

theorem rvCoordinateBundle_invariant_preserving_old_radii
    (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) (u : Fin r → RVInfinity M)
    (α : Fin n → Gamma M) (hC : AlphaInvariant α (vfFibre C.carrier u))
    (ε : Fin (n+1) → Gamma M)
    (hW : AlphaInvariant ε (vfFibre (rvCoordinateBundle C k).carrier u)) :
    AlphaInvariant (Fin.snoc α (ε (Fin.last n))) (vfFibre (rvCoordinateBundle C k).carrier u) := by
  have step (a b : Fin (n+1) → VF M)
      (hab : Congruent (Fin.snoc α (ε (Fin.last n))) a b)
      (ha : a ∈ vfFibre (rvCoordinateBundle C k).carrier u) :
      b ∈ vfFibre (rvCoordinateBundle C k).carrier u := by
    have hInit : Congruent α (Fin.init a) (Fin.init b) := by
      intro i
      simpa only [Fin.snoc_castSucc,Fin.init] using hab i.castSucc
    have hBase : (Fin.init b,u) ∈ C.carrier := (hC _ _ hInit).mp ha.1
    let b' := Fin.snoc (Fin.init a) (b (Fin.last n))
    have hCong : Congruent ε a b' := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [b',Fin.snoc_last] using hab (Fin.last n)
      · simpa only [b',Fin.snoc_castSucc,Fin.init,sub_self,valueHom_eq_value]
          using gamma_lt_value_zero (ε j.castSucc)
    have hb' := (hW a b' hCong).mp ha
    refine ⟨hBase,?_⟩
    simpa only [b',Fin.snoc_last] using hb'.2
  exact fun a b hab => ⟨step a b hab,step b a hab.symm⟩

end DiamondIntegral.Section6
