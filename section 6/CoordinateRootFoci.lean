import «section 6».CoordinateRootMeans

/-! Actual coordinate-root means have the permitted source leading
term wherever the root fiber is nonempty. The original-base mean map
and every full source/tag condition remain explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem meanMap_leadingTerm (R : CoordinateRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (N : ℕ) (hN : R.Bound N) (U : DefSet (rawRVSpace (M := M) r) S)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hNonempty : ∀ p ∈ A.carrier, p.2 ∈ U.carrier → (R.fibre (Fin.init p.1) p.2).Nonempty) :
    ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre (R.meanMap h00 N hN (projectedActiveDomain A U)) p.2 (Fin.init p.1) 0) =
        rv M (p.1 (Fin.last n)) := by
  intro p hp hu
  let C := projectedActiveDomain A U
  have hpC : (Fin.init p.1,p.2) ∈ C.carrier := ⟨⟨p,hp,hu⟩,rfl⟩
  rw [totalFocusFibre_at _ _ _ hpC,R.meanMap_value]
  apply SpecialTransformations.Section5.mean_sameRV h00 _ (hNonempty p hp hu)
  intro x hx
  have h := congrFun (htag _ (R.subset ((R.mem_fibre _ _ _).mp hx)) p hp rfl) (Fin.last n)
  change rv M ((Fin.snoc (Fin.init p.1) x : Fin (n+1) → VF M) (Fin.last n)) = rv M (p.1 (Fin.last n)) at h
  change rv M x = rv M (p.1 (Fin.last n))
  simpa only [Fin.snoc_last] using h

end DiamondIntegral.Section6.CoordinateRootFamily
