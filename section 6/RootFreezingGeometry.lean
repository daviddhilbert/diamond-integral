import «section 6».CoordinateRootFoci

/-! Freezing preserves full current-domain membership in both
directions and commutes with insertion of the targeted VF coordinate.
These equalities transport finite root fibers and their control invariant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}

theorem mixedFamilyFreeze_mem_iff
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (C : Set (Mixed M n r))
    (hprod : ∀ D : balls, CoordinateProductDomain C (vfOpenBall D.val) (centers D) j)
    (p : Mixed M n r) : mixedFamilyFreeze balls centers j p ∈ C ↔ p ∈ C := by
  by_cases hx : ∃ D : balls, p.1 j ∈ vfOpenBall D.val
  · obtain ⟨D,hD⟩ := hx
    have hf : vfFamilyFreeze balls centers (p.1 j) = centers D := by
      rw [vfFamilyFreeze_eq balls centers hsep]
      exact familyFreeze_inside _ _ (fun D E x hx hE => hsep D E x.val hx hE) D _ hD
    simpa only [mixedFamilyFreeze,hf] using (hprod D p hD).symm
  · have hf : vfFamilyFreeze balls centers (p.1 j) = p.1 j := by
      rw [vfFamilyFreeze_eq balls centers hsep]
      exact familyFreeze_outside _ _ _ (not_exists.mp hx)
    simpa only [mixedFamilyFreeze,hf,Function.update_eq_self,Prod.mk.eta]

theorem mixedFamilyFreeze_snoc
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (b : Fin n → VF M) (x : VF M) (u : Fin r → RVInfinity M) :
    mixedFamilyFreeze balls centers j.castSucc (Fin.snoc b x,u) =
      (Fin.snoc (mixedFamilyFreeze balls centers j (b,u)).1 x,u) := by
  apply Prod.ext
  · change Function.update (Fin.snoc b x : Fin (n+1) → VF M) j.castSucc
        (vfFamilyFreeze balls centers ((Fin.snoc b x : Fin (n+1) → VF M) j.castSucc)) =
          (Fin.snoc (Function.update b j (vfFamilyFreeze balls centers (b j))) x : Fin (n+1) → VF M)
    rw [Fin.snoc_castSucc]
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Function.update_of_ne (Ne.symm (Fin.castSucc_ne_last j)),Fin.snoc_last]
    · by_cases hk : k = j
      · subst k
        simp only [Function.update_self,Fin.snoc_castSucc,mixedFamilyFreeze]
      · have hkj : k.castSucc ≠ j.castSucc := fun h => hk (Fin.castSucc_inj.mp h)
        simp only [Function.update_of_ne hkj,Fin.snoc_castSucc,mixedFamilyFreeze,Function.update_of_ne hk]
  · rfl

end DiamondIntegral.Section6.FMT
