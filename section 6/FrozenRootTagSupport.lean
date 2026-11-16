import «section 6».FrozenCoordinateRoots

/-! Freezing actual roots retains every old RV label. Thus any active
condition expressed by those labels remains valid for all new roots. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem frozen_tags_subset (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprod : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc) :
    Prod.snd '' (R.frozen balls centers j hsep hballs hcenters hprod).roots.carrier ⊆
      Prod.snd '' R.roots.carrier := by
  rintro u ⟨p,hp,rfl⟩
  have h := (R.mem_frozenRoots balls centers j hsep hballs hcenters hprod p).mp hp
  exact ⟨FMT.mixedFamilyFreeze balls centers j.castSucc p,h,rfl⟩

end DiamondIntegral.Section6.CoordinateRootFamily
