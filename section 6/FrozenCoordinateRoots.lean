import «section 6».RootFreezingGeometry

/-! Freeze an actual finite coordinate-root family on the same current
ambient. Its complete original-base graph, exact frozen fibers, cardinal
bound and partition-control invariant are all retained. -/

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

def frozenRoots (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val))) :
    DefSet (rawMixedSpace (M := M) (n+1) r) S := by
  let F := FMT.mixedFamilyFreezeMap balls centers j.castSucc hsep hballs hcenters A
  exact ⟨{p | ∃ q : A, q.val = p ∧ (F q).val ∈ R.roots.carrier},Map.definable_preimage F R.roots.definable⟩

theorem mem_frozenRoots (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprod : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (p : Mixed M (n+1) r) :
    p ∈ (R.frozenRoots balls centers j hsep hballs hcenters).carrier ↔
      FMT.mixedFamilyFreeze balls centers j.castSucc p ∈ R.roots.carrier := by
  constructor
  · rintro ⟨q,rfl,hq⟩
    exact hq
  · intro hq
    have hp : p ∈ A.carrier := (FMT.mixedFamilyFreeze_mem_iff balls centers j.castSucc hsep A.carrier hprod p).mp
      (R.subset hq)
    exact ⟨⟨p,hp⟩,rfl,hq⟩

def frozen (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprod : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc) :
    CoordinateRootFamily A where
  roots := R.frozenRoots balls centers j hsep hballs hcenters
  subset := fun _ ⟨q,hq,_⟩ => hq ▸ q.property
  finite := by
    intro b u
    convert R.finite (FMT.mixedFamilyFreeze balls centers j (b,u)).1 u using 1
    ext x
    change (Fin.snoc b x,u) ∈ (R.frozenRoots balls centers j hsep hballs hcenters).carrier ↔ _
    rw [R.mem_frozenRoots balls centers j hsep hballs hcenters hprod,FMT.mixedFamilyFreeze_snoc]
    rfl

theorem frozen_fibre (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprod : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (b : Fin n → VF M) (u : Fin r → RVInfinity M) :
    (R.frozen balls centers j hsep hballs hcenters hprod).fibre b u =
      R.fibre (FMT.mixedFamilyFreeze balls centers j (b,u)).1 u := by
  ext x
  rw [mem_fibre,mem_fibre]
  change (Fin.snoc b x,u) ∈ (R.frozenRoots balls centers j hsep hballs hcenters).carrier ↔ _
  rw [R.mem_frozenRoots balls centers j hsep hballs hcenters hprod,FMT.mixedFamilyFreeze_snoc]

theorem frozen_bound (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprod : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (N : ℕ) (hN : R.Bound N) : (R.frozen balls centers j hsep hballs hcenters hprod).Bound N := by
  intro b u
  rw [frozen_fibre]
  exact hN _ _

end DiamondIntegral.Section6.CoordinateRootFamily
