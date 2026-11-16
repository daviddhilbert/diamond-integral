import «section 6».FrozenCoordinateRoots

/-! The actual root-control invariant survives protected freezing.
Freezing the actual mean map is exactly the mean of the frozen root
fiber, so subsequent root-count descent uses the repaired focus itself. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem frozen_control (R : CoordinateRootFamily A)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hsep : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hballs : S.Definable LRV (OpenBallCodes.pullback balls))
    (hcenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (hprodA : ∀ D : balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (P : Set (Mixed M (n+1) r))
    (hprodP : ∀ D : balls, FMT.CoordinateProductDomain P (FMT.vfOpenBall D.val) (centers D) j.castSucc)
    (hControl : CoordinateRootControl (G := G) R P) :
    CoordinateRootControl (G := G) (R.frozen balls centers j hsep hballs hcenters hprodA) P := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  let q := FMT.mixedFamilyFreeze balls centers j (b,u)
  have hAmbient' (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) : (Fin.snoc q.1 z,u) ∈ A.carrier := by
    have hm := FMT.mixedFamilyFreeze_mapsTo balls centers j.castSucc A.carrier hsep hprodA (hAmbient z hz)
    rwa [FMT.mixedFamilyFreeze_snoc] at hm
  have hAvoid' (z : VF M) (hz : z ∈ R.fibre q.1 u) : z ∉ Balls.openDisc Valued.v a ρ :=
    hAvoid z (by rw [frozen_fibre]; exact hz)
  have h := hControl q.1 u a ρ hAmbient' hAvoid' x hx y hy
  have hX := FMT.mixedFamilyFreeze_mem_iff balls centers j.castSucc hsep P hprodP (Fin.snoc b x,u)
  have hY := FMT.mixedFamilyFreeze_mem_iff balls centers j.castSucc hsep P hprodP (Fin.snoc b y,u)
  rw [FMT.mixedFamilyFreeze_snoc] at hX hY
  exact hX.symm.trans (h.trans hY)

variable {B : DefSet (rawMixedSpace (M := M) (n+2) r) S}
variable {U : DefSet (rawRVSpace (M := M) r) S}

theorem frozen_meanMap_value (R : CoordinateRootFamily B) (h00 : M ⊨ Axioms.ACVF00)
    (N : ℕ) (hN : R.Bound N) (F : FMT.FocusFreezingData (projectedActiveDomain B U))
    (hprodB : ∀ D : F.balls, FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall D.val)
      (F.centers D) (0 : Fin (n+1)).castSucc) (p : projectedActiveDomain B U) :
    ((R.frozen F.balls F.centers 0 F.separated F.balls_definable F.centers_definable hprodB).meanMap h00 N
      (R.frozen_bound F.balls F.centers 0 F.separated F.balls_definable F.centers_definable hprodB N hN)
        (projectedActiveDomain B U) p).val 0 =
      (F.frozenMap (R.meanMap h00 N hN (projectedActiveDomain B U)) p).val 0 := by
  let R' := R.frozen F.balls F.centers 0 F.separated F.balls_definable F.centers_definable hprodB
  let f := R.meanMap h00 N hN (projectedActiveDomain B U)
  let q := FMT.mixedFamilyFreeze F.balls F.centers 0 p.val
  have hq : q ∈ (projectedActiveDomain B U).carrier :=
    FMT.mixedFamilyFreeze_mapsTo F.balls F.centers 0 _ F.separated F.product_domain p.property
  have hLeft : (R'.meanMap h00 N
      (R.frozen_bound F.balls F.centers 0 F.separated F.balls_definable F.centers_definable hprodB N hN)
        (projectedActiveDomain B U) p).val 0 = Barycentre.mean (R.fibre q.1 q.2) := by
    rw [meanMap_value,frozen_fibre]
    rfl
  have hRight : (F.frozenMap f p).val 0 = Barycentre.mean (R.fibre q.1 q.2) := by
    have hpValue := congrFun (totalFocusFibre_at (F.frozenMap f) p.val.2 p.val.1 p.property) 0
    have hqValue := congrFun (totalFocusFibre_at f q.2 q.1 hq) 0
    calc
      _ = totalFocusFibre (F.frozenMap f) p.val.2 p.val.1 0 := hpValue.symm
      _ = totalFocusFibre f q.2 q.1 0 := FMT.totalFocusFibre_frozen_at F f p.val p.property
      _ = (f ⟨q,hq⟩).val 0 := hqValue
      _ = Barycentre.mean (R.fibre q.1 q.2) := R.meanMap_value h00 N hN _ ⟨q,hq⟩
  exact hLeft.trans hRight.symm

end DiamondIntegral.Section6.CoordinateRootFamily
