import «section 6».ProtectedFocusFreezing

/-! Actual FMT composition preserves the permitted focus leading
term when its product-domain condition holds on the current ambient.
The frozen complementary coordinate leaves the targeted last VF
coordinate and every old RV label unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem mixedFamilyFreeze_init
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M)
    (p : Mixed M (n+2) r) :
    let q := mixedFamilyFreeze balls centers (0 : Fin (n+1)).castSucc p
    (Fin.init q.1,q.2) = mixedFamilyFreeze balls centers 0 (Fin.init p.1,p.2) := by
  apply Prod.ext
  · change Fin.init (Function.update p.1 (0 : Fin (n+1)).castSucc _) = _
    rw [init_update_castSucc]
    rfl
  · rfl

theorem totalFocusFibre_frozen_at
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S} (D : FocusFreezingData C)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B) (p : Mixed M (n+1) r) (hp : p ∈ C.carrier) :
    totalFocusFibre (D.frozenMap f) p.2 p.1 0 =
      totalFocusFibre f (mixedFamilyFreeze D.balls D.centers 0 p).2
        (mixedFamilyFreeze D.balls D.centers 0 p).1 0 := by
  let q := mixedFamilyFreeze D.balls D.centers 0 p
  have hq : q ∈ C.carrier := mixedFamilyFreeze_mapsTo D.balls D.centers 0 C.carrier
    D.separated D.product_domain hp
  have hLeft := congrFun (totalFocusFibre_at (D.frozenMap f) p.2 p.1 hp) 0
  have hRight := congrFun (totalFocusFibre_at f q.2 q.1 hq) 0
  apply hLeft.trans
  change (f ⟨q,hq⟩).val 0 = totalFocusFibre f q.2 q.1 0
  exact hRight.symm

theorem frozenProjectedFocus_leadingTerms
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {U : DefSet (rawRVSpace (M := M) r) S}
    (D : FocusFreezingData (projectedActiveDomain A U))
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hprod : ∀ E : D.balls, CoordinateProductDomain A.carrier (vfOpenBall E.val)
      (D.centers E) (0 : Fin (n+1)).castSucc)
    (hFocusRV : ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre f p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last (n+1)))) :
    ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre (D.frozenMap f) p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last (n+1))) := by
  intro p hp hu
  let q := mixedFamilyFreeze D.balls D.centers (0 : Fin (n+1)).castSucc p
  have hq : q ∈ A.carrier := mixedFamilyFreeze_mapsTo D.balls D.centers _ A.carrier D.separated hprod hp
  have hpC : (Fin.init p.1,p.2) ∈ (projectedActiveDomain A U).carrier := ⟨⟨p,hp,hu⟩,rfl⟩
  have hAt := totalFocusFibre_frozen_at D f (Fin.init p.1,p.2) hpC
  have hInit : mixedFamilyFreeze D.balls D.centers 0 (Fin.init p.1,p.2) = (Fin.init q.1,q.2) :=
    (mixedFamilyFreeze_init D.balls D.centers p).symm
  have hLast : q.1 (Fin.last (n+1)) = p.1 (Fin.last (n+1)) := by
    change Function.update p.1 (0 : Fin (n+1)).castSucc
      (vfFamilyFreeze D.balls D.centers (p.1 (0 : Fin (n+1)).castSucc))
        (Fin.last (n+1)) = p.1 (Fin.last (n+1))
    rw [Function.update_of_ne (Ne.symm (Fin.castSucc_ne_last (0 : Fin (n+1))))]
  rw [hAt,hInit]
  exact (hFocusRV q hq hu).trans (congrArg (rv M) hLast)

end DiamondIntegral.Section6.FMT
