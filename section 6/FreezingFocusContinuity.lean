import «section 6».MixedFreezing

/-! Freezing retains continuity on each actual RV fiber. Invariance of
the current focus domain supplies its coordinate product condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem coordinateProductDomain_of_invariant
    (C : Set (Mixed M n r)) (D : Set (VF M)) (c : VF M) (i : Fin n) (δ : Gamma M)
    (hC : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre C u))
    (hD : ∀ x ∈ D, δ.val < vfValue (x-c)) : CoordinateProductDomain C D c i := by
  intro p hp
  apply hC p.2 p.1 (Function.update p.1 i c)
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using hD (p.1 i) hp
  · simp only [Function.update_of_ne hj,sub_self]
    exact gamma_lt_value_zero δ

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfTupleFreeze_continuous
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite) (c : A → VF M) (i : Fin n)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E) :
    Continuous (fun a : Fin n → VF M => Function.update a i (vfFamilyFreeze A c (a i))) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self,Function.comp_def] using
      (vfFamilyFreeze_continuous hv A hA c hsep).comp (continuous_apply i)
  · simpa only [Function.update_of_ne hj] using (continuous_apply j : Continuous (fun a : Fin n → VF M => a j))

def focusFibre {C : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B)
    (u : Fin r → RVInfinity M) (a : vfFibre C.carrier u) : VF M :=
  (f ⟨(a.val,u),a.property⟩).val 0

theorem frozenFocusMap_continuous
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite) (c : A → VF M) (i : Fin n)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
    (hcdef : S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (c D).val)))
    {C : DefSet (rawMixedSpace (M := M) n r) S}
    (hprod : ∀ D : A, CoordinateProductDomain C.carrier (vfOpenBall D.val) (c D) i)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B)
    (u : Fin r → RVInfinity M) (hf : Continuous (focusFibre f u)) :
    Continuous (focusFibre (frozenFocusMap A c i hsep hAdef hcdef hprod f) u) := by
  let g (a : vfFibre C.carrier u) : vfFibre C.carrier u :=
    ⟨Function.update a.val i (vfFamilyFreeze A c (a.val i)),
      mixedFamilyFreeze_mapsTo A c i C.carrier hsep hprod a.property⟩
  have hg : Continuous g :=
    (((vfTupleFreeze_continuous hv A hA c i hsep).comp continuous_subtype_val).subtype_mk
      (fun a => mixedFamilyFreeze_mapsTo A c i C.carrier hsep hprod a.property))
  exact hf.comp hg

end DiamondIntegral.Section6.FMT
