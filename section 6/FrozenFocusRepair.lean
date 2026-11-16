import «section 6».FreezingRemovesDiscontinuities

/-! The uniform continuity repair for actual original-base focus maps.
The existing full-graph FMT map is used, with a product condition on
this precise current domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem frozenFocusMap_continuous_after_exception
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite) (c : A → VF M)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
    (hcdef : S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (c D).val)))
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hprod : ∀ D : A, CoordinateProductDomain C.carrier (vfOpenBall D.val) (c D) 0)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B)
    (u : Fin r → RVInfinity M)
    (hFibres : ∀ a : VF M, Continuous (fun b : Fin n → VF M => totalFocusFibre f u (Fin.cons a b)))
    (E : Set (Fin 1 → VF M)) (hEF : E.Finite)
    (hCover : ∀ a ∈ E, ∃ D : A, a 0 ∈ vfOpenBall D.val)
    (hCont : ContinuousOn (totalFocusFibre f u) {x | (fun _ : Fin 1 => x 0) ∉ E}) :
    Continuous (focusFibre (frozenFocusMap A c 0 hsep hAdef hcdef hprod f) u) := by
  have hg := vfFamilyFreeze_removes_discontinuities hv A hA c hsep
    (totalFocusFibre f u) hFibres E hEF hCover hCont
  convert (continuous_apply (0 : Fin 1)).comp (hg.comp continuous_subtype_val) using 1
  funext p
  let q := mixedFamilyFreeze A c (0 : Fin (n+1)) (p.val,u)
  have hq : q ∈ C.carrier := mixedFamilyFreeze_mapsTo A c 0 C.carrier hsep hprod p.property
  have hqval : q.1 = Fin.cons (vfFamilyFreeze A c (p.val 0)) (Fin.tail p.val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [q,mixedFamilyFreeze,Function.update_self,Fin.cons_zero]
    · simp only [q,mixedFamilyFreeze,Function.update_of_ne (Fin.succ_ne_zero j),Fin.cons_succ,Fin.tail]
  have hAt := congrFun (totalFocusFibre_at f u q.1 hq) 0
  change (f ⟨q,hq⟩).val 0 = totalFocusFibre f u
    (Fin.cons (vfFamilyFreeze A c (p.val 0)) (Fin.tail p.val)) 0
  exact hAt.symm.trans (congrArg (fun z => totalFocusFibre f u z 0) hqval)

theorem exists_finite_exception_for_focus_freezing
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hC : ∀ u, IsClopen (vfFibre C.carrier u))
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B)
    (hf : ∀ u a, Continuous (focusTailMap f u a)) :
    ∃ E : Set (Fin 1 → VF M), E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      ∀ (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite) (c : A → VF M)
        (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
          x ∈ OpenBallCodes.underlying E.val → D = E)
        (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
        (hcdef : S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (c D).val)))
        (hprod : ∀ D : A, CoordinateProductDomain C.carrier (vfOpenBall D.val) (c D) 0),
        (∀ a ∈ E, ∃ D : A, a 0 ∈ vfOpenBall D.val) →
        ∀ u, Continuous (focusFibre (frozenFocusMap A c 0 hsep hAdef hcdef hprod f) u) := by
  obtain ⟨E,hEF,hEdef,hCont⟩ := exists_uniform_focus_continuity_exception h00 hc hκ hs hsmall hv hC f hf
  refine ⟨E,hEF,hEdef,fun A hA c hsep hAdef hcdef hprod hCover u => ?_⟩
  exact frozenFocusMap_continuous_after_exception hv A hA c hsep hAdef hcdef hprod f u
    (fun a => totalFocusFibre_tail_continuous hv hC f u a (hf u a)) E hEF hCover (hCont u)

end DiamondIntegral.Section6.FMT
