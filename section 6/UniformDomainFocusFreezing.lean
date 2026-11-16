import «section 6».ProtectedFocusFreezing

/-! One continuity-repair disc family protects every domain invariant
at the chosen radius, independently of its VF and RV arities. This
includes the unary parameter domain together with current joint pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FMT
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_continuous_focus_freezing_with_all_domains
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (δ : Gamma M) (hC : ∀ u,AlphaInvariant (fun _ => δ) (vfFibre C.carrier u))
    (s : VF M) (hs0 : s ≠ 0) (hsdef : S.Definable₁ LRV {s.val}) (hδs : δ.val ≤ vfValue s)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B)
    (hf : ∀ u a,Continuous (focusTailMap f u a)) :
    ∃ D : FocusFreezingData C,(∀ u,Continuous (focusFibre (D.frozenMap f) u)) ∧
      ∀ m t : ℕ,∀ P : Set (Mixed M m t),
        (∀ u,AlphaInvariant (fun _ => δ) (vfFibre P u)) → ∀ j : Fin m,∀ E : D.balls,
          CoordinateProductDomain P (vfOpenBall E.val) (D.centers E) j := by
  have hClopen : ∀ u,IsClopen (vfFibre C.carrier u) := fun u => (hC u).isClopen hv
  obtain ⟨E,hEF,hEdef,hCont⟩ := exists_uniform_focus_continuity_exception h00 hc hκ hs hsmall hv hClopen f hf
  let A := exceptionalOpenBalls E s hs0
  have hAF : A.Finite := exceptionalOpenBalls_finite E hEF s hs0
  have hAdef : S.Definable LRV (OpenBallCodes.pullback A) := exceptionalOpenBalls_definable E hEdef s hs0 hsdef
  have hsep := sameOpenRadius_separated A s (exceptionalOpenBalls_sameRadius hv E s hs0)
  obtain ⟨c,hcMem,hcDef⟩ := exceptionalOpenBalls_centers hc h00 hv E hEF hEdef s hs0 hsdef
  have hprod := exceptionalOpenBalls_product_domain hv C.carrier δ hC E s hs0 hδs c hcMem (0 : Fin (n+1))
  let D : FocusFreezingData C := ⟨A,hAF,c,hcMem,hsep,hAdef,hcDef,hprod⟩
  refine ⟨D,fun u => ?_,fun m t P hP j => ?_⟩
  · exact frozenFocusMap_continuous_after_exception hv A hAF c hsep hAdef hcDef hprod f u
      (fun a => totalFocusFibre_tail_continuous hv hClopen f u a (hf u a)) E hEF
      (exceptionalOpenBalls_cover E s hs0) (hCont u)
  · exact exceptionalOpenBalls_product_domain hv P δ hP E s hs0 hδs c hcMem j

end DiamondIntegral.Section6.FMT
