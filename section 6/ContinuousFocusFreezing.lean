import «section 6».ExceptionalBallDomains

/-! Existence of the full original-base FMT continuity repair. Finite
exceptions, actual discs, definable centers and the current-domain
product condition are constructed; only continuous tail fibers enter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

structure FocusFreezingData (C : DefSet (rawMixedSpace (M := M) (n+1) r) S) where
  balls : Set (OpenBallCodes.OpenBall M)
  finite : balls.Finite
  centers : balls → VF M
  center_mem : ∀ D, centers D ∈ vfOpenBall D.val
  separated : ∀ D E : balls, ∀ x, x ∈ OpenBallCodes.underlying D.val →
    x ∈ OpenBallCodes.underlying E.val → D = E
  balls_definable : S.Definable LRV (OpenBallCodes.pullback balls)
  centers_definable : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val))
  product_domain : ∀ D : balls, CoordinateProductDomain C.carrier (vfOpenBall D.val) (centers D) 0

def FocusFreezingData.frozenMap {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (D : FocusFreezingData C) {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B) : Map C B :=
  frozenFocusMap D.balls D.centers 0 D.separated D.balls_definable D.centers_definable D.product_domain f

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_continuous_focus_freezing_with_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (δ : Gamma M) (hC : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre C.carrier u))
    (s : VF M) (hs0 : s ≠ 0) (hsdef : S.Definable₁ LRV {s.val}) (hδs : δ.val ≤ vfValue s)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B)
    (hf : ∀ u a, Continuous (focusTailMap f u a)) :
    ∃ D : FocusFreezingData C, ∀ u, Continuous (focusFibre (D.frozenMap f) u) := by
  have hClopen : ∀ u, IsClopen (vfFibre C.carrier u) := fun u => (hC u).isClopen hv
  obtain ⟨E,hEF,hEdef,hCont⟩ := exists_uniform_focus_continuity_exception h00 hc hκ hs hsmall hv hClopen f hf
  let A := exceptionalOpenBalls E s hs0
  have hAF : A.Finite := exceptionalOpenBalls_finite E hEF s hs0
  have hAdef : S.Definable LRV (OpenBallCodes.pullback A) := exceptionalOpenBalls_definable E hEdef s hs0 hsdef
  have hsep := sameOpenRadius_separated A s (exceptionalOpenBalls_sameRadius hv E s hs0)
  obtain ⟨c,hcMem,hcDef⟩ := exceptionalOpenBalls_centers hc h00 hv E hEF hEdef s hs0 hsdef
  have hprod := exceptionalOpenBalls_product_domain hv C.carrier δ hC E s hs0 hδs c hcMem (0 : Fin (n+1))
  let D : FocusFreezingData C := ⟨A,hAF,c,hcMem,hsep,hAdef,hcDef,hprod⟩
  refine ⟨D,fun u => ?_⟩
  exact frozenFocusMap_continuous_after_exception hv A hAF c hsep hAdef hcDef hprod f u
    (fun a => totalFocusFibre_tail_continuous hv hClopen f u a (hf u a)) E hEF
    (exceptionalOpenBalls_cover E s hs0) (hCont u)

theorem exists_continuous_focus_freezing
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S} (hC : ProperInvariant S C.carrier)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B)
    (hf : ∀ u a, Continuous (focusTailMap f u a)) :
    ∃ D : FocusFreezingData C, ∀ u, Continuous (focusFibre (D.frozenMap f) u) := by
  obtain ⟨δ,hδdef,hδ0,hδ⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hC
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ0 hδdef
  exact exists_continuous_focus_freezing_with_radius h00 hc hκ hs hsmall hv δ hδ s hs0 hsdef hδs.le f hf

end DiamondIntegral.Section6.FMT
