import «section 6».UniformDomainFocusFreezing

/-! One original-base finite disc family repairs a finite collection
of scalar maps simultaneously. The same parameter substitution therefore
applies to forward maps, inverse maps and their graph indicators. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FMT
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {I : Type} [Finite I]

theorem exists_finite_family_continuity_exception
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hC : ∀ u,IsClopen (vfFibre C.carrier u))
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : I → Map C B)
    (hf : ∀ i u a,Continuous (focusTailMap (f i) u a)) :
    ∃ E : Set (Fin 1 → VF M),E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      ∀ i u,ContinuousOn (totalFocusFibre (f i) u) {x | (fun _ : Fin 1 => x 0) ∉ E} := by
  let H i := exists_uniform_focus_continuity_exception h00 hc hκ hs hsmall hv hC (f i) (hf i)
  let E₀ i := (H i).choose
  have hEF (i) : (E₀ i).Finite := (H i).choose_spec.1
  have hEDef (i) : S.Definable LRV (vfValues '' E₀ i) := (H i).choose_spec.2.1
  let E := ⋃ i,E₀ i
  have hE : E.Finite := Set.finite_iUnion hEF
  have hCodes : vfValues '' E=⋃ i,vfValues '' E₀ i := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨i,a,hi,rfl⟩
    · intro hz
      obtain ⟨i,a,ha,rfl⟩ := Set.mem_iUnion.mp hz
      exact ⟨a,Set.mem_iUnion.mpr ⟨i,ha⟩,rfl⟩
  have hDef : S.Definable LRV (vfValues '' E) := hCodes.symm ▸ Set.definable_iUnion_of_finite hEDef
  refine ⟨E,hE,hDef,fun i u => ((H i).choose_spec.2.2 u).mono ?_⟩
  intro x hx hxi
  exact hx (Set.mem_iUnion.mpr ⟨i,hxi⟩)

theorem exists_finite_family_focus_freezing_with_all_domains
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (δ : Gamma M) (hC : ∀ u,AlphaInvariant (fun _ => δ) (vfFibre C.carrier u))
    (s : VF M) (hs0 : s ≠ 0) (hsdef : S.Definable₁ LRV {s.val}) (hδs : δ.val ≤ vfValue s)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : I → Map C B)
    (hf : ∀ i u a,Continuous (focusTailMap (f i) u a)) :
    ∃ D : FocusFreezingData C,(∀ i u,Continuous (focusFibre (D.frozenMap (f i)) u)) ∧
      ∀ m t : ℕ,∀ P : Set (Mixed M m t),
        (∀ u,AlphaInvariant (fun _ => δ) (vfFibre P u)) → ∀ j : Fin m,∀ E : D.balls,
          CoordinateProductDomain P (vfOpenBall E.val) (D.centers E) j := by
  have hClopen : ∀ u,IsClopen (vfFibre C.carrier u) := fun u => (hC u).isClopen hv
  obtain ⟨E,hEF,hEdef,hCont⟩ := exists_finite_family_continuity_exception h00 hc hκ hs hsmall hv hClopen f hf
  let A := exceptionalOpenBalls E s hs0
  have hAF : A.Finite := exceptionalOpenBalls_finite E hEF s hs0
  have hAdef : S.Definable LRV (OpenBallCodes.pullback A) := exceptionalOpenBalls_definable E hEdef s hs0 hsdef
  have hsep := sameOpenRadius_separated A s (exceptionalOpenBalls_sameRadius hv E s hs0)
  obtain ⟨c,hcMem,hcDef⟩ := exceptionalOpenBalls_centers hc h00 hv E hEF hEdef s hs0 hsdef
  have hprod := exceptionalOpenBalls_product_domain hv C.carrier δ hC E s hs0 hδs c hcMem (0 : Fin (n+1))
  let D : FocusFreezingData C := ⟨A,hAF,c,hcMem,hsep,hAdef,hcDef,hprod⟩
  refine ⟨D,fun i u => ?_,fun m t P hP j => ?_⟩
  · exact frozenFocusMap_continuous_after_exception hv A hAF c hsep hAdef hcDef hprod (f i) u
      (fun a => totalFocusFibre_tail_continuous hv hClopen (f i) u a (hf i u a)) E hEF
      (exceptionalOpenBalls_cover E s hs0) (hCont i u)
  · exact exceptionalOpenBalls_product_domain hv P δ hP E s hs0 hδs c hcMem j

end DiamondIntegral.Section6.FMT
