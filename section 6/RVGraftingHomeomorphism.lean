import «section 6».RVGrafting

/-! Grafting proper invariant labels is a proper covariant homeomorphism
with total VF derivative equal to the identity at every point. This is
the deferred-base grafting step used by standard contractions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r q : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {D : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem graft_continuous (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D) :
    ContinuousOnGraphFibres (graft hc τ) := by
  intro u v
  apply continuous_id.continuousOn.congr
  intro a ha
  obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph (graft hc τ) u v ha
  exact (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)

theorem graft_vfChart (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (τ : Map A D) (hτ : ProperCovariant τ) (p : A) : IsVFChartAt (graft hc τ) p id := by
  let u := p.val.2
  let v := (graft hc τ p).val.2
  have hp : p.val.1 ∈ graphFibreSource (graft hc τ) u v := ⟨p.val.1,p,rfl,rfl⟩
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((graft_source_clopen hc hv τ hτ u v).isOpen.mem_nhds hp)
  refine ⟨ρ,fun x hx => ?_⟩
  obtain ⟨b,p',hp',hgp'⟩ := hρ hx
  have hxA : (x,u) ∈ A.carrier := hp' ▸ p'.property
  have hPoint : p' = (⟨(x,u),hxA⟩ : A) := Subtype.ext hp'
  have hb : b = x := (congrArg Prod.fst hgp').symm.trans (congrArg Prod.fst hp')
  refine ⟨hxA,?_⟩
  change (graft hc τ ⟨(x,u),hxA⟩).val = (x,v)
  rw [← hPoint]
  simpa only [hb] using hgp'

theorem graft_unit_derivative (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (τ : Map A D) (hτ : ProperCovariant τ) (p : A) : HasMixedUnitDerivativeAt (graft hc τ) p := by
  obtain ⟨L,hL,hdet⟩ := hasUnitJacobianAt_id p.val.1
  exact ⟨L,⟨id,graft_vfChart hc hv τ hτ p,(hasDerivativeAt_iff_companion _ _ _).mp hL⟩,hdet⟩

theorem graft_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (τ : Map A D) (hA : ProperInvariant S A.carrier) (hτ : ProperCovariant τ) :
    ProperInvariant S (graftMap hc τ).image.carrier := by
  apply (lemma_6_5 h00 hc hκ hs hv _ (graftMap hc τ).image.definable
    (graft_vfBounded hc τ hA.vfBounded) (graft_rvBounded hc τ hA.rvBounded hτ.imageRVBounded)).mpr
  intro v
  rw [graft_image_fibre,graft_range_eq_source]
  exact graft_source_clopen hc hv τ hτ _ _

theorem graft_properCovariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (τ : Map A D) (hA : ProperInvariant S A.carrier) (hτ : ProperCovariant τ) : ProperCovariant (graft hc τ) :=
  properCovariant_of_clopen_ranges h00 hc hκ hs hv (graft hc τ) hA
    (graft_properInvariant h00 hc hκ hs hv τ hA hτ) (graft_continuous hc τ)
    (fun u v => (graft_source_clopen hc hv τ hτ u v).isOpen)
    (fun u v => (graft_range_eq_source hc τ u v).symm ▸ graft_source_clopen hc hv τ hτ u v)

theorem graft_properHomeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (τ : Map A D) (hA : ProperInvariant S A.carrier) (hτ : ProperCovariant τ) :
    ProperCovariantHomeomorphism (graft hc τ) :=
  properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ (graft hc τ)
    (graft_properCovariant h00 hc hκ hs hv τ hA hτ) (graft_bijective hc τ) (graft_continuous hc τ)

end DiamondIntegral.Section6
