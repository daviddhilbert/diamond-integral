import «section 6».InvariantOfCovariance
import «section 2».ClosedBoundedHomeomorphism
import Section4.DefinableCategory

/-! Inverse graph fibers and continuity. Closed bounded definable graph
domains give actual homeomorphisms by the checked Corollary 2.49. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem inverse_graph_iff (f : Map A B) (hf : Function.Bijective f)
    (x : Mixed M n r) (y : Mixed M m s) : (f.inverse hf).graph y x ↔ f.graph x y := by
  constructor
  · rintro ⟨q,hq,hgq⟩
    exact ⟨f.inverse hf q,hgq,by rw [Map.apply_inverse]; exact hq⟩
  · rintro ⟨p,hp,hfp⟩
    exact ⟨f p,hfp,by rw [Map.inverse_apply]; exact hp⟩

theorem inverse_graphFibre_iff (f : Map A B) (hf : Function.Bijective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a : Fin n → VF M) (b : Fin m → VF M) :
    graphFibre (f.inverse hf) v u b a ↔ graphFibre f u v a b :=
  inverse_graph_iff f hf (a,u) (b,v)

theorem inverse_graphFibreSource (f : Map A B) (hf : Function.Bijective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (f.inverse hf) v u = graphFibreRange f u v := by
  ext b
  exact exists_congr (fun a => inverse_graphFibre_iff f hf u v a b)

theorem inverse_graphFibreRange (f : Map A B) (hf : Function.Bijective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange (f.inverse hf) v u = graphFibreSource f u v := by
  ext a
  exact exists_congr (fun b => inverse_graphFibre_iff f hf u v a b)

theorem graphFibreMap_injOn (f : Map A B) (hf : Function.Injective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Set.InjOn (graphFibreMap f u v) (graphFibreSource f u v) := by
  intro a ha b hb hab
  obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph f u v ha
  obtain ⟨q,hq,hfq⟩ := graphFibreMap_graph f u v hb
  have hout : (graphFibreMap f u v a,v) = (graphFibreMap f u v b,v) :=
    congrArg (fun x => (x,v)) hab
  have he : p = q := hf (Subtype.ext (hfp.trans (hout.trans hfq.symm)))
  exact congrArg Prod.fst (hp.symm.trans (he ▸ hq))

theorem graphFibreMap_inverse_mapsTo (f : Map A B) (hf : Function.Bijective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Set.MapsTo (graphFibreMap (f.inverse hf) v u) (graphFibreRange f u v) (graphFibreSource f u v) := by
  intro b hb
  have hbg : b ∈ graphFibreSource (f.inverse hf) v u := (inverse_graphFibreSource f hf u v).symm ▸ hb
  have hg := graphFibreMap_graph (f.inverse hf) v u hbg
  exact ⟨b,(inverse_graphFibre_iff f hf u v _ _).mp hg⟩

theorem graphFibreMap_apply_inverse (f : Map A B) (hf : Function.Bijective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    {b : Fin m → VF M} (hb : b ∈ graphFibreRange f u v) :
    graphFibreMap f u v (graphFibreMap (f.inverse hf) v u b) = b := by
  have hbg : b ∈ graphFibreSource (f.inverse hf) v u := (inverse_graphFibreSource f hf u v).symm ▸ hb
  have hg := (inverse_graphFibre_iff f hf u v _ _).mp (graphFibreMap_graph (f.inverse hf) v u hbg)
  exact graphFibre_functional f u v
    (graphFibreMap_graph f u v (graphFibreMap_inverse_mapsTo f hf u v hb)) hg

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem ProperCovariant.inverse_continuous
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {f : Map A B} (hcov : ProperCovariant f) (hf : Function.Bijective f)
    (hcont : ContinuousOnGraphFibres f) : ContinuousOnGraphFibres (f.inverse hf) := by
  intro v u
  rw [inverse_graphFibreSource f hf u v]
  let D := graphFibreSource f u v
  let E := graphFibreRange f u v
  let F := graphFibreMap f u v
  obtain ⟨α,β,_,_,hD,_,_⟩ := hcov.radii u v
  have hb : ∃ γ : Gamma M, ∀ x ∈ D, ∀ i, γ.val ≤ vfValue (x i) := by
    obtain ⟨γ,hγ⟩ := hcov.sourceVFBounded
    exact ⟨γ,fun x hx i => hγ (x,u) (graphFibreSource_subset f u v hx) i⟩
  obtain ⟨H,hH⟩ := corollary_2_49 h00 hc hκ hs hv D (graphFibreSource_definable f u v)
    (hD.isClopen hv).isClosed hb F (graphFibreMap_definable f u v) (hcont u v)
    (graphFibreMap_injOn f hf.injective u v)
  let e : E ≃ₜ (F '' D) := Homeomorph.setCongr (graphFibreRange_eq_image f u v)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hcontinuous : Continuous (fun b : E => (H.symm (e b)).val) :=
    continuous_subtype_val.comp (H.symm.continuous.comp e.continuous)
  convert hcontinuous using 1
  funext b
  apply graphFibreMap_injOn f hf.injective u v
    (graphFibreMap_inverse_mapsTo f hf u v b.property) (H.symm (e b)).property
  have hright : F (H.symm (e b)).val = b.val :=
    (hH (H.symm (e b))).symm.trans (congrArg Subtype.val (H.apply_symm_apply (e b)))
  exact (graphFibreMap_apply_inverse f hf u v b.property).trans hright.symm

theorem ProperCovariant.inverse_properCovariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} (hcov : ProperCovariant f) (hf : Function.Bijective f)
    (hcont : ContinuousOnGraphFibres f) : ProperCovariant (f.inverse hf) := by
  have hA := hcov.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  have hB := hcov.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hf.surjective
  apply properCovariant_of_clopen_ranges h00 hc hκ hs hv (f.inverse hf) hB hA
    (hcov.inverse_continuous h00 hc hκ hs hv hf hcont)
  · intro v u
    rw [inverse_graphFibreSource f hf u v]
    obtain ⟨_,_,_,_,_,hran,_⟩ := hcov.radii u v
    exact hran.isOpen hv
  · intro v u
    rw [inverse_graphFibreRange f hf u v]
    obtain ⟨_,_,_,_,hdom,_,_⟩ := hcov.radii u v
    exact hdom.isClopen hv

end DiamondIntegral.Section6
