import «section 6».InverseFibres
import Section4.Products

/-! Restriction to a proper invariant source subset. The range on a fixed
graph fiber is a clopen inverse image under the continuous inverse fiber. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A C : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem graphFibre_restrict_iff (f : Map A B) (hCA : C.carrier ⊆ A.carrier)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a : Fin n → VF M) (b : Fin m → VF M) :
    graphFibre (f.restrict hCA) u v a b ↔ (a,u) ∈ C.carrier ∧ graphFibre f u v a b := by
  constructor
  · rintro ⟨p,hp,hfp⟩
    exact ⟨hp ▸ p.property,⟨p.val,hCA p.property⟩,hp,hfp⟩
  · rintro ⟨ha,p,hp,hfp⟩
    let q : C := ⟨(a,u),ha⟩
    have he : (⟨q.val,hCA q.property⟩ : A) = p := Subtype.ext hp.symm
    refine ⟨q,rfl,?_⟩
    change (f ⟨q.val,hCA q.property⟩).val = (b,v)
    rw [he]
    exact hfp

theorem graphFibreSource_restrict (f : Map A B) (hCA : C.carrier ⊆ A.carrier)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (f.restrict hCA) u v = vfFibre C.carrier u ∩ graphFibreSource f u v := by
  ext a
  constructor
  · rintro ⟨b,hb⟩
    have h := (graphFibre_restrict_iff f hCA u v a b).mp hb
    exact ⟨h.1,b,h.2⟩
  · rintro ⟨ha,b,hb⟩
    exact ⟨b,(graphFibre_restrict_iff f hCA u v a b).mpr ⟨ha,hb⟩⟩

theorem graphFibreMap_restrict_eqOn (f : Map A B) (hCA : C.carrier ⊆ A.carrier)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Set.EqOn (graphFibreMap (f.restrict hCA) u v) (graphFibreMap f u v)
      (graphFibreSource (f.restrict hCA) u v) := by
  intro a ha
  have hG := ((graphFibre_restrict_iff f hCA u v _ _).mp
    (graphFibreMap_graph (f.restrict hCA) u v ha)).2
  have haD : a ∈ graphFibreSource f u v := ((graphFibreSource_restrict f hCA u v) ▸ ha).2
  exact graphFibre_functional f u v hG (graphFibreMap_graph f u v haD)

theorem graphFibreMap_inverse_eq_of_graph (f : Map A B) (hf : Function.Bijective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    {a : Fin n → VF M} {b : Fin m → VF M} (hab : graphFibre f u v a b) :
    graphFibreMap (f.inverse hf) v u b = a := by
  have hbg : b ∈ graphFibreSource (f.inverse hf) v u :=
    ⟨a,(inverse_graphFibre_iff f hf u v a b).mpr hab⟩
  exact graphFibre_functional (f.inverse hf) v u
    (graphFibreMap_graph (f.inverse hf) v u hbg) ((inverse_graphFibre_iff f hf u v a b).mpr hab)

theorem graphFibreRange_restrict (f : Map A B) (hf : Function.Bijective f)
    (hCA : C.carrier ⊆ A.carrier) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange (f.restrict hCA) u v = graphFibreRange f u v ∩
      graphFibreMap (f.inverse hf) v u ⁻¹' vfFibre C.carrier u := by
  ext b
  constructor
  · rintro ⟨a,hab⟩
    obtain ⟨ha,hG⟩ := (graphFibre_restrict_iff f hCA u v a b).mp hab
    refine ⟨⟨a,hG⟩,?_⟩
    change graphFibreMap (f.inverse hf) v u b ∈ vfFibre C.carrier u
    rw [graphFibreMap_inverse_eq_of_graph f hf u v hG]
    exact ha
  · rintro ⟨hb,hC⟩
    have hbg : b ∈ graphFibreSource (f.inverse hf) v u := (inverse_graphFibreSource f hf u v).symm ▸ hb
    have hG := (inverse_graphFibre_iff f hf u v _ _).mp (graphFibreMap_graph (f.inverse hf) v u hbg)
    exact ⟨_,(graphFibre_restrict_iff f hCA u v _ _).mpr ⟨hC,hG⟩⟩

theorem restrict_toImage_bijective (f : Map A B) (hf : Function.Injective f)
    (hCA : C.carrier ⊆ A.carrier) : Function.Bijective (f.restrict hCA).toImage := by
  constructor
  · intro a b he
    have hval := congrArg (fun x : (f.restrict hCA).image => x.val) he
    have he' : f ⟨a.val,hCA a.property⟩ = f ⟨b.val,hCA b.property⟩ :=
      Subtype.ext hval
    exact Subtype.ext (congrArg (fun x : A => x.val) (hf he'))
  · rintro ⟨_,a,rfl⟩
    exact ⟨a,rfl⟩

theorem ProperCovariant.toImage {f : Map A B} (hcov : ProperCovariant f) :
    ProperCovariant f.toImage :=
  ⟨hcov.sourceVFBounded,hcov.imageVFBounded,hcov.sourceRVBounded,hcov.imageRVBounded,hcov.radii⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousOnGraphFibres_restrict {f : Map A B} (hcont : ContinuousOnGraphFibres f)
    (hCA : C.carrier ⊆ A.carrier) : ContinuousOnGraphFibres (f.restrict hCA) := by
  intro u v
  have hsub : graphFibreSource (f.restrict hCA) u v ⊆ graphFibreSource f u v := by
    rw [graphFibreSource_restrict f hCA u v]
    exact Set.inter_subset_right
  exact ((hcont u v).mono hsub).congr (fun a ha => graphFibreMap_restrict_eqOn f hCA u v ha)

theorem ProperCovariant.restrict
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} (hcov : ProperCovariant f) (hf : Function.Bijective f)
    (hcont : ContinuousOnGraphFibres f) (hCA : C.carrier ⊆ A.carrier)
    (hC : ProperInvariant S C.carrier) : ProperCovariant (f.restrict hCA) := by
  have hB := hcov.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hf.surjective
  have hInv := hcov.inverse_continuous h00 hc hκ hs hv hf hcont
  apply properCovariant_of_clopen_ranges h00 hc hκ hs hv (f.restrict hCA) hC hB
    (continuousOnGraphFibres_restrict hcont hCA)
  · intro u v
    rw [graphFibreSource_restrict f hCA u v]
    obtain ⟨_,_,_,_,hD,_,_⟩ := hcov.radii u v
    exact (hC.clopen_fibres hv u).isOpen.inter (hD.isOpen hv)
  · intro u v
    rw [graphFibreRange_restrict f hf hCA u v]
    obtain ⟨_,_,_,_,_,hE,_⟩ := hcov.radii u v
    have hcontInv : ContinuousOn (graphFibreMap (f.inverse hf) v u) (graphFibreRange f u v) :=
      (inverse_graphFibreSource f hf u v) ▸ hInv v u
    exact ⟨hcontInv.preimage_isClosed_of_isClosed (hE.isClopen hv).isClosed
      (hC.clopen_fibres hv u).isClosed,
      hcontInv.isOpen_inter_preimage (hE.isOpen hv) (hC.clopen_fibres hv u).isOpen⟩

end DiamondIntegral.Section6
