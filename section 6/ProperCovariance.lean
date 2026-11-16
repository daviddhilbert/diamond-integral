import «section 6».OpenPartitions

/-! Definition 6.2 and Lemma 6.7 for actual definable mixed-sort maps.
The global image bounds and the full source/target tag base are explicit.
Continuity is imposed on the actual graph-fiber maps, never inferred
from the existence of partial derivatives. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

def NamedGammaTuple {k : ℕ} (T : Set M) (α : Fin k → Gamma M) : Prop :=
  ∀ i, T.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α i}}

def mixedMapRange (f : Map A B) : Set (Mixed M m s) := Set.range (fun p : A => (f p).val)

structure ProperCovariant (f : Map A B) : Prop where
  sourceVFBounded : VFBounded A.carrier
  imageVFBounded : VFBounded (mixedMapRange f)
  sourceRVBounded : RVSupportDoublyBounded A.carrier
  imageRVBounded : RVSupportDoublyBounded (mixedMapRange f)
  radii : ∀ u : Fin r → RVInfinity M, ∀ v : Fin s → RVInfinity M,
    ∃ α : Fin n → Gamma M, ∃ β : Fin m → Gamma M,
      NamedGammaTuple (graphFibreBase S u v) α ∧
      NamedGammaTuple (graphFibreBase S u v) β ∧
      AlphaInvariant α (graphFibreSource f u v) ∧
      AlphaInvariant β (graphFibreRange f u v) ∧
      AlphaBetaCovariant α β (graphFibreSource f u v) (graphFibreMap f u v)

def ContinuousOnGraphFibres {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (f : Map A B) : Prop := ∀ u v, ContinuousOn (graphFibreMap f u v) (graphFibreSource f u v)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem properCovariant_of_clopen_ranges
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier)
    (hcont : ContinuousOnGraphFibres f)
    (hdom : ∀ u v, IsOpen (graphFibreSource f u v))
    (hran : ∀ u v, IsClopen (graphFibreRange f u v)) : ProperCovariant f := by
  have hsub : mixedMapRange f ⊆ B.carrier := by
    rintro _ ⟨p,rfl⟩
    exact (f p).property
  refine ⟨hA.vfBounded,hB.vfBounded.mono hsub,hA.rvBounded,hB.rvBounded.mono hsub,fun u v => ?_⟩
  have hDb : ∃ γ : Gamma M, ∀ x ∈ graphFibreSource f u v, ∀ i, γ.val ≤ vfValue (x i) := by
    obtain ⟨γ,hγ⟩ := hA.vfBounded
    exact ⟨γ,fun x hx i => hγ (x,u) (graphFibreSource_subset f u v hx) i⟩
  have hEb : ∃ γ : Gamma M, ∀ x ∈ graphFibreRange f u v, ∀ i, γ.val ≤ vfValue (x i) := by
    obtain ⟨γ,hγ⟩ := hB.vfBounded
    exact ⟨γ,fun x hx i => hγ (x,v) (graphFibreRange_subset f u v hx) i⟩
  obtain ⟨β,hβdef,hβ⟩ := clopen_has_named_invariant_radius h00 hc hκ hs hv
    (graphFibreRange f u v) (graphFibreRange_definable f u v) (hran u v) hEb
  obtain ⟨α,hαdef,hα,hcov⟩ := continuous_named_uniform_covariance h00 hc hκ hs hv
    (graphFibreSource f u v) (graphFibreSource_definable f u v)
    (graphFibreSource_isClopen hv f hA hdom u v) hDb (graphFibreMap f u v)
    (graphFibreMap_definable f u v) (hcont u v) β hβdef
  exact ⟨fun _ => α,fun _ => β,fun _ => hαdef,fun _ => hβdef,hα,hβ,hcov⟩

/-- Lemma 6.7, including the weaker open-range hypothesis for bijections.
All source graph fibers are open and all graph-fiber maps are continuous. -/
theorem lemma_6_7
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hf : Function.Surjective f)
    (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier)
    (hcont : ContinuousOnGraphFibres f) (hdom : ∀ u v, IsOpen (graphFibreSource f u v)) :
    ((∀ u v, IsClopen (graphFibreRange f u v)) → ProperCovariant f) ∧
      (Function.Injective f → (∀ u v, IsOpen (graphFibreRange f u v)) → ProperCovariant f) := by
  constructor
  · exact properCovariant_of_clopen_ranges h00 hc hκ hs hv f hA hB hcont hdom
  · intro hinj hopen
    exact properCovariant_of_clopen_ranges h00 hc hκ hs hv f hA hB hcont hdom
      (graphFibreRange_isClopen_of_bijective hv f ⟨hinj,hf⟩ hB hopen)

end DiamondIntegral.Section6
