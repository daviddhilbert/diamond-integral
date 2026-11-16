import «section 6».MeasuredRVChainExtensions

/-! Canonical global intermediate objects: use the target structural
volume on a chosen label piece and the old source volume elsewhere.
Their actual Gamma forms retain the original total weight. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvIso_restricted_map_injective {U V : RVObject (M := M) S n} (e : U ≅ V)
    (D : DefSet (rawRVSpace (M := M) U.arity) S) (hD : D.carrier ⊆ U.domain.carrier) :
    Function.Injective (e.hom.map.restrict hD) := by
  intro u v he
  have h := (rvIso_map_bijective e).1 he
  exact Subtype.ext (congrArg (fun x : U.domain => x.val) h)

def measuredRVLabelReplacement (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier) :
    MeasuredRVObject (M := M) S n :=
  measuredRVVolumeExtension hc U V D (e.iso.hom.map.restrict hD) (rvIso_restricted_map_injective e.iso D hD)

theorem measuredRVLabelReplacement_of_mem (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (u : U.object.domain) (hu : u.val ∈ D.carrier) :
    (measuredRVLabelReplacement hc e D hD).object.value u = V.object.value (e.iso.hom.map u) :=
  measuredRVVolumeExtension_of_mem hc U V D (e.iso.hom.map.restrict hD)
    (rvIso_restricted_map_injective e.iso D hD) u hu

theorem measuredRVLabelReplacement_of_not_mem (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (u : U.object.domain) (hu : u.val ∉ D.carrier) :
    (measuredRVLabelReplacement hc e D hD).object.value u = U.object.value u :=
  measuredRVVolumeExtension_of_not_mem hc U V D (e.iso.hom.map.restrict hD)
    (rvIso_restricted_map_injective e.iso D hD) u hu

theorem measuredRVLabelReplacement_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (u : U.object.domain) : (measuredRVLabelReplacement hc e D hD).totalWeight u = U.totalWeight u :=
  measuredRVVolumeExtension_totalWeight hc U V D (e.iso.hom.map.restrict hD)
    (rvIso_restricted_map_injective e.iso D hD) u

theorem measuredRVLabelReplacement_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (hU : U.doublyBounded) (hV : V.doublyBounded) : (measuredRVLabelReplacement hc e D hD).doublyBounded :=
  measuredRVVolumeExtension_doublyBounded hc U V D (e.iso.hom.map.restrict hD)
    (rvIso_restricted_map_injective e.iso D hD) hU hV

def measuredRVLabelReplacementInitialIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (hEmpty : ∀ u : U.object.domain, u.val ∉ D.carrier) :
    MeasuredRVIso U (measuredRVLabelReplacement hc e D hD) where
  iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id
    (fun u => measuredRVLabelReplacement_of_not_mem hc e D hD u (hEmpty u))
  balance u := (measuredRVLabelReplacement_totalWeight hc e D hD u).symm

def measuredRVLabelReplacementFinalIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (hCover : ∀ u : U.object.domain, u.val ∈ D.carrier) :
    MeasuredRVIso (measuredRVLabelReplacement hc e D hD) V where
  iso := rvIsoOfVolumePreservingBijection e.iso.hom.map (rvIso_map_bijective e.iso)
    (fun u => (measuredRVLabelReplacement_of_mem hc e D hD u (hCover u)).symm)
  balance u := (measuredRVLabelReplacement_totalWeight hc e D hD u).trans (e.balance u)

end DiamondIntegral.Section6
