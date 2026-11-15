import IntegrationSection5.RVProjectionNormalization
import IntegrationSection5.GammaRVUnion
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {k : ℕ}
local notation "restrictRV" => @SpecialTransformations.Section4.RVObject.restrict M (@CanonicalStructure.normalize M sM) S k
local notation "unionSubsetRV" => @SpecialTransformations.Section4.rvUnionSubset M (@CanonicalStructure.normalize M sM) S k

def gammaRVUnionCoverIso (U : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k)
    (A0 A1 : PresentedSet (rawRVSpace (M := M) (rvObjectArity U)) S)
    (hA0 : carrier A0 ⊆ carrier (rvObjectDomain U)) (hA1 : carrier A1 ⊆ carrier (rvObjectDomain U))
    (hCover : carrier (normalizedRVUnionSet A0 A1) = carrier (rvObjectDomain U))
    (hU : GammaSetDefinable G {p : Point (M := M) 0 (rvObjectArity U) | p.2 ∈ carrier (rvObjectDomain U)}) :
    GammaRVIso G (restrictRV U (normalizedRVUnionSet A0 A1) (unionSubsetRV U A0 A1 hA0 hA1)) U := by
  let f : Map (normalizedRVUnionSet A0 A1) (rvObjectDomain U) := Map.inclusion (unionSubsetRV U A0 A1 hA0 hA1)
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => Subtype.ext (congrArg (fun z : rvObjectDomain U => z.val) h),?_⟩
    intro p
    exact ⟨⟨p.val,(Set.ext_iff.mp hCover p.val).mpr p.property⟩,rfl⟩
  apply GammaRVIso.ofVolumePreserving f hf (fun _ => rfl)
  apply gamma_rvMap_identity_values f (fun _ => rfl)
  have he : {p : Point (M := M) 0 (rvObjectArity U) | p.2 ∈ carrier (normalizedRVUnionSet A0 A1)} =
      {p : Point (M := M) 0 (rvObjectArity U) | p.2 ∈ carrier (rvObjectDomain U)} := by rw [hCover]
  exact he.symm ▸ hU

def gammaRVPartitionIso
    (U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k)
    (A0 A1 : PresentedSet (rawRVSpace (M := M) (rvObjectArity U)) S)
    (B0 B1 : PresentedSet (rawRVSpace (M := M) (rvObjectArity V)) S)
    (hA0 : carrier A0 ⊆ carrier (rvObjectDomain U)) (hA1 : carrier A1 ⊆ carrier (rvObjectDomain U))
    (hB0 : carrier B0 ⊆ carrier (rvObjectDomain V)) (hB1 : carrier B1 ⊆ carrier (rvObjectDomain V))
    (hdA : Disjoint (carrier A0) (carrier A1)) (hdB : Disjoint (carrier B0) (carrier B1))
    (hCoverA : carrier (normalizedRVUnionSet A0 A1) = carrier (rvObjectDomain U))
    (hCoverB : carrier (normalizedRVUnionSet B0 B1) = carrier (rvObjectDomain V))
    (hU : GammaSetDefinable G {p : Point (M := M) 0 (rvObjectArity U) | p.2 ∈ carrier (rvObjectDomain U)})
    (hV : GammaSetDefinable G {p : Point (M := M) 0 (rvObjectArity V) | p.2 ∈ carrier (rvObjectDomain V)})
    (e0 : GammaRVIso G (restrictRV U A0 hA0) (restrictRV V B0 hB0))
    (e1 : GammaRVIso G (restrictRV U A1 hA1) (restrictRV V B1 hB1)) : GammaRVIso G U V :=
  (gammaRVUnionCoverIso U A0 A1 hA0 hA1 hCoverA hU).symm.trans
    ((gammaRVUnionIso U V A0 A1 B0 B1 hA0 hA1 hB0 hB1 hdA hdB e0 e1).trans
      (gammaRVUnionCoverIso V B0 B1 hB0 hB1 hCoverB hV))

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {a k : ℕ}
theorem selectedVolumeObject_restrict (A B : PresentedSet (rawRVSpace (M := M) a) S)
    (ρ : Fin k → Fin a) (h : carrier B ⊆ carrier A) :
    @SpecialTransformations.Section4.RVObject.restrict M (@CanonicalStructure.normalize M sM) S k
      (selectedVolumeObject A ρ) B h = selectedVolumeObject B ρ := by
  rfl
end IntegrationInACVF.Section5
