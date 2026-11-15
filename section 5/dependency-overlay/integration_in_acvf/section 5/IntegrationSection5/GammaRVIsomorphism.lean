import IntegrationSection5.GammaRVGraphs
import Section4.RVReindexing

/-! Actual RV-category isomorphisms equipped with full original-Gamma
graphs in both directions. Certificates are preserved by composition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {k : ℕ}

def rvIsoHomMap
    {U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k}
    (e : U ≅ V) : Map (rvObjectDomain U) (rvObjectDomain V) :=
  @SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S k U V e.hom

def rvIsoInvMap
    {U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k}
    (e : U ≅ V) : Map (rvObjectDomain V) (rvObjectDomain U) :=
  @SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S k V U e.inv

structure GammaRVIso (G : GammaParameters.Base (M := M))
    (U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k) where
  iso : U ≅ V
  hom_graph : GammaGraphDefinable G (rvMapGraph (rvIsoHomMap iso))
  inv_graph : GammaGraphDefinable G (rvMapGraph (rvIsoInvMap iso))

namespace GammaRVIso
variable {U V W : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k}

def symm (e : GammaRVIso G U V) : GammaRVIso G V U := ⟨e.iso.symm,e.inv_graph,e.hom_graph⟩

def trans (e : GammaRVIso G U V) (f : GammaRVIso G V W) : GammaRVIso G U W :=
  ⟨e.iso.trans f.iso,gamma_rvMap_comp (rvIsoHomMap e.iso) (rvIsoHomMap f.iso) e.hom_graph f.hom_graph,
    gamma_rvMap_comp (rvIsoInvMap f.iso) (rvIsoInvMap e.iso) f.inv_graph e.inv_graph⟩

def ofVolumePreserving (f : Map (rvObjectDomain U) (rvObjectDomain V)) (hf : Function.Bijective f)
    (hvol : ∀ a : rvObjectDomain U, (rvObjectVolume V (f a)).val = (rvObjectVolume U a).val)
    (hG : GammaGraphDefinable G (rvMapGraph f)) : GammaRVIso G U V :=
  ⟨@SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection M
      (@CanonicalStructure.normalize M sM) S k U V f hf hvol,
    hG,gamma_rvMap_inverse f hf hG⟩

def reindexVolume (U : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k)
    (σ : Equiv.Perm (Fin k))
    (hU : GammaSetDefinable G {p : Point (M := M) 0 (rvObjectArity U) | p.2 ∈ carrier (rvObjectDomain U)}) :
    GammaRVIso G U (@SpecialTransformations.Section4.RVObject.reindexVolume M
      (@CanonicalStructure.normalize M sM) S k k U σ) := by
  let e := @SpecialTransformations.Section4.rvReindexVolumeIso M
    (@CanonicalStructure.normalize M sM) S k U σ
  have hId : GammaGraphDefinable G (rvMapGraph (Map.id (rvObjectDomain U))) :=
    gamma_rvMap_identity_values _ (fun _ => rfl) hU
  exact ⟨e,hId,gamma_rvMap_inverse (Map.id (rvObjectDomain U)) Function.bijective_id hId⟩

end GammaRVIso
end IntegrationInACVF.Section5
