import IntegrationSection5.GammaRVIsomorphism
import IntegrationSection5.UnaryHeadRVPresentation

/-! Explicit RV-domain presentation and constant-profile isomorphisms
retain their full original-Gamma graphs in both directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {r k m : ℕ}

def gammaCarrierVolumeIso (A B : PresentedSet (rawRVSpace (M := M) r) S)
    (u : Map A (PresentedSet.univ (rawRVSpace k) S))
    (v : Map B (PresentedSet.univ (rawRVSpace k) S)) (hAB : carrier A = carrier B)
    (hvol : ∀ a : A, (v ⟨a.val,hAB.le a.property⟩).val = (u a).val)
    (hA : GammaSetDefinable G {p : Point (M := M) 0 r | p.2 ∈ carrier A}) :
    GammaRVIso G
      (@SpecialTransformations.Section4.RVObject.mk M (@CanonicalStructure.normalize M sM) S k r A u)
      (@SpecialTransformations.Section4.RVObject.mk M (@CanonicalStructure.normalize M sM) S k r B v) := by
  let F : Map A B := Map.inclusion hAB.le
  have hF : Function.Bijective F := by
    constructor
    · intro a b he
      exact Subtype.ext (congrArg (fun x : B => x.val) he)
    · intro b
      exact ⟨⟨b.val,hAB.ge b.property⟩,Subtype.ext rfl⟩
  exact GammaRVIso.ofVolumePreserving F hF hvol (gamma_rvMap_identity_values F (fun _ => rfl) hA)

theorem gamma_unary_head_domain (V : DefSet (M := M) S 1 m)
    (hV : GammaSetDefinable G (carrier V)) :
    GammaSetDefinable G {p : Point (M := M) 0 (1+m) |
      p.2 ∈ carrier (Map.image (rawLabelMap (headImage V)))} := by
  have h := gamma_pullback_domain (gammaLogicInput G) V hV
  have he : {p : Point (M := M) 0 (1+m) | p.2 ∈ carrier (Map.image (rawLabelMap (headImage V)))} =
      {p : Point (M := M) 0 (1+m) | p.2 ∈ carrier (Map.image (rawKeyMap V))} := by
    ext p
    rw [unary_head_raw_domain]
  exact he.symm ▸ h

def gammaUnaryHeadVolumeIso (V : DefSet (M := M) S 1 m) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin k → Fin (1+m)) :
    GammaRVIso G (selectedVolumeObject (Map.image (rawLabelMap (headImage V))) ρ)
      (selectedVolumeObject (Map.image (rawKeyMap V)) ρ) :=
  gammaCarrierVolumeIso _ _ (rawRVProjectionMap ρ _) (rawRVProjectionMap ρ _)
    (unary_head_raw_domain V) (fun _ => rfl) (gamma_unary_head_domain V hV)

def gammaUnaryProfileIso
    {U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S 1}
    (e : GammaRVIso G U V)
    (u : Map (rvObjectDomain U) (PresentedSet.univ (rawRVSpace 2) S))
    (v : Map (rvObjectDomain V) (PresentedSet.univ (rawRVSpace 2) S))
    (r t : RV (M := M)) (hrt : r.val = iRVZero ↔ t.val = iRVZero)
    (hu : ∀ a, (u a).val = ![r,(rvObjectVolume U a).val 0])
    (hv : ∀ b, (v b).val = ![t,(rvObjectVolume V b).val 0]) :
    GammaRVIso G (@rvUnaryProfileObject M (@CanonicalStructure.normalize M sM) S U u)
      (@rvUnaryProfileObject M (@CanonicalStructure.normalize M sM) S V v) :=
  ⟨@rvUnaryProfileIso M (@CanonicalStructure.normalize M sM) S U V e.iso u v r t hrt hu hv,
    e.hom_graph,e.inv_graph⟩

end IntegrationInACVF.Section5
