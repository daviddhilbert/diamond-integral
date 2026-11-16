import «section 6».OrdinaryLocalTranslations
import «section 6».OrdinaryChainZeroEndpoints
import «section 6».UnaryPullbackPreservation

/-! Sufficiently small whole cores at actual ordinary zero-event
centers have RV-pullback images. Surjectivity onto the ordinary target
and its exact unary difference law prove full image saturation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}

def ordinaryCenteredCoreImage (T : SpecialTransformations.Section5.Chain R 1 A B) (p : A) (γ : Gamma M) :
    Set (Mixed M 1 s) := {q | ∃ a : A,a.val.1 0 ∈ centeredGammaDisc (p.val.1 0) γ ∧
      a.val.2=p.val.2 ∧ (T.toMap a).val=q}

theorem ordinary_centered_core_image_rvPullback_of_translation
    (T : SpecialTransformations.Section5.Chain R 1 A B) (p : A) (γ : Gamma M)
    (hB : IsRVPullback (SpecialTransformations.Section5.carrier B))
    (hTranslation : ∀ a : A,a.val.1 0 ∈ centeredGammaDisc (p.val.1 0) γ → a.val.2=p.val.2 →
      ordinaryUnaryField (T.toMap a).val=ordinaryUnaryField a.val-ordinaryUnaryField p.val) :
    IsRVPullback (ordinaryCenteredCoreImage T p γ) := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨z,hz,hVF,hRV⟩ := (mem_rvHull_iff (ordinaryCenteredCoreImage T p γ) q).mp hq
  obtain ⟨a,haDisc,haTags,haMap⟩ := hz
  have hzB : z ∈ SpecialTransformations.Section5.carrier B := haMap ▸ (T.toMap a).property
  have hqB := rvPullback_mem_of_sameRV hB hzB hVF hRV
  obtain ⟨b,hb⟩ := T.bijective.surjective ⟨q,hqB⟩
  have hbMap : (T.toMap b).val=q := congrArg Subtype.val hb
  have hbTags : (T.toMap b).val.2=(T.toMap a).val.2 := by
    have hh := congrArg (fun w : Mixed M 1 s => w.2) hbMap
    have ha := congrArg (fun w : Mixed M 1 s => w.2) haMap
    exact hh.trans (hRV.symm.trans ha.symm)
  have hbOldTags : b.val.2=p.val.2 := (T.labels_eq_of b a hbTags).trans haTags
  have hDifference : ordinaryUnaryField (T.toMap b).val-ordinaryUnaryField (T.toMap a).val=
      ordinaryUnaryField b.val-ordinaryUnaryField a.val := by
    simpa only [ordinaryUnaryField,SpecialTransformations.Section5.vfAt] using T.unary_sub b a hbTags
  have hbField : ordinaryUnaryField (T.toMap b).val=ordinaryUnaryField q := congrArg (fun w : Mixed M 1 s => w.1 0) hbMap
  rw [hbField,hTranslation a haDisc haTags] at hDifference
  have hbCentered : ordinaryUnaryField b.val-ordinaryUnaryField p.val=ordinaryUnaryField q := by linear_combination -hDifference
  have hLead : rv M ((T.toMap a).val.1 0)=rv M (q.1 0) := by
    have hh := congrArg (fun w : Mixed M 1 s => rv M (w.1 0)) haMap
    exact hh.trans (congrFun hVF 0)
  have hValue : vfValue (ordinaryUnaryField q)=vfValue (ordinaryUnaryField (T.toMap a).val) := congrArg Values.vrv hLead.symm
  have hbDisc : b.val.1 0 ∈ centeredGammaDisc (p.val.1 0) γ := by
    apply (mem_centeredGammaDisc _ _ _).mpr
    change γ.val < vfValue (ordinaryUnaryField b.val-ordinaryUnaryField p.val)
    rw [hbCentered,hValue,hTranslation a haDisc haTags]
    exact (mem_centeredGammaDisc _ _ _).mp haDisc
  exact ⟨b,hbDisc,hbOldTags,hbMap⟩

theorem ordinary_centered_zero_event_core_images_rvPullback
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (hB : IsRVPullback (SpecialTransformations.Section5.carrier B)) (p : A)
    (hp : p.val ∈ ordinaryChainZeroSources T) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ γ : Gamma M,η ≤ γ → IsRVPullback (ordinaryCenteredCoreImage T p γ) := by
  obtain ⟨η,hη1,hLocal⟩ := ordinary_chain_locally_translation hc hs hsmall T hT p
  have hp0 := (ordinaryChainZeroSources_iff_endpoint_zero T p).mp hp
  refine ⟨η,hη1,fun γ hηγ => ordinary_centered_core_image_rvPullback_of_translation T p γ hB ?_⟩
  intro a haDisc haTags
  have hh := (mem_centeredGammaDisc _ _ _).mp haDisc
  have hClose : η.val < vfValue (ordinaryUnaryField a.val-ordinaryUnaryField p.val) :=
    (show η.val ≤ γ.val from hηγ).trans_lt hh
  have hTranslate := hLocal a haTags hClose
  simpa only [ordinaryUnaryField,hp0,sub_zero] using hTranslate

end DiamondIntegral.Section6
