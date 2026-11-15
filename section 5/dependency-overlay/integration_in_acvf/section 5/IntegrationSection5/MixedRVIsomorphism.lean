import IntegrationSection5.MixedVolumeImages
import IntegrationSection5.MapInverseBijection
import Section4.LiftBijections
import IntegrationSection5.SmallGammaPresentation
import IntegrationSection5.GammaRVIsomorphism
import IntegrationSection5.RVContractionGamma
/-! The RV-category isomorphism of an actual mutually contractible mixed
bijection, in every VF arity. Weight comes from the pinned checked
injective commuting-lift dimension theorem; finite Gamma support constructs
an internal small real presentation rather than assuming it. Both full
original-base graph certificates are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def pullbackConjugate (f : Map A B) (hA : IsRVPullback (carrier A)) :
    Map (rawLift (pullbackObject A)) (rawLift (pullbackObject B)) :=
  Map.comp (pullbackLiftMap B) (Map.comp f (Map.inverse (pullbackLiftMap A) (pullbackLiftMap_bijective A hA)))

theorem pullbackConjugate_commutes (f : Map A B) (hc : Contractible f)
    (hA : IsRVPullback (carrier A)) :
    @SpecialTransformations.Section4.LiftCommutes M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) S n (pullbackObject A) (pullbackObject B)
      (rvContractionMap f hc) (pullbackConjugate f hA) := by
  intro p u hpu
  let a := Map.inverse (pullbackLiftMap A) (pullbackLiftMap_bijective A hA) p
  have ha : pullbackLiftMap A a = p := Map.apply_inverse _ _ p
  have hKey : Map.toImage (rawKeyMap A) a = u := by
    apply Subtype.ext
    exact (congrArg (fun q : rawLift (pullbackObject A) => q.val.2) ha).trans hpu
  have hVal := rvContractionMap_volume_spec f hc a
  have hOut := rvContractionMap_spec f hc a
  rw [hKey] at hVal hOut
  apply Prod.ext
  · change @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) n (f a).val.1 = _
    rw [normalized_tupleRV]
    exact hVal.symm
  · change (rawKeyMap B (f a)).val = _
    exact (congrArg Subtype.val hOut).symm

theorem mixed_rvContractionMap_volumetric_small {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Injective f) (hc : Contractible f)
    (hA : IsRVPullback (carrier A))
    (hB : IsRVPullback (carrier B))
    (u : rvObjectDomain (pullbackObject A)) :
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) n
      (rvObjectVolume (pullbackObject A) u).val ≤
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) n
      (rvObjectVolume (pullbackObject B) (rvContractionMap f hc u)).val := by
  let G := pullbackConjugate f hA
  let Fc := rvContractionMap f hc
  have hComm := pullbackConjugate_commutes f hc hA
  have hG : Function.Injective G := by
    intro p q he
    have h1 := (pullbackLiftMap_bijective B hB).1 he
    have h2 := hf h1
    have h3 := congrArg (pullbackLiftMap A) h2
    simpa only [Map.apply_inverse] using h3
  have hSat := @Saturated.normalize M sM κ hs
  let Δ := @SpecialTransformations.Section4.gammaSpace M sM hM
  have hΔ := @SpecialTransformations.Section4.gammaSpace_rvCoded M sM hM
  have hcan := @CanonicalStructure.normalize_isCanonical M sM
  let hN := @CanonicalStructure.normalized_model M sM hM
  let N := @CanonicalStructure.normalize M sM
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  let v := Values.presentationValuation (M := M)
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
  exact SpecialTransformations.Section4.lift_injective_volumetric hcan hκ hSat hsmall Δ hΔ
    Values.presentation_compatible Fc G hComm hG u

theorem mixed_rvContractionMap_volumetric {G : GammaParameters.Base (M := M)}
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk G.real < κ)
    (f : Map A B) (hf : Function.Injective f) (hc : Contractible f)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hADef : GammaSetDefinable G (carrier A)) (hBDef : GammaSetDefinable G (carrier B))
    (hfDef : GammaGraphDefinable G (pointMapGraph f))
    (u : rvObjectDomain (pullbackObject A)) :
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) n
      (rvObjectVolume (pullbackObject A) u).val ≤
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) n
      (rvObjectVolume (pullbackObject B) (rvContractionMap f hc u)).val := by
  obtain ⟨R,hGR,hR,hAr,hBr,hfr⟩ := common_gamma_presentation_small hκ hsmall
    (carrier A) (carrier B) f hADef hBDef hfDef
  let AR := PresentedSet.mk (carrier A) hAr
  let BR := PresentedSet.mk (carrier B) hBr
  let F : Map AR BR := Map.mk f hfr
  have hFA : IsRVPullback (carrier AR) := hA
  have hFB : IsRVPullback (carrier BR) := hB
  have hFC : Contractible F := hc
  have hFI : Function.Injective F := hf
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective A u
  have h := mixed_rvContractionMap_volumetric_small hκ hs hR F hFI hFC hFA hFB
    (Map.toImage (rawKeyMap AR) a)
  rw [pullbackObject_value_key,rvContractionMap_volume_spec] at h ⊢
  exact h

variable {P : GammaParameters.Base (M := M)}

def mixedRVHom {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    @SpecialTransformations.Section4.RVHom M (@CanonicalStructure.normalize M sM) S n
      (@pullbackObject M sM hM S n m A) (@pullbackObject M sM hM S n l B) := by
  refine @SpecialTransformations.Section4.RVHom.mk M (@CanonicalStructure.normalize M sM) S n
    (@pullbackObject M sM hM S n m A) (@pullbackObject M sM hM S n l B)
    (rvContractionMap f hc) ?_ ?_
  · exact mixed_rvContractionMap_volumetric hκ hs hsmall f hf.1 hc hA hB hADef hBDef hfDef
  · exact mixed_rvContractionMap_finite_volume_images hκ hs hsmall f hc hA hfDef

def mixedRVIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    pullbackObject A ≅ pullbackObject B where
  hom := mixedRVHom hκ hs hsmall f hf hc hback hA hB hADef hBDef hfDef
  inv := mixedRVHom hκ hs hsmall (Map.inverse f hf) (inverse_map_bijective f hf) hback
    (inverse_map_inverse_contractible f hf hc) hB hA hBDef hADef (gamma_inverse_map_graph f hf hfDef)
  hom_inv_id := by
    apply @SpecialTransformations.Section4.RVHom.ext M (@CanonicalStructure.normalize M sM) S n _ _ _ _
    apply Map.ext
    intro u
    obtain ⟨a,rfl⟩ := rawKeyImage_surjective A u
    change rvContractionMap (Map.inverse f hf) hback
      (rvContractionMap f hc (Map.toImage (rawKeyMap A) a)) = Map.toImage (rawKeyMap A) a
    rw [rvContractionMap_spec,rvContractionMap_spec,Map.inverse_apply]
  inv_hom_id := by
    apply @SpecialTransformations.Section4.RVHom.ext M (@CanonicalStructure.normalize M sM) S n _ _ _ _
    apply Map.ext
    intro u
    obtain ⟨b,rfl⟩ := rawKeyImage_surjective B u
    change rvContractionMap f hc
      (rvContractionMap (Map.inverse f hf) hback (Map.toImage (rawKeyMap B) b)) = Map.toImage (rawKeyMap B) b
    rw [rvContractionMap_spec,rvContractionMap_spec,Map.apply_inverse]

theorem mixedRVIso_spec {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) (a : A) :
    (@SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S n
      (@pullbackObject M sM hM S n m A) (@pullbackObject M sM hM S n l B)
      (mixedRVIso hκ hs hsmall f hf hc hback hA hB hADef hBDef hfDef).hom)
      (Map.toImage (rawKeyMap A) a) = Map.toImage (rawKeyMap B) (f a) :=
  rvContractionMap_spec f hc a


def mixedGammaRVIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    GammaRVIso P (pullbackObject A) (pullbackObject B) :=
  ⟨mixedRVIso hκ hs hsmall f hf hc hback hA hB hADef hBDef hfDef,
    gamma_rvContractionMap_graph f hc hfDef,
    gamma_rvContractionMap_graph (Map.inverse f hf) hback (gamma_inverse_map_graph f hf hfDef)⟩

end IntegrationInACVF.Section5
