import IntegrationSection5.GammaRVIsomorphism
import IntegrationSection5.RVContractionGamma
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def fixedVFRVIso (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i) :
    GammaRVIso G (pullbackObject A) (pullbackObject B) := by
  apply GammaRVIso.ofVolumePreserving (rvContractionMap f hc) (rvContractionMap_bijective f hf hc hback) _
    (gamma_rvContractionMap_graph f hc hfG)
  intro q
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective A q
  rw [rvContractionMap_volume_spec,pullbackObject_value_key]
  funext i
  exact congrArg rv (hVF a i)

theorem fixedVFRVIso_square (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i) (a : A) :
    rvIsoHomMap (fixedVFRVIso f hf hc hback hfG hVF).iso (Map.toImage (rawKeyMap A) a) =
      Map.toImage (rawKeyMap B) (f a) := rvContractionMap_spec f hc a

end IntegrationInACVF.Section5
