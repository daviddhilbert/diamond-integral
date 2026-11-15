import IntegrationSection5.HullTranslationFocus
import IntegrationSection5.ScalarRealPresentation
import Section5.GammaLift

/-! Construct an actual special translation, with complete original-Gamma
certificates, from the source tag and a centre in its actual RV class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

theorem gamma_tagged_translation (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (i : Fin n) (k : Fin m) (hTag : Tagged A i k)
    (c : Point (M := M) n m → VF (M := M))
    (hind : ∀ p ∈ A, ∀ q ∈ A, erase i p = erase i q → c p = c q)
    (hRV : ∀ p ∈ A, rv (c p) = rv (vfAt p i))
    (hc : GammaScalarGraphDefinable G (fun p x => p ∈ A ∧ x = c p)) :
    ∃ B : Set (Point (M := M) n m), ∃ T : GammaSpecialBijection G A B,
      ∀ a : A, ((T.iso (gammaLogicInput G)).equiv a).val = replace i a.val (vfAt a.val i-c a.val) := by
  obtain ⟨S,hGS,hAr,hcr⟩ := scalar_real_presentation A hA c hc
  let AR : DefSet (M := M) S n m := @PresentedSet.mk M sM (pointSpace n m) S A hAr
  let D : Focus AR i k := hullTranslationFocus hTag c hind hRV hcr
  have hD : GammaFocusDefinable G D := hullTranslationFocus_gamma (A := AR) (i := i) (k := k) hA hTag c hind hRV hcr hc
  have hEta : GammaSetDefinable G (carrier D.etaImage) :=
    GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal D) ⟨hA,hD⟩
  let T : GammaSpecialBijection G A (carrier D.etaImage) :=
    ⟨S,hGS,AR,D.etaImage,rfl,rfl,SpecialBijection.centripetal D,⟨⟨hA,hD⟩,hEta⟩⟩
  refine ⟨carrier D.etaImage,T,?_⟩
  intro a
  exact hullTranslationFocus_apply (A := AR) (i := i) (k := k) hTag c hind hRV hcr a

end IntegrationInACVF.Section5
