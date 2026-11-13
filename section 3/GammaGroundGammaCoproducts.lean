import «section 3».GammaGroundGammaTagIsomorphisms
import «section 3».GammaGroundFamilyCodeCoproducts
import «section 3».CoproductIsoClasses
/-! Gamma disjoint unions preserve the defining RV contraction witnesses.
Their actual isomorphism classes carry the coproduct additive monoid. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundGammaHom.coprod {A B A' B' : GammaGroundGammaObject hc ground k} (f : GammaGroundGammaHom A A') (g : GammaGroundGammaHom B B') :
    GammaGroundGammaHom (A.coprod B) (A'.coprod B') where
  bijection := f.bijection.coprod g.bijection
  contraction := by
    obtain ⟨F, hF⟩ := f.contraction
    obtain ⟨G, hG⟩ := g.contraction
    let H := (gammaGroundFamilyCodeCoprodBridge A' B').symm.comp
      ((F.coprod G).comp (gammaGroundFamilyCodeCoprodBridge A B))
    refine ⟨H, fun c => ?_⟩
    rcases gammaGroundFamilyCodeCoprod_cases A B c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · change (A'.coprod B').decode ((gammaGroundFamilyCodeCoprodBridge A' B').equiv.symm
        (gammaGroundFamilyCoprodMapEquiv F G ((gammaGroundFamilyCodeCoprodBridge A B).equiv (gammaGroundFamilyCodeCoprodInl A B a)))) =
        gammaGroundFamilyCoprodMapEquiv f.bijection g.bijection ((A.coprod B).decode (gammaGroundFamilyCodeCoprodInl A B a))
      rw [gammaGroundFamilyCodeCoprodBridge_inl, gammaGroundFamilyCoprodMapEquiv_inl, gammaGroundFamilyCodeCoprodBridge_symm_inl,
        gammaGroundFamilyCodeCoprod_decode_inl, gammaGroundFamilyCodeCoprod_decode_inl, gammaGroundFamilyCoprodMapEquiv_inl, hF]
    · change (A'.coprod B').decode ((gammaGroundFamilyCodeCoprodBridge A' B').equiv.symm
        (gammaGroundFamilyCoprodMapEquiv F G ((gammaGroundFamilyCodeCoprodBridge A B).equiv (gammaGroundFamilyCodeCoprodInr A B b)))) =
        gammaGroundFamilyCoprodMapEquiv f.bijection g.bijection ((A.coprod B).decode (gammaGroundFamilyCodeCoprodInr A B b))
      rw [gammaGroundFamilyCodeCoprodBridge_inr, gammaGroundFamilyCoprodMapEquiv_inr, gammaGroundFamilyCodeCoprodBridge_symm_inr,
        gammaGroundFamilyCodeCoprod_decode_inr, gammaGroundFamilyCodeCoprod_decode_inr, gammaGroundFamilyCoprodMapEquiv_inr, hG]

def gammaGroundGammaCoproductIsoData (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    CoproductIsoData (GammaGroundGammaObject hc ground k) where
  empty := GammaGroundGammaObject.empty hc ground k
  coprod := GammaGroundFiniteFamily.coprod
  mapIso e f := asIso (show _ ⟶ _ from GammaGroundGammaHom.coprod e.hom f.hom)
  assocIso := gammaGroundGammaCoprodAssocIso
  commIso := gammaGroundGammaCoprodCommIso
  emptyIso := gammaGroundGammaCoprodEmptyIso

abbrev GammaGroundGammaIsoClasses (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  CoproductIsoClasses (gammaGroundGammaCoproductIsoData (M := M) hc ground k)

def gammaGroundGammaIsoClass (A : GammaGroundGammaObject hc ground k) : GammaGroundGammaIsoClasses hc ground k :=
  coproductIsoClass (gammaGroundGammaCoproductIsoData hc ground k) A

theorem gammaGroundGammaIsoClass_eq_iff {A B : GammaGroundGammaObject hc ground k} : gammaGroundGammaIsoClass A = gammaGroundGammaIsoClass B ↔ Nonempty (A ≅ B) :=
  coproductIsoClass_eq_iff _

@[simp] theorem gammaGroundGammaIsoClass_empty : gammaGroundGammaIsoClass (GammaGroundGammaObject.empty hc ground k) = 0 := rfl

theorem gammaGroundGammaIsoClass_coprod (A B : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaIsoClass (A.coprod B) = gammaGroundGammaIsoClass A + gammaGroundGammaIsoClass B := rfl

end DiamondIntegral.Section3
