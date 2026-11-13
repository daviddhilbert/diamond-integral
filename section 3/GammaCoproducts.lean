import «section 3».GammaTagIsomorphisms
import «section 3».FamilyCodeCoproducts
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def GammaHom.coprod {A B A' B' : GammaObject hc S k} (f : GammaHom A A') (g : GammaHom B B') :
    GammaHom (A.coprod B) (A'.coprod B') where
  bijection := f.bijection.coprod g.bijection
  contraction := by
    obtain ⟨F, hF⟩ := f.contraction
    obtain ⟨G, hG⟩ := g.contraction
    let H := (familyCodeCoprodBridge A' B').symm.comp
      ((F.coprod G).comp (familyCodeCoprodBridge A B))
    refine ⟨H, fun c => ?_⟩
    rcases familyCodeCoprod_cases A B c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · change (A'.coprod B').decode ((familyCodeCoprodBridge A' B').equiv.symm
        (familyCoprodMapEquiv F G ((familyCodeCoprodBridge A B).equiv (familyCodeCoprodInl A B a)))) =
        familyCoprodMapEquiv f.bijection g.bijection ((A.coprod B).decode (familyCodeCoprodInl A B a))
      rw [familyCodeCoprodBridge_inl, familyCoprodMapEquiv_inl, familyCodeCoprodBridge_symm_inl,
        familyCodeCoprod_decode_inl, familyCodeCoprod_decode_inl, familyCoprodMapEquiv_inl, hF]
    · change (A'.coprod B').decode ((familyCodeCoprodBridge A' B').equiv.symm
        (familyCoprodMapEquiv F G ((familyCodeCoprodBridge A B).equiv (familyCodeCoprodInr A B b)))) =
        familyCoprodMapEquiv f.bijection g.bijection ((A.coprod B).decode (familyCodeCoprodInr A B b))
      rw [familyCodeCoprodBridge_inr, familyCoprodMapEquiv_inr, familyCodeCoprodBridge_symm_inr,
        familyCodeCoprod_decode_inr, familyCodeCoprod_decode_inr, familyCoprodMapEquiv_inr, hG]

def gammaCoproductIsoData (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    CoproductIsoData (GammaObject hc S k) where
  empty := GammaObject.empty hc S k
  coprod := FiniteFamily.coprod
  mapIso e f := asIso (show _ ⟶ _ from GammaHom.coprod e.hom f.hom)
  assocIso := gammaCoprodAssocIso
  commIso := gammaCoprodCommIso
  emptyIso := gammaCoprodEmptyIso

abbrev GammaIsoClasses (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  CoproductIsoClasses (gammaCoproductIsoData (M := M) hc S k)

def gammaIsoClass (A : GammaObject hc S k) : GammaIsoClasses hc S k :=
  coproductIsoClass (gammaCoproductIsoData hc S k) A

theorem gammaIsoClass_eq_iff {A B : GammaObject hc S k} : gammaIsoClass A = gammaIsoClass B ↔ Nonempty (A ≅ B) :=
  coproductIsoClass_eq_iff _

@[simp] theorem gammaIsoClass_empty : gammaIsoClass (GammaObject.empty hc S k) = 0 := rfl

theorem gammaIsoClass_coprod (A B : GammaObject hc S k) :
    gammaIsoClass (A.coprod B) = gammaIsoClass A + gammaIsoClass B := rfl

end DiamondIntegral.Section3
