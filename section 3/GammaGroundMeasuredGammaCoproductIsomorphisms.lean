import «section 3».GammaGroundMeasuredGammaCoproducts
import «section 3».GammaGroundGammaPartitions
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

theorem gammaGroundGammaCoprodComm_inl (A B : GammaGroundGammaObject hc ground k) (a : A.Carrier) :
    (gammaGroundGammaCoprodCommIso A B).hom.bijection.equiv (gammaGroundFamilyCoprodInl A B a) = gammaGroundFamilyCoprodInr B A a := by
  apply gammaGroundFamilyCarrier_ext _
  · exact finAddFlip_apply_castAdd a.1 B.tags
  · rfl

theorem gammaGroundGammaCoprodComm_inr (A B : GammaGroundGammaObject hc ground k) (b : B.Carrier) :
    (gammaGroundGammaCoprodCommIso A B).hom.bijection.equiv (gammaGroundFamilyCoprodInr A B b) = gammaGroundFamilyCoprodInl B A b := by
  apply gammaGroundFamilyCarrier_ext _
  · exact finAddFlip_apply_natAdd b.1 A.tags
  · rfl

def gammaGroundMeasuredGammaCoprodCommHom (A B : GammaGroundMeasuredGammaObject hc ground k) :
    GammaGroundMeasuredGammaHom (A.coprod B) (B.coprod A) where
  underlying := (gammaGroundGammaCoprodCommIso A.underlying B.underlying).hom
  preserves x := by
    rcases gammaGroundFamilyCoprod_cases A.underlying B.underlying x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [gammaGroundGammaCoprodComm_inl, gammaGroundMeasuredGammaCoprod_combined_left, gammaGroundMeasuredGammaCoprod_combined_right]
    · rw [gammaGroundGammaCoprodComm_inr, gammaGroundMeasuredGammaCoprod_combined_right, gammaGroundMeasuredGammaCoprod_combined_left]

def GammaGroundMeasuredGammaHom.coprod {A B A' B' : GammaGroundMeasuredGammaObject hc ground k}
    (f : GammaGroundMeasuredGammaHom A A') (g : GammaGroundMeasuredGammaHom B B') :
    GammaGroundMeasuredGammaHom (A.coprod B) (A'.coprod B') where
  underlying := f.underlying.coprod g.underlying
  preserves x := by
    rcases gammaGroundFamilyCoprod_cases A.underlying B.underlying x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · change (A.coprod B).combinedWeight (gammaGroundFamilyCoprodInl _ _ a) =
        (A'.coprod B').combinedWeight (gammaGroundFamilyCoprodMapEquiv f.underlying.bijection g.underlying.bijection (gammaGroundFamilyCoprodInl _ _ a))
      rw [gammaGroundFamilyCoprodMapEquiv_inl, gammaGroundMeasuredGammaCoprod_combined_left, gammaGroundMeasuredGammaCoprod_combined_left]
      exact f.preserves a
    · change (A.coprod B).combinedWeight (gammaGroundFamilyCoprodInr _ _ b) =
        (A'.coprod B').combinedWeight (gammaGroundFamilyCoprodMapEquiv f.underlying.bijection g.underlying.bijection (gammaGroundFamilyCoprodInr _ _ b))
      rw [gammaGroundFamilyCoprodMapEquiv_inr, gammaGroundMeasuredGammaCoprod_combined_right, gammaGroundMeasuredGammaCoprod_combined_right]
      exact g.preserves b

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundGammaCoprodAssoc_left (A B D : GammaGroundGammaObject hc ground k) (a : A.Carrier) :
    (gammaGroundGammaCoprodAssocIso A B D).hom.bijection.equiv (gammaGroundFamilyCoprodInl _ D (gammaGroundFamilyCoprodInl A B a)) =
      gammaGroundFamilyCoprodInl A (B.coprod D) a := by
  apply gammaGroundFamilyCarrier_ext _
  · apply Fin.ext; rfl
  · rfl

theorem gammaGroundGammaCoprodAssoc_middle (A B D : GammaGroundGammaObject hc ground k) (b : B.Carrier) :
    (gammaGroundGammaCoprodAssocIso A B D).hom.bijection.equiv (gammaGroundFamilyCoprodInl _ D (gammaGroundFamilyCoprodInr A B b)) =
      gammaGroundFamilyCoprodInr A _ (gammaGroundFamilyCoprodInl B D b) := by
  apply gammaGroundFamilyCarrier_ext _
  · apply Fin.ext; rfl
  · rfl

theorem gammaGroundGammaCoprodAssoc_right (A B D : GammaGroundGammaObject hc ground k) (d : D.Carrier) :
    (gammaGroundGammaCoprodAssocIso A B D).hom.bijection.equiv (gammaGroundFamilyCoprodInr (A.coprod B) D d) =
      gammaGroundFamilyCoprodInr A _ (gammaGroundFamilyCoprodInr B D d) := by
  apply gammaGroundFamilyCarrier_ext _
  · apply Fin.ext
    exact Nat.add_assoc A.tags B.tags d.1.val
  · rfl

def gammaGroundMeasuredGammaCoprodAssocHom (A B D : GammaGroundMeasuredGammaObject hc ground k) :
    GammaGroundMeasuredGammaHom ((A.coprod B).coprod D) (A.coprod (B.coprod D)) where
  underlying := (gammaGroundGammaCoprodAssocIso A.underlying B.underlying D.underlying).hom
  preserves x := by
    rcases gammaGroundFamilyCoprod_cases (A.underlying.coprod B.underlying) D.underlying x with ⟨ab, rfl⟩ | ⟨d, rfl⟩
    · rcases gammaGroundFamilyCoprod_cases A.underlying B.underlying ab with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · rw [gammaGroundGammaCoprodAssoc_left, gammaGroundMeasuredGammaCoprod_combined_left,
          gammaGroundMeasuredGammaCoprod_combined_left, gammaGroundMeasuredGammaCoprod_combined_left]
      · rw [gammaGroundGammaCoprodAssoc_middle, gammaGroundMeasuredGammaCoprod_combined_left,
          gammaGroundMeasuredGammaCoprod_combined_right, gammaGroundMeasuredGammaCoprod_combined_right,
          gammaGroundMeasuredGammaCoprod_combined_left]
    · rw [gammaGroundGammaCoprodAssoc_right, gammaGroundMeasuredGammaCoprod_combined_right,
        gammaGroundMeasuredGammaCoprod_combined_right, gammaGroundMeasuredGammaCoprod_combined_right]

theorem gammaGroundGammaCoprodEmpty_inr (A : GammaGroundGammaObject hc ground k) (a : A.Carrier) :
    (gammaGroundGammaCoprodEmptyIso A).hom.bijection.equiv (gammaGroundFamilyCoprodInr (GammaGroundGammaObject.empty hc ground k) A a) = a := by
  apply gammaGroundFamilyCarrier_ext _
  · apply Fin.ext
    exact Nat.zero_add a.1.val
  · rfl

def gammaGroundMeasuredGammaCoprodEmptyHom (A : GammaGroundMeasuredGammaObject hc ground k) :
    GammaGroundMeasuredGammaHom ((GammaGroundMeasuredGammaObject.empty hc ground k).coprod A) A where
  underlying := (gammaGroundGammaCoprodEmptyIso A.underlying).hom
  preserves x := by
    rcases gammaGroundFamilyCoprod_cases (GammaGroundGammaObject.empty hc ground k) A.underlying x with ⟨e, rfl⟩ | ⟨a, rfl⟩
    · exact e.1.elim0
    · exact (gammaGroundMeasuredGammaCoprod_combined_right (GammaGroundMeasuredGammaObject.empty hc ground k) A a).trans
        (congrArg A.combinedWeight (gammaGroundGammaCoprodEmpty_inr A.underlying a).symm)

def gammaGroundMeasuredGammaCoproductIsoData (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    CoproductIsoData (GammaGroundMeasuredGammaObject hc ground k) where
  empty := GammaGroundMeasuredGammaObject.empty hc ground k
  coprod := GammaGroundMeasuredGammaObject.coprod
  mapIso e f := asIso (show _ ⟶ _ from GammaGroundMeasuredGammaHom.coprod e.hom f.hom)
  assocIso A B D := asIso (show _ ⟶ _ from gammaGroundMeasuredGammaCoprodAssocHom A B D)
  commIso A B := asIso (show _ ⟶ _ from gammaGroundMeasuredGammaCoprodCommHom A B)
  emptyIso A := asIso (show _ ⟶ _ from gammaGroundMeasuredGammaCoprodEmptyHom A)

abbrev GammaGroundMeasuredGammaIsoClasses (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  CoproductIsoClasses (gammaGroundMeasuredGammaCoproductIsoData (M := M) hc ground k)

def gammaGroundMeasuredGammaIsoClass (A : GammaGroundMeasuredGammaObject hc ground k) : GammaGroundMeasuredGammaIsoClasses hc ground k :=
  coproductIsoClass (gammaGroundMeasuredGammaCoproductIsoData hc ground k) A

theorem gammaGroundMeasuredGammaIsoClass_eq_iff {A B : GammaGroundMeasuredGammaObject hc ground k} :
    gammaGroundMeasuredGammaIsoClass A = gammaGroundMeasuredGammaIsoClass B ↔ Nonempty (A ≅ B) := coproductIsoClass_eq_iff _

@[simp] theorem gammaGroundMeasuredGammaIsoClass_empty : gammaGroundMeasuredGammaIsoClass (GammaGroundMeasuredGammaObject.empty hc ground k) = 0 := rfl

theorem gammaGroundMeasuredGammaIsoClass_coprod (A B : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaIsoClass (A.coprod B) = gammaGroundMeasuredGammaIsoClass A + gammaGroundMeasuredGammaIsoClass B := rfl

end DiamondIntegral.Section3

