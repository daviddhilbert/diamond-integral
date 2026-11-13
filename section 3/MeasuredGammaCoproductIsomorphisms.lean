import «section 3».MeasuredGammaCoproducts
import «section 3».MeasuredGammaRVScissors

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

theorem gammaCoprodComm_inl (A B : GammaObject hc S k) (a : A.Carrier) :
    (gammaCoprodCommIso A B).hom.bijection.equiv (familyCoprodInl A B a) = familyCoprodInr B A a := by
  apply familyCarrier_ext _
  · exact finAddFlip_apply_castAdd a.1 B.tags
  · rfl

theorem gammaCoprodComm_inr (A B : GammaObject hc S k) (b : B.Carrier) :
    (gammaCoprodCommIso A B).hom.bijection.equiv (familyCoprodInr A B b) = familyCoprodInl B A b := by
  apply familyCarrier_ext _
  · exact finAddFlip_apply_natAdd b.1 A.tags
  · rfl

def measuredGammaCoprodCommHom (A B : MeasuredGammaObject hc S k) :
    MeasuredGammaHom (A.coprod B) (B.coprod A) where
  underlying := (gammaCoprodCommIso A.underlying B.underlying).hom
  preserves x := by
    rcases familyCoprod_cases A.underlying B.underlying x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [gammaCoprodComm_inl, measuredGammaCoprod_combined_left, measuredGammaCoprod_combined_right]
    · rw [gammaCoprodComm_inr, measuredGammaCoprod_combined_right, measuredGammaCoprod_combined_left]

def MeasuredGammaHom.coprod {A B A' B' : MeasuredGammaObject hc S k}
    (f : MeasuredGammaHom A A') (g : MeasuredGammaHom B B') :
    MeasuredGammaHom (A.coprod B) (A'.coprod B') where
  underlying := f.underlying.coprod g.underlying
  preserves x := by
    rcases familyCoprod_cases A.underlying B.underlying x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · change (A.coprod B).combinedWeight (familyCoprodInl _ _ a) =
        (A'.coprod B').combinedWeight (familyCoprodMapEquiv f.underlying.bijection g.underlying.bijection (familyCoprodInl _ _ a))
      rw [familyCoprodMapEquiv_inl, measuredGammaCoprod_combined_left, measuredGammaCoprod_combined_left]
      exact f.preserves a
    · change (A.coprod B).combinedWeight (familyCoprodInr _ _ b) =
        (A'.coprod B').combinedWeight (familyCoprodMapEquiv f.underlying.bijection g.underlying.bijection (familyCoprodInr _ _ b))
      rw [familyCoprodMapEquiv_inr, measuredGammaCoprod_combined_right, measuredGammaCoprod_combined_right]
      exact g.preserves b

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem gammaCoprodAssoc_left (A B D : GammaObject hc S k) (a : A.Carrier) :
    (gammaCoprodAssocIso A B D).hom.bijection.equiv (familyCoprodInl _ D (familyCoprodInl A B a)) =
      familyCoprodInl A (B.coprod D) a := by
  apply familyCarrier_ext _
  · apply Fin.ext; rfl
  · rfl

theorem gammaCoprodAssoc_middle (A B D : GammaObject hc S k) (b : B.Carrier) :
    (gammaCoprodAssocIso A B D).hom.bijection.equiv (familyCoprodInl _ D (familyCoprodInr A B b)) =
      familyCoprodInr A _ (familyCoprodInl B D b) := by
  apply familyCarrier_ext _
  · apply Fin.ext; rfl
  · rfl

theorem gammaCoprodAssoc_right (A B D : GammaObject hc S k) (d : D.Carrier) :
    (gammaCoprodAssocIso A B D).hom.bijection.equiv (familyCoprodInr (A.coprod B) D d) =
      familyCoprodInr A _ (familyCoprodInr B D d) := by
  apply familyCarrier_ext _
  · apply Fin.ext
    exact Nat.add_assoc A.tags B.tags d.1.val
  · rfl

def measuredGammaCoprodAssocHom (A B D : MeasuredGammaObject hc S k) :
    MeasuredGammaHom ((A.coprod B).coprod D) (A.coprod (B.coprod D)) where
  underlying := (gammaCoprodAssocIso A.underlying B.underlying D.underlying).hom
  preserves x := by
    rcases familyCoprod_cases (A.underlying.coprod B.underlying) D.underlying x with ⟨ab, rfl⟩ | ⟨d, rfl⟩
    · rcases familyCoprod_cases A.underlying B.underlying ab with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · rw [gammaCoprodAssoc_left, measuredGammaCoprod_combined_left,
          measuredGammaCoprod_combined_left, measuredGammaCoprod_combined_left]
      · rw [gammaCoprodAssoc_middle, measuredGammaCoprod_combined_left,
          measuredGammaCoprod_combined_right, measuredGammaCoprod_combined_right,
          measuredGammaCoprod_combined_left]
    · rw [gammaCoprodAssoc_right, measuredGammaCoprod_combined_right,
        measuredGammaCoprod_combined_right, measuredGammaCoprod_combined_right]

theorem gammaCoprodEmpty_inr (A : GammaObject hc S k) (a : A.Carrier) :
    (gammaCoprodEmptyIso A).hom.bijection.equiv (familyCoprodInr (GammaObject.empty hc S k) A a) = a := by
  apply familyCarrier_ext _
  · apply Fin.ext
    exact Nat.zero_add a.1.val
  · rfl

def measuredGammaCoprodEmptyHom (A : MeasuredGammaObject hc S k) :
    MeasuredGammaHom ((MeasuredGammaObject.empty hc S k).coprod A) A where
  underlying := (gammaCoprodEmptyIso A.underlying).hom
  preserves x := by
    rcases familyCoprod_cases (GammaObject.empty hc S k) A.underlying x with ⟨e, rfl⟩ | ⟨a, rfl⟩
    · exact e.1.elim0
    · exact (measuredGammaCoprod_combined_right (MeasuredGammaObject.empty hc S k) A a).trans
        (congrArg A.combinedWeight (gammaCoprodEmpty_inr A.underlying a).symm)

def measuredGammaCoproductIsoData (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    CoproductIsoData (MeasuredGammaObject hc S k) where
  empty := MeasuredGammaObject.empty hc S k
  coprod := MeasuredGammaObject.coprod
  mapIso e f := asIso (show _ ⟶ _ from MeasuredGammaHom.coprod e.hom f.hom)
  assocIso A B D := asIso (show _ ⟶ _ from measuredGammaCoprodAssocHom A B D)
  commIso A B := asIso (show _ ⟶ _ from measuredGammaCoprodCommHom A B)
  emptyIso A := asIso (show _ ⟶ _ from measuredGammaCoprodEmptyHom A)

abbrev MeasuredGammaIsoClasses (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  CoproductIsoClasses (measuredGammaCoproductIsoData (M := M) hc S k)

def measuredGammaIsoClass (A : MeasuredGammaObject hc S k) : MeasuredGammaIsoClasses hc S k :=
  coproductIsoClass (measuredGammaCoproductIsoData hc S k) A

theorem measuredGammaIsoClass_eq_iff {A B : MeasuredGammaObject hc S k} :
    measuredGammaIsoClass A = measuredGammaIsoClass B ↔ Nonempty (A ≅ B) := coproductIsoClass_eq_iff _

@[simp] theorem measuredGammaIsoClass_empty : measuredGammaIsoClass (MeasuredGammaObject.empty hc S k) = 0 := rfl

theorem measuredGammaIsoClass_coprod (A B : MeasuredGammaObject hc S k) :
    measuredGammaIsoClass (A.coprod B) = measuredGammaIsoClass A + measuredGammaIsoClass B := rfl

end DiamondIntegral.Section3

