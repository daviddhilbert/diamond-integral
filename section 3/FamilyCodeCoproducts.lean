import «section 3».CodePresentations
import «section 3».FamilyCoproductMaps
import «section 3».FamilyPieceMaps

/-! Full real-code preimages commute with finite tagged disjoint union,
through explicit maps that retain every code. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P : Space L M}

def familyCodeCoprodInl (A B : FiniteFamily P S) (a : A.codeLift.Carrier) : (A.coprod B).codeLift.Carrier :=
  ⟨Fin.castAdd B.tags a.1, ⟨a.2.val, by simpa only [FiniteFamily.codeLift, FiniteFamily.coprod, Fin.addCases_left] using a.2.property⟩⟩

def familyCodeCoprodInr (A B : FiniteFamily P S) (b : B.codeLift.Carrier) : (A.coprod B).codeLift.Carrier :=
  ⟨Fin.natAdd A.tags b.1, ⟨b.2.val, by simpa only [FiniteFamily.codeLift, FiniteFamily.coprod, Fin.addCases_right] using b.2.property⟩⟩

def familyCodeCoprodBridge (A B : FiniteFamily P S) :
    FamilyBijection (A.coprod B).codeLift (A.codeLift.coprod B.codeLift) :=
  FamilyBijection.pieces (A.coprod B).codeLift _ (fun i => DefinableBijection.ofCarrierEq (by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [FiniteFamily.codeLift, FiniteFamily.coprod, Fin.addCases_left]
    · simp only [FiniteFamily.codeLift, FiniteFamily.coprod, Fin.addCases_right]))

@[simp] theorem familyCodeCoprodBridge_inl (A B : FiniteFamily P S) (a : A.codeLift.Carrier) :
    (familyCodeCoprodBridge A B).equiv (familyCodeCoprodInl A B a) =
      familyCoprodInl A.codeLift B.codeLift a := rfl

@[simp] theorem familyCodeCoprodBridge_inr (A B : FiniteFamily P S) (b : B.codeLift.Carrier) :
    (familyCodeCoprodBridge A B).equiv (familyCodeCoprodInr A B b) =
      familyCoprodInr A.codeLift B.codeLift b := rfl

@[simp] theorem familyCodeCoprod_decode_inl (A B : FiniteFamily P S) (a : A.codeLift.Carrier) :
    (A.coprod B).decode (familyCodeCoprodInl A B a) = familyCoprodInl A B (A.decode a) := rfl

@[simp] theorem familyCodeCoprod_decode_inr (A B : FiniteFamily P S) (b : B.codeLift.Carrier) :
    (A.coprod B).decode (familyCodeCoprodInr A B b) = familyCoprodInr A B (B.decode b) := rfl

@[simp] theorem familyCodeCoprodBridge_symm_inl (A B : FiniteFamily P S) (a : A.codeLift.Carrier) :
    (familyCodeCoprodBridge A B).equiv.symm (familyCoprodInl A.codeLift B.codeLift a) = familyCodeCoprodInl A B a :=
  (familyCodeCoprodBridge A B).equiv.symm_apply_eq.mpr (familyCodeCoprodBridge_inl A B a).symm

@[simp] theorem familyCodeCoprodBridge_symm_inr (A B : FiniteFamily P S) (b : B.codeLift.Carrier) :
    (familyCodeCoprodBridge A B).equiv.symm (familyCoprodInr A.codeLift B.codeLift b) = familyCodeCoprodInr A B b :=
  (familyCodeCoprodBridge A B).equiv.symm_apply_eq.mpr (familyCodeCoprodBridge_inr A B b).symm

theorem familyCodeCoprod_cases (A B : FiniteFamily P S) (x : (A.coprod B).codeLift.Carrier) :
    (∃ a, familyCodeCoprodInl A B a = x) ∨ (∃ b, familyCodeCoprodInr A B b = x) := by
  obtain ⟨i, a⟩ := x
  revert a
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · intro a
    left
    refine ⟨⟨i, ⟨a.val, ?_⟩⟩, rfl⟩
    simpa only [FiniteFamily.codeLift, FiniteFamily.coprod, Fin.addCases_left] using a.property
  · intro b
    right
    refine ⟨⟨j, ⟨b.val, ?_⟩⟩, rfl⟩
    simpa only [FiniteFamily.codeLift, FiniteFamily.coprod, Fin.addCases_right] using b.property

end DiamondIntegral.Section3
