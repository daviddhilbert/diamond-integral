import «section 3».GammaGroundCodePresentations
import «section 3».GammaGroundFamilyCoproductMaps
import «section 3».GammaGroundFamilyPieceMaps
/-! Full real-code preimages commute with finite tagged disjoint union,
through explicit maps that retain every code. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P : Space LRV M}

def gammaGroundFamilyCodeCoprodInl (A B : GammaGroundFiniteFamily hc ground P) (a : A.codeLift.Carrier) : (A.coprod B).codeLift.Carrier :=
  ⟨Fin.castAdd B.tags a.1, ⟨a.2.val, by simpa only [GammaGroundFiniteFamily.codeLift, GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.2.property⟩⟩

def gammaGroundFamilyCodeCoprodInr (A B : GammaGroundFiniteFamily hc ground P) (b : B.codeLift.Carrier) : (A.coprod B).codeLift.Carrier :=
  ⟨Fin.natAdd A.tags b.1, ⟨b.2.val, by simpa only [GammaGroundFiniteFamily.codeLift, GammaGroundFiniteFamily.coprod, Fin.addCases_right] using b.2.property⟩⟩

def gammaGroundFamilyCodeCoprodBridge (A B : GammaGroundFiniteFamily hc ground P) :
    GammaGroundFamilyBijection (A.coprod B).codeLift (A.codeLift.coprod B.codeLift) :=
  GammaGroundFamilyBijection.pieces (A.coprod B).codeLift _ (fun i => GammaGroundBijection.ofCarrierEq (by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [GammaGroundFiniteFamily.codeLift, GammaGroundFiniteFamily.coprod, Fin.addCases_left]
    · simp only [GammaGroundFiniteFamily.codeLift, GammaGroundFiniteFamily.coprod, Fin.addCases_right]))

@[simp] theorem gammaGroundFamilyCodeCoprodBridge_inl (A B : GammaGroundFiniteFamily hc ground P) (a : A.codeLift.Carrier) :
    (gammaGroundFamilyCodeCoprodBridge A B).equiv (gammaGroundFamilyCodeCoprodInl A B a) =
      gammaGroundFamilyCoprodInl A.codeLift B.codeLift a := rfl

@[simp] theorem gammaGroundFamilyCodeCoprodBridge_inr (A B : GammaGroundFiniteFamily hc ground P) (b : B.codeLift.Carrier) :
    (gammaGroundFamilyCodeCoprodBridge A B).equiv (gammaGroundFamilyCodeCoprodInr A B b) =
      gammaGroundFamilyCoprodInr A.codeLift B.codeLift b := rfl

@[simp] theorem gammaGroundFamilyCodeCoprod_decode_inl (A B : GammaGroundFiniteFamily hc ground P) (a : A.codeLift.Carrier) :
    (A.coprod B).decode (gammaGroundFamilyCodeCoprodInl A B a) = gammaGroundFamilyCoprodInl A B (A.decode a) := rfl

@[simp] theorem gammaGroundFamilyCodeCoprod_decode_inr (A B : GammaGroundFiniteFamily hc ground P) (b : B.codeLift.Carrier) :
    (A.coprod B).decode (gammaGroundFamilyCodeCoprodInr A B b) = gammaGroundFamilyCoprodInr A B (B.decode b) := rfl

@[simp] theorem gammaGroundFamilyCodeCoprodBridge_symm_inl (A B : GammaGroundFiniteFamily hc ground P) (a : A.codeLift.Carrier) :
    (gammaGroundFamilyCodeCoprodBridge A B).equiv.symm (gammaGroundFamilyCoprodInl A.codeLift B.codeLift a) = gammaGroundFamilyCodeCoprodInl A B a :=
  (gammaGroundFamilyCodeCoprodBridge A B).equiv.symm_apply_eq.mpr (gammaGroundFamilyCodeCoprodBridge_inl A B a).symm

@[simp] theorem gammaGroundFamilyCodeCoprodBridge_symm_inr (A B : GammaGroundFiniteFamily hc ground P) (b : B.codeLift.Carrier) :
    (gammaGroundFamilyCodeCoprodBridge A B).equiv.symm (gammaGroundFamilyCoprodInr A.codeLift B.codeLift b) = gammaGroundFamilyCodeCoprodInr A B b :=
  (gammaGroundFamilyCodeCoprodBridge A B).equiv.symm_apply_eq.mpr (gammaGroundFamilyCodeCoprodBridge_inr A B b).symm

theorem gammaGroundFamilyCodeCoprod_cases (A B : GammaGroundFiniteFamily hc ground P) (x : (A.coprod B).codeLift.Carrier) :
    (∃ a, gammaGroundFamilyCodeCoprodInl A B a = x) ∨ (∃ b, gammaGroundFamilyCodeCoprodInr A B b = x) := by
  obtain ⟨i, a⟩ := x
  revert a
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · intro a
    left
    refine ⟨⟨i, ⟨a.val, ?_⟩⟩, rfl⟩
    simpa only [GammaGroundFiniteFamily.codeLift, GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.property
  · intro b
    right
    refine ⟨⟨j, ⟨b.val, ?_⟩⟩, rfl⟩
    simpa only [GammaGroundFiniteFamily.codeLift, GammaGroundFiniteFamily.coprod, Fin.addCases_right] using b.property

end DiamondIntegral.Section3
