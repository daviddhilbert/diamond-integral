import «section 3».GammaGroundFamilyTagMaps
/-! The carrier of the tagged gammaGroundFamily coproduct is the genuine disjoint
sum of the two original carriers. -/
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

def gammaGroundFamilyCoprodInl (A B : GammaGroundFiniteFamily hc ground P) (a : A.Carrier) : (A.coprod B).Carrier :=
  ⟨Fin.castAdd B.tags a.1, ⟨a.2.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.2.property⟩⟩

def gammaGroundFamilyCoprodInr (A B : GammaGroundFiniteFamily hc ground P) (b : B.Carrier) : (A.coprod B).Carrier :=
  ⟨Fin.natAdd A.tags b.1, ⟨b.2.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using b.2.property⟩⟩

def gammaGroundFamilyCoprodDecode (A B : GammaGroundFiniteFamily hc ground P) (x : (A.coprod B).Carrier) : A.Carrier ⊕ B.Carrier := by
  obtain ⟨i, a⟩ := x
  refine (Fin.addCases (motive := fun i => (A.coprod B).piece i → A.Carrier ⊕ B.Carrier) ?_ ?_ i) a
  · intro i a
    exact Sum.inl ⟨i, ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.property⟩⟩
  · intro j b
    exact Sum.inr ⟨j, ⟨b.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using b.property⟩⟩

@[simp] theorem gammaGroundFamilyCoprodDecode_inl (A B : GammaGroundFiniteFamily hc ground P) (a : A.Carrier) :
    gammaGroundFamilyCoprodDecode A B (gammaGroundFamilyCoprodInl A B a) = Sum.inl a := by
  cases a
  simp only [gammaGroundFamilyCoprodDecode, gammaGroundFamilyCoprodInl, Fin.addCases_left]

@[simp] theorem gammaGroundFamilyCoprodDecode_inr (A B : GammaGroundFiniteFamily hc ground P) (b : B.Carrier) :
    gammaGroundFamilyCoprodDecode A B (gammaGroundFamilyCoprodInr A B b) = Sum.inr b := by
  cases b
  simp only [gammaGroundFamilyCoprodDecode, gammaGroundFamilyCoprodInr, Fin.addCases_right]

def gammaGroundFamilyCoprodEncode (A B : GammaGroundFiniteFamily hc ground P) : A.Carrier ⊕ B.Carrier → (A.coprod B).Carrier :=
  Sum.elim (gammaGroundFamilyCoprodInl A B) (gammaGroundFamilyCoprodInr A B)

theorem gammaGroundFamilyCoprodEncode_decode (A B : GammaGroundFiniteFamily hc ground P) (x : (A.coprod B).Carrier) :
    gammaGroundFamilyCoprodEncode A B (gammaGroundFamilyCoprodDecode A B x) = x := by
  obtain ⟨i, a⟩ := x
  revert a
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · intro a
    simp only [gammaGroundFamilyCoprodDecode, Fin.addCases_left, gammaGroundFamilyCoprodEncode, Sum.elim_inl, gammaGroundFamilyCoprodInl]
  · intro b
    simp only [gammaGroundFamilyCoprodDecode, Fin.addCases_right, gammaGroundFamilyCoprodEncode, Sum.elim_inr, gammaGroundFamilyCoprodInr]

def gammaGroundFamilyCoprodEquiv (A B : GammaGroundFiniteFamily hc ground P) : (A.coprod B).Carrier ≃ A.Carrier ⊕ B.Carrier where
  toFun := gammaGroundFamilyCoprodDecode A B
  invFun := gammaGroundFamilyCoprodEncode A B
  left_inv := gammaGroundFamilyCoprodEncode_decode A B
  right_inv x := by
    cases x with
    | inl a => exact gammaGroundFamilyCoprodDecode_inl A B a
    | inr b => exact gammaGroundFamilyCoprodDecode_inr A B b

end DiamondIntegral.Section3
