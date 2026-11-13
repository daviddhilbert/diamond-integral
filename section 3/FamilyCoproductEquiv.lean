import «section 3».FamilyTagMaps

/-! The carrier of the tagged family coproduct is the genuine disjoint
sum of the two original carriers. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P : Space L M}

def familyCoprodInl (A B : FiniteFamily P S) (a : A.Carrier) : (A.coprod B).Carrier :=
  ⟨Fin.castAdd B.tags a.1, ⟨a.2.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using a.2.property⟩⟩

def familyCoprodInr (A B : FiniteFamily P S) (b : B.Carrier) : (A.coprod B).Carrier :=
  ⟨Fin.natAdd A.tags b.1, ⟨b.2.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using b.2.property⟩⟩

def familyCoprodDecode (A B : FiniteFamily P S) (x : (A.coprod B).Carrier) : A.Carrier ⊕ B.Carrier := by
  obtain ⟨i, a⟩ := x
  refine (Fin.addCases (motive := fun i => (A.coprod B).piece i → A.Carrier ⊕ B.Carrier) ?_ ?_ i) a
  · intro i a
    exact Sum.inl ⟨i, ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using a.property⟩⟩
  · intro j b
    exact Sum.inr ⟨j, ⟨b.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using b.property⟩⟩

@[simp] theorem familyCoprodDecode_inl (A B : FiniteFamily P S) (a : A.Carrier) :
    familyCoprodDecode A B (familyCoprodInl A B a) = Sum.inl a := by
  cases a
  simp only [familyCoprodDecode, familyCoprodInl, Fin.addCases_left]

@[simp] theorem familyCoprodDecode_inr (A B : FiniteFamily P S) (b : B.Carrier) :
    familyCoprodDecode A B (familyCoprodInr A B b) = Sum.inr b := by
  cases b
  simp only [familyCoprodDecode, familyCoprodInr, Fin.addCases_right]

def familyCoprodEncode (A B : FiniteFamily P S) : A.Carrier ⊕ B.Carrier → (A.coprod B).Carrier :=
  Sum.elim (familyCoprodInl A B) (familyCoprodInr A B)

theorem familyCoprodEncode_decode (A B : FiniteFamily P S) (x : (A.coprod B).Carrier) :
    familyCoprodEncode A B (familyCoprodDecode A B x) = x := by
  obtain ⟨i, a⟩ := x
  revert a
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · intro a
    simp only [familyCoprodDecode, Fin.addCases_left, familyCoprodEncode, Sum.elim_inl, familyCoprodInl]
  · intro b
    simp only [familyCoprodDecode, Fin.addCases_right, familyCoprodEncode, Sum.elim_inr, familyCoprodInr]

def familyCoprodEquiv (A B : FiniteFamily P S) : (A.coprod B).Carrier ≃ A.Carrier ⊕ B.Carrier where
  toFun := familyCoprodDecode A B
  invFun := familyCoprodEncode A B
  left_inv := familyCoprodEncode_decode A B
  right_inv x := by
    cases x with
    | inl a => exact familyCoprodDecode_inl A B a
    | inr b => exact familyCoprodDecode_inr A B b

end DiamondIntegral.Section3
