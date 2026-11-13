import «section 3».FamilyCoproductEquiv

/-! Disjoint union preserves actual definable family bijections. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P Q : Space L M}

@[simp] theorem familyCoprodInl_inj (A B : FiniteFamily P S) (a b : A.Carrier) :
    familyCoprodInl A B a = familyCoprodInl A B b ↔ a = b := by
  constructor
  · intro h
    exact Sum.inl.inj (by simpa only [familyCoprodDecode_inl] using congrArg (familyCoprodDecode A B) h)
  · exact congrArg _

@[simp] theorem familyCoprodInr_inj (A B : FiniteFamily P S) (a b : B.Carrier) :
    familyCoprodInr A B a = familyCoprodInr A B b ↔ a = b := by
  constructor
  · intro h
    exact Sum.inr.inj (by simpa only [familyCoprodDecode_inr] using congrArg (familyCoprodDecode A B) h)
  · exact congrArg _

@[simp] theorem familyCoprodInl_ne_inr (A B : FiniteFamily P S) (a : A.Carrier) (b : B.Carrier) :
    familyCoprodInl A B a ≠ familyCoprodInr A B b := by
  intro h
  have ht := congrArg (familyCoprodDecode A B) h
  simpa only [familyCoprodDecode_inl, familyCoprodDecode_inr, Sum.inl_ne_inr] using ht

def familyCoprodMapEquiv {A B : FiniteFamily P S} {A' B' : FiniteFamily Q S}
    (f : FamilyBijection A A') (g : FamilyBijection B B') : (A.coprod B).Carrier ≃ (A'.coprod B').Carrier :=
  (familyCoprodEquiv A B).trans ((Equiv.sumCongr f.equiv g.equiv).trans (familyCoprodEquiv A' B').symm)

@[simp] theorem familyCoprodMapEquiv_inl {A B : FiniteFamily P S} {A' B' : FiniteFamily Q S}
    (f : FamilyBijection A A') (g : FamilyBijection B B') (a : A.Carrier) :
    familyCoprodMapEquiv f g (familyCoprodInl A B a) = familyCoprodInl A' B' (f.equiv a) := by
  change familyCoprodEncode A' B' (Sum.map f.equiv g.equiv
    (familyCoprodDecode A B (familyCoprodInl A B a))) = _
  rw [familyCoprodDecode_inl]
  rfl

@[simp] theorem familyCoprodMapEquiv_inr {A B : FiniteFamily P S} {A' B' : FiniteFamily Q S}
    (f : FamilyBijection A A') (g : FamilyBijection B B') (b : B.Carrier) :
    familyCoprodMapEquiv f g (familyCoprodInr A B b) = familyCoprodInr A' B' (g.equiv b) := by
  change familyCoprodEncode A' B' (Sum.map f.equiv g.equiv
    (familyCoprodDecode A B (familyCoprodInr A B b))) = _
  rw [familyCoprodDecode_inr]
  rfl

theorem familyCoprodMapEquiv_definable {A B : FiniteFamily P S} {A' B' : FiniteFamily Q S}
    (f : FamilyBijection A A') (g : FamilyBijection B B') :
    FamilyDefinable (A.coprod B) (A'.coprod B') (familyCoprodMapEquiv f g) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · exact (f.definable i j).congr P Q (by
        intro x y
        constructor
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : (A.coprod B).piece (Fin.castAdd B.tags i) :=
            ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using a.property⟩
          let b' : (A'.coprod B').piece (Fin.castAdd B'.tags j) :=
            ⟨b.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using b.property⟩
          refine ⟨a', b', hx, hy, ?_⟩
          change familyCoprodMapEquiv f g (familyCoprodInl A B ⟨i, a⟩) = familyCoprodInl A' B' ⟨j, b⟩
          rw [familyCoprodMapEquiv_inl, he]
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : A.piece i := ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using a.property⟩
          let b' : A'.piece j := ⟨b.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using b.property⟩
          have he' : familyCoprodMapEquiv f g (familyCoprodInl A B ⟨i, a'⟩) = familyCoprodInl A' B' ⟨j, b'⟩ := he
          rw [familyCoprodMapEquiv_inl] at he'
          exact ⟨a', b', hx, hy, (familyCoprodInl_inj _ _ _ _).mp he'⟩)
    · have hd : P.RelationDefinable Q S (fun _ _ => False) := by
        change S.Definable L _
        simp [Space.relation]
      exact hd.congr P Q (by
        intro x y
        constructor
        · exact False.elim
        · rintro ⟨a, b, _, _, he⟩
          let a' : A.piece i := ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using a.property⟩
          let b' : B'.piece j := ⟨b.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using b.property⟩
          have he' : familyCoprodMapEquiv f g (familyCoprodInl A B ⟨i, a'⟩) = familyCoprodInr A' B' ⟨j, b'⟩ := he
          rw [familyCoprodMapEquiv_inl] at he'
          exact familyCoprodInl_ne_inr _ _ _ _ he')
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hd : P.RelationDefinable Q S (fun _ _ => False) := by
        change S.Definable L _
        simp [Space.relation]
      exact hd.congr P Q (by
        intro x y
        constructor
        · exact False.elim
        · rintro ⟨a, b, _, _, he⟩
          let a' : B.piece i := ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using a.property⟩
          let b' : A'.piece j := ⟨b.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using b.property⟩
          have he' : familyCoprodMapEquiv f g (familyCoprodInr A B ⟨i, a'⟩) = familyCoprodInl A' B' ⟨j, b'⟩ := he
          rw [familyCoprodMapEquiv_inr] at he'
          exact familyCoprodInl_ne_inr _ _ _ _ he'.symm)
    · exact (g.definable i j).congr P Q (by
        intro x y
        constructor
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : (A.coprod B).piece (Fin.natAdd A.tags i) :=
            ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using a.property⟩
          let b' : (A'.coprod B').piece (Fin.natAdd A'.tags j) :=
            ⟨b.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using b.property⟩
          refine ⟨a', b', hx, hy, ?_⟩
          change familyCoprodMapEquiv f g (familyCoprodInr A B ⟨i, a⟩) = familyCoprodInr A' B' ⟨j, b⟩
          rw [familyCoprodMapEquiv_inr, he]
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : B.piece i := ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using a.property⟩
          let b' : B'.piece j := ⟨b.val, by simpa only [FiniteFamily.coprod, Fin.addCases_right] using b.property⟩
          have he' : familyCoprodMapEquiv f g (familyCoprodInr A B ⟨i, a'⟩) = familyCoprodInr A' B' ⟨j, b'⟩ := he
          rw [familyCoprodMapEquiv_inr] at he'
          exact ⟨a', b', hx, hy, (familyCoprodInr_inj _ _ _ _).mp he'⟩)

def FamilyBijection.coprod {A B : FiniteFamily P S} {A' B' : FiniteFamily Q S}
    (f : FamilyBijection A A') (g : FamilyBijection B B') : FamilyBijection (A.coprod B) (A'.coprod B') :=
  ⟨familyCoprodMapEquiv f g, familyCoprodMapEquiv_definable f g⟩

end DiamondIntegral.Section3
