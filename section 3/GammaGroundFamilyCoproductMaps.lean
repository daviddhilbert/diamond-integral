import «section 3».GammaGroundFamilyCoproductEquiv
/-! Disjoint union preserves actual definable gammaGroundFamily bijections. -/
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
variable {P Q : Space LRV M}

@[simp] theorem gammaGroundFamilyCoprodInl_inj (A B : GammaGroundFiniteFamily hc ground P) (a b : A.Carrier) :
    gammaGroundFamilyCoprodInl A B a = gammaGroundFamilyCoprodInl A B b ↔ a = b := by
  constructor
  · intro h
    exact Sum.inl.inj (by simpa only [gammaGroundFamilyCoprodDecode_inl] using congrArg (gammaGroundFamilyCoprodDecode A B) h)
  · exact congrArg _

@[simp] theorem gammaGroundFamilyCoprodInr_inj (A B : GammaGroundFiniteFamily hc ground P) (a b : B.Carrier) :
    gammaGroundFamilyCoprodInr A B a = gammaGroundFamilyCoprodInr A B b ↔ a = b := by
  constructor
  · intro h
    exact Sum.inr.inj (by simpa only [gammaGroundFamilyCoprodDecode_inr] using congrArg (gammaGroundFamilyCoprodDecode A B) h)
  · exact congrArg _

@[simp] theorem gammaGroundFamilyCoprodInl_ne_inr (A B : GammaGroundFiniteFamily hc ground P) (a : A.Carrier) (b : B.Carrier) :
    gammaGroundFamilyCoprodInl A B a ≠ gammaGroundFamilyCoprodInr A B b := by
  intro h
  have ht := congrArg (gammaGroundFamilyCoprodDecode A B) h
  simpa only [gammaGroundFamilyCoprodDecode_inl, gammaGroundFamilyCoprodDecode_inr, Sum.inl_ne_inr] using ht

def gammaGroundFamilyCoprodMapEquiv {A B : GammaGroundFiniteFamily hc ground P} {A' B' : GammaGroundFiniteFamily hc ground Q}
    (f : GammaGroundFamilyBijection A A') (g : GammaGroundFamilyBijection B B') : (A.coprod B).Carrier ≃ (A'.coprod B').Carrier :=
  (gammaGroundFamilyCoprodEquiv A B).trans ((Equiv.sumCongr f.equiv g.equiv).trans (gammaGroundFamilyCoprodEquiv A' B').symm)

@[simp] theorem gammaGroundFamilyCoprodMapEquiv_inl {A B : GammaGroundFiniteFamily hc ground P} {A' B' : GammaGroundFiniteFamily hc ground Q}
    (f : GammaGroundFamilyBijection A A') (g : GammaGroundFamilyBijection B B') (a : A.Carrier) :
    gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInl A B a) = gammaGroundFamilyCoprodInl A' B' (f.equiv a) := by
  change gammaGroundFamilyCoprodEncode A' B' (Sum.map f.equiv g.equiv
    (gammaGroundFamilyCoprodDecode A B (gammaGroundFamilyCoprodInl A B a))) = _
  rw [gammaGroundFamilyCoprodDecode_inl]
  rfl

@[simp] theorem gammaGroundFamilyCoprodMapEquiv_inr {A B : GammaGroundFiniteFamily hc ground P} {A' B' : GammaGroundFiniteFamily hc ground Q}
    (f : GammaGroundFamilyBijection A A') (g : GammaGroundFamilyBijection B B') (b : B.Carrier) :
    gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInr A B b) = gammaGroundFamilyCoprodInr A' B' (g.equiv b) := by
  change gammaGroundFamilyCoprodEncode A' B' (Sum.map f.equiv g.equiv
    (gammaGroundFamilyCoprodDecode A B (gammaGroundFamilyCoprodInr A B b))) = _
  rw [gammaGroundFamilyCoprodDecode_inr]
  rfl

theorem gammaGroundFamilyCoprodMapEquiv_definable {A B : GammaGroundFiniteFamily hc ground P} {A' B' : GammaGroundFiniteFamily hc ground Q}
    (f : GammaGroundFamilyBijection A A') (g : GammaGroundFamilyBijection B B') :
    GammaGroundFamilyDefinable (A.coprod B) (A'.coprod B') (gammaGroundFamilyCoprodMapEquiv f g) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · exact (f.definable i j).congr (by
        intro x y
        constructor
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : (A.coprod B).piece (Fin.castAdd B.tags i) :=
            ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.property⟩
          let b' : (A'.coprod B').piece (Fin.castAdd B'.tags j) :=
            ⟨b.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using b.property⟩
          refine ⟨a', b', hx, hy, ?_⟩
          change gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInl A B ⟨i, a⟩) = gammaGroundFamilyCoprodInl A' B' ⟨j, b⟩
          rw [gammaGroundFamilyCoprodMapEquiv_inl, he]
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : A.piece i := ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.property⟩
          let b' : A'.piece j := ⟨b.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using b.property⟩
          have he' : gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInl A B ⟨i, a'⟩) = gammaGroundFamilyCoprodInl A' B' ⟨j, b'⟩ := he
          rw [gammaGroundFamilyCoprodMapEquiv_inl] at he'
          exact ⟨a', b', hx, hy, (gammaGroundFamilyCoprodInl_inj _ _ _ _).mp he'⟩)
    · have hd : GammaGroundRelationDefinable hc ground P Q (fun _ _ => False) := by
        exact (GammaGroundDefSet.empty hc ground (P.prod Q)).definable
      exact hd.congr (by
        intro x y
        constructor
        · exact False.elim
        · rintro ⟨a, b, _, _, he⟩
          let a' : A.piece i := ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.property⟩
          let b' : B'.piece j := ⟨b.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using b.property⟩
          have he' : gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInl A B ⟨i, a'⟩) = gammaGroundFamilyCoprodInr A' B' ⟨j, b'⟩ := he
          rw [gammaGroundFamilyCoprodMapEquiv_inl] at he'
          exact gammaGroundFamilyCoprodInl_ne_inr _ _ _ _ he')
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hd : GammaGroundRelationDefinable hc ground P Q (fun _ _ => False) := by
        exact (GammaGroundDefSet.empty hc ground (P.prod Q)).definable
      exact hd.congr (by
        intro x y
        constructor
        · exact False.elim
        · rintro ⟨a, b, _, _, he⟩
          let a' : B.piece i := ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using a.property⟩
          let b' : A'.piece j := ⟨b.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using b.property⟩
          have he' : gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInr A B ⟨i, a'⟩) = gammaGroundFamilyCoprodInl A' B' ⟨j, b'⟩ := he
          rw [gammaGroundFamilyCoprodMapEquiv_inr] at he'
          exact gammaGroundFamilyCoprodInl_ne_inr _ _ _ _ he'.symm)
    · exact (g.definable i j).congr (by
        intro x y
        constructor
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : (A.coprod B).piece (Fin.natAdd A.tags i) :=
            ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using a.property⟩
          let b' : (A'.coprod B').piece (Fin.natAdd A'.tags j) :=
            ⟨b.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using b.property⟩
          refine ⟨a', b', hx, hy, ?_⟩
          change gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInr A B ⟨i, a⟩) = gammaGroundFamilyCoprodInr A' B' ⟨j, b⟩
          rw [gammaGroundFamilyCoprodMapEquiv_inr, he]
        · rintro ⟨a, b, hx, hy, he⟩
          let a' : B.piece i := ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using a.property⟩
          let b' : B'.piece j := ⟨b.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using b.property⟩
          have he' : gammaGroundFamilyCoprodMapEquiv f g (gammaGroundFamilyCoprodInr A B ⟨i, a'⟩) = gammaGroundFamilyCoprodInr A' B' ⟨j, b'⟩ := he
          rw [gammaGroundFamilyCoprodMapEquiv_inr] at he'
          exact ⟨a', b', hx, hy, (gammaGroundFamilyCoprodInr_inj _ _ _ _).mp he'⟩)

def GammaGroundFamilyBijection.coprod {A B : GammaGroundFiniteFamily hc ground P} {A' B' : GammaGroundFiniteFamily hc ground Q}
    (f : GammaGroundFamilyBijection A A') (g : GammaGroundFamilyBijection B B') : GammaGroundFamilyBijection (A.coprod B) (A'.coprod B') :=
  ⟨gammaGroundFamilyCoprodMapEquiv f g, gammaGroundFamilyCoprodMapEquiv_definable f g⟩

end DiamondIntegral.Section3
