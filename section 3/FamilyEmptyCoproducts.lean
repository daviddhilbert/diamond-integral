import «section 3».FamilyPartitions

/-! Empty pieces may be removed from a tagged disjoint union through a
genuine definable bijection, even when an entire family has zero tags. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P : Space L M}

def familyCoprodDropEmpty (A B : FiniteFamily P S) (hB : ∀ i, (B.piece i).carrier = ∅)
    (x : (A.coprod B).Carrier) : A.Carrier :=
  match familyCoprodDecode A B x with
  | .inl a => a
  | .inr b => False.elim (Set.notMem_empty b.2.val (hB b.1 ▸ b.2.property))

@[simp] theorem familyCoprodDropEmpty_inl (A B : FiniteFamily P S) (hB : ∀ i, (B.piece i).carrier = ∅)
    (a : A.Carrier) : familyCoprodDropEmpty A B hB (familyCoprodInl A B a) = a := by
  unfold familyCoprodDropEmpty
  rw [familyCoprodDecode_inl]

def familyCoprodDropEmptyEquiv (A B : FiniteFamily P S) (hB : ∀ i, (B.piece i).carrier = ∅) :
    (A.coprod B).Carrier ≃ A.Carrier where
  toFun := familyCoprodDropEmpty A B hB
  invFun := familyCoprodInl A B
  left_inv x := by
    rcases familyCoprod_cases A B x with ⟨a, rfl⟩ | ⟨b, _⟩
    · rw [familyCoprodDropEmpty_inl]
    · exact False.elim (Set.notMem_empty b.2.val (hB b.1 ▸ b.2.property))
  right_inv := familyCoprodDropEmpty_inl A B hB

theorem familyCoprodDropEmpty_definable (A B : FiniteFamily P S) (hB : ∀ i, (B.piece i).carrier = ∅) :
    FamilyDefinable (A.coprod B) A (familyCoprodDropEmpty A B hB) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact (FamilyDefinable.id A i j).congr P P (by
      intro x y
      constructor
      · rintro ⟨a, b, hx, hy, he⟩
        let a' : (A.coprod B).piece (Fin.castAdd B.tags i) :=
          ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using a.property⟩
        refine ⟨a', b, hx, hy, ?_⟩
        change familyCoprodDropEmpty A B hB (familyCoprodInl A B ⟨i, a⟩) = ⟨j, b⟩
        rw [familyCoprodDropEmpty_inl]
        exact he
      · rintro ⟨a, b, hx, hy, he⟩
        let a' : A.piece i := ⟨a.val, by simpa only [FiniteFamily.coprod, Fin.addCases_left] using a.property⟩
        have he' : familyCoprodDropEmpty A B hB (familyCoprodInl A B ⟨i, a'⟩) = ⟨j, b⟩ := he
        rw [familyCoprodDropEmpty_inl] at he'
        exact ⟨a', b, hx, hy, he'⟩)
  · have hd : P.RelationDefinable P S (fun _ _ => False) := by
      change S.Definable L _
      simp [Space.relation]
    exact hd.congr P P (by
      intro x y
      constructor
      · exact False.elim
      · rintro ⟨a, _, _, _, _⟩
        have ha : a.val ∈ (B.piece i).carrier := by
          simpa only [FiniteFamily.coprod, Fin.addCases_right] using a.property
        exact Set.notMem_empty a.val (hB i ▸ ha))

def familyCoprodEmptyRightBijection (A B : FiniteFamily P S) (hB : ∀ i, (B.piece i).carrier = ∅) :
    FamilyBijection (A.coprod B) A := ⟨familyCoprodDropEmptyEquiv A B hB, familyCoprodDropEmpty_definable A B hB⟩

end DiamondIntegral.Section3
