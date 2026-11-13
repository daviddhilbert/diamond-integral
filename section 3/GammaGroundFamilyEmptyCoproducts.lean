import «section 3».GammaGroundFamilyPartitions
/-! Empty pieces may be removed from a tagged disjoint union through a
genuine definable bijection, even when an entire gammaGroundFamily has zero tags. -/
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

def gammaGroundFamilyCoprodDropEmpty (A B : GammaGroundFiniteFamily hc ground P) (hB : ∀ i, (B.piece i).carrier = ∅)
    (x : (A.coprod B).Carrier) : A.Carrier :=
  match gammaGroundFamilyCoprodDecode A B x with
  | .inl a => a
  | .inr b => False.elim (Set.notMem_empty b.2.val (hB b.1 ▸ b.2.property))

@[simp] theorem gammaGroundFamilyCoprodDropEmpty_inl (A B : GammaGroundFiniteFamily hc ground P) (hB : ∀ i, (B.piece i).carrier = ∅)
    (a : A.Carrier) : gammaGroundFamilyCoprodDropEmpty A B hB (gammaGroundFamilyCoprodInl A B a) = a := by
  unfold gammaGroundFamilyCoprodDropEmpty
  rw [gammaGroundFamilyCoprodDecode_inl]

def gammaGroundFamilyCoprodDropEmptyEquiv (A B : GammaGroundFiniteFamily hc ground P) (hB : ∀ i, (B.piece i).carrier = ∅) :
    (A.coprod B).Carrier ≃ A.Carrier where
  toFun := gammaGroundFamilyCoprodDropEmpty A B hB
  invFun := gammaGroundFamilyCoprodInl A B
  left_inv x := by
    rcases gammaGroundFamilyCoprod_cases A B x with ⟨a, rfl⟩ | ⟨b, _⟩
    · rw [gammaGroundFamilyCoprodDropEmpty_inl]
    · exact False.elim (Set.notMem_empty b.2.val (hB b.1 ▸ b.2.property))
  right_inv := gammaGroundFamilyCoprodDropEmpty_inl A B hB

theorem gammaGroundFamilyCoprodDropEmpty_definable (A B : GammaGroundFiniteFamily hc ground P) (hB : ∀ i, (B.piece i).carrier = ∅) :
    GammaGroundFamilyDefinable (A.coprod B) A (gammaGroundFamilyCoprodDropEmpty A B hB) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact (GammaGroundFamilyDefinable.id A i j).congr (by
      intro x y
      constructor
      · rintro ⟨a, b, hx, hy, he⟩
        let a' : (A.coprod B).piece (Fin.castAdd B.tags i) :=
          ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.property⟩
        refine ⟨a', b, hx, hy, ?_⟩
        change gammaGroundFamilyCoprodDropEmpty A B hB (gammaGroundFamilyCoprodInl A B ⟨i, a⟩) = ⟨j, b⟩
        rw [gammaGroundFamilyCoprodDropEmpty_inl]
        exact he
      · rintro ⟨a, b, hx, hy, he⟩
        let a' : A.piece i := ⟨a.val, by simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_left] using a.property⟩
        have he' : gammaGroundFamilyCoprodDropEmpty A B hB (gammaGroundFamilyCoprodInl A B ⟨i, a'⟩) = ⟨j, b⟩ := he
        rw [gammaGroundFamilyCoprodDropEmpty_inl] at he'
        exact ⟨a', b, hx, hy, he'⟩)
  · have hd : GammaGroundRelationDefinable hc ground P P (fun _ _ => False) := by
      exact (GammaGroundDefSet.empty hc ground (P.prod P)).definable
    exact hd.congr (by
      intro x y
      constructor
      · exact False.elim
      · rintro ⟨a, _, _, _, _⟩
        have ha : a.val ∈ (B.piece i).carrier := by
          simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using a.property
        exact Set.notMem_empty a.val (hB i ▸ ha))

def gammaGroundFamilyCoprodEmptyRightBijection (A B : GammaGroundFiniteFamily hc ground P) (hB : ∀ i, (B.piece i).carrier = ∅) :
    GammaGroundFamilyBijection (A.coprod B) A := ⟨gammaGroundFamilyCoprodDropEmptyEquiv A B hB, gammaGroundFamilyCoprodDropEmpty_definable A B hB⟩

end DiamondIntegral.Section3
