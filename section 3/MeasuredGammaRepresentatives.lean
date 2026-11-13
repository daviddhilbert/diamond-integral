import «section 3».MeasuredGammaPartitions

/-! Measured Gamma sums are represented by the actual tagged union,
with the original forms inherited on both pieces. -/
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

theorem measuredGammaRestriction_combined (A : MeasuredGammaObject hc S k)
    (X : Fin A.underlying.tags → DefSet ((volumeGammaSpace hc).power (Fin k)) S)
    (hX : ∀ i, (X i).carrier ⊆ (A.underlying.piece i).carrier)
    (a : (A.underlying.restrict X).Carrier) :
    (A.restrict X hX).combinedWeight a = A.combinedWeight ⟨a.1, Map.inclusion (hX a.1) a.2⟩ := rfl

def measuredGammaCoprodLeftCutHom (A B : MeasuredGammaObject hc S k) :
    MeasuredGammaHom ((A.coprod B).restrict (gammaCoprodLeftCut A.underlying B.underlying)
      (gammaCoprodLeftCut_subset A.underlying B.underlying)) A where
  underlying := (gammaCoprodLeftCutIso A.underlying B.underlying).hom
  preserves x := by
    rcases x with ⟨i, x⟩
    revert x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro x
      let a : A.underlying.Carrier := ⟨i, ⟨x.val, by
        simpa only [MeasuredGammaObject.restrict, GammaObject.restrict, gammaCoprodLeftCut, Fin.addCases_left] using x.property⟩⟩
      have hm : (gammaCoprodLeftCutIso A.underlying B.underlying).hom.bijection.equiv
          ⟨Fin.castAdd B.underlying.tags i, x⟩ = a := by
        exact familyCoprodDropEmpty_inl A.underlying B.underlying.emptyPieces (fun _ => rfl) a
      calc
        _ = (A.coprod B).combinedWeight
            (familyCoprodInl A.underlying B.underlying a) := rfl
        _ = A.combinedWeight a := measuredGammaCoprod_combined_left A B a
        _ = _ := congrArg A.combinedWeight hm.symm
    · intro x
      exact False.elim (by
        have hx := x.property
        simpa only [MeasuredGammaObject.restrict, GammaObject.restrict, gammaCoprodLeftCut, Fin.addCases_right, DefSet.empty, Set.mem_empty_iff_false] using hx)

def measuredGammaCoprodRightCutHom (A B : MeasuredGammaObject hc S k) :
    MeasuredGammaHom ((A.coprod B).restrict
      ((A.coprod B).underlying.difference (gammaCoprodLeftCut A.underlying B.underlying))
      (fun _ _ h => h.1)) B where
  underlying := (gammaCoprodRightCutIso A.underlying B.underlying).hom
  preserves x := by
    rcases x with ⟨i, x⟩
    revert x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro x
      have hx := x.property
      change x.val ∈ ((A.underlying.coprod B.underlying).piece (Fin.castAdd B.underlying.tags i)).carrier ∧
        x.val ∉ (gammaCoprodLeftCut A.underlying B.underlying (Fin.castAdd B.underlying.tags i)).carrier at hx
      simp only [FiniteFamily.coprod, Fin.addCases_left, gammaCoprodLeftCut] at hx
      exact False.elim (hx.2 hx.1)
    · intro x
      have hx : x.val ∈ (B.underlying.piece j).carrier := by
        have hh := x.property
        change x.val ∈ ((A.underlying.coprod B.underlying).piece (Fin.natAdd A.underlying.tags j)).carrier ∧ _ at hh
        simpa only [FiniteFamily.coprod, Fin.addCases_right] using hh.1
      let b : B.underlying.Carrier := ⟨j, ⟨x.val, hx⟩⟩
      have hm : (gammaCoprodRightCutIso A.underlying B.underlying).hom.bijection.equiv
          ⟨Fin.natAdd A.underlying.tags j, x⟩ = b := by
        change familyCoprodDropEmpty B.underlying A.underlying.emptyPieces (fun _ => rfl) _ = b
        rw [← familyCoprodDropEmpty_inl B.underlying A.underlying.emptyPieces (fun _ => rfl) b]
        apply congrArg (familyCoprodDropEmpty B.underlying A.underlying.emptyPieces (fun _ => rfl))
        apply familyCarrier_ext _
        · exact finAddFlip_apply_natAdd j A.underlying.tags
        · rfl
      calc
        _ = (A.coprod B).combinedWeight
            (familyCoprodInr A.underlying B.underlying b) := rfl
        _ = B.combinedWeight b := measuredGammaCoprod_combined_right A B b
        _ = _ := congrArg B.combinedWeight hm.symm

theorem measuredGammaClass_coprod (A B : MeasuredGammaObject hc S k) :
    measuredGammaClass (A.coprod B) = measuredGammaClass A + measuredGammaClass B := by
  have hs := measuredGammaClass_scissor (A.coprod B)
    (gammaCoprodLeftCut A.underlying B.underlying)
    (gammaCoprodLeftCut_subset A.underlying B.underlying)
  have hA := measuredGammaClass_iso (asIso (show _ ⟶ _ from measuredGammaCoprodLeftCutHom A B))
  have hB := measuredGammaClass_iso (asIso (show _ ⟶ _ from measuredGammaCoprodRightCutHom A B))
  rw [hA, hB] at hs
  exact hs.symm

theorem measuredGammaClass_surjective :
    Function.Surjective (measuredGammaClass (M := M) (hc := hc) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (measuredGammaPresentation hc S k)
    MeasuredGammaObject.coprod measuredGammaClass_coprod

end DiamondIntegral.Section3
