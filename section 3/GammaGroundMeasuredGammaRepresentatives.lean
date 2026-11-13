import «section 3».GammaGroundMeasuredGammaPartitions
import «section 3».GammaGroundGammaCoproductCuts
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredGammaRestriction_combined (A : GammaGroundMeasuredGammaObject hc ground k)
    (X : Fin A.underlying.tags → GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k)))
    (hX : ∀ i, (X i).carrier ⊆ (A.underlying.piece i).carrier)
    (a : (A.underlying.restrict X).Carrier) :
    (A.restrict X hX).combinedWeight a = A.combinedWeight ⟨a.1, GammaGroundMap.inclusion (hX a.1) a.2⟩ := rfl

def gammaGroundMeasuredGammaCoprodLeftCutHom (A B : GammaGroundMeasuredGammaObject hc ground k) :
    GammaGroundMeasuredGammaHom ((A.coprod B).restrict (gammaGroundGammaCoprodLeftCut A.underlying B.underlying)
      (gammaGroundGammaCoprodLeftCut_subset A.underlying B.underlying)) A where
  underlying := (gammaGroundGammaCoprodLeftCutIso A.underlying B.underlying).hom
  preserves x := by
    rcases x with ⟨i, x⟩
    revert x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro x
      let a : A.underlying.Carrier := ⟨i, ⟨x.val, by
        simpa only [GammaGroundMeasuredGammaObject.restrict, GammaGroundGammaObject.restrict, gammaGroundGammaCoprodLeftCut, Fin.addCases_left] using x.property⟩⟩
      have hm : (gammaGroundGammaCoprodLeftCutIso A.underlying B.underlying).hom.bijection.equiv
          ⟨Fin.castAdd B.underlying.tags i, x⟩ = a := by
        exact gammaGroundFamilyCoprodDropEmpty_inl A.underlying B.underlying.emptyPieces (fun _ => rfl) a
      calc
        _ = (A.coprod B).combinedWeight
            (gammaGroundFamilyCoprodInl A.underlying B.underlying a) := rfl
        _ = A.combinedWeight a := gammaGroundMeasuredGammaCoprod_combined_left A B a
        _ = _ := congrArg A.combinedWeight hm.symm
    · intro x
      exact False.elim (by
        have hx := x.property
        simpa only [GammaGroundMeasuredGammaObject.restrict, GammaGroundGammaObject.restrict, gammaGroundGammaCoprodLeftCut, Fin.addCases_right, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty, Set.mem_empty_iff_false] using hx)

def gammaGroundMeasuredGammaCoprodRightCutHom (A B : GammaGroundMeasuredGammaObject hc ground k) :
    GammaGroundMeasuredGammaHom ((A.coprod B).restrict
      ((A.coprod B).underlying.difference (gammaGroundGammaCoprodLeftCut A.underlying B.underlying))
      (fun _ _ h => h.1)) B where
  underlying := (gammaGroundGammaCoprodRightCutIso A.underlying B.underlying).hom
  preserves x := by
    rcases x with ⟨i, x⟩
    revert x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro x
      have hx := x.property
      change x.val ∈ ((A.underlying.coprod B.underlying).piece (Fin.castAdd B.underlying.tags i)).carrier ∧
        x.val ∉ (gammaGroundGammaCoprodLeftCut A.underlying B.underlying (Fin.castAdd B.underlying.tags i)).carrier at hx
      simp only [GammaGroundFiniteFamily.coprod, Fin.addCases_left, gammaGroundGammaCoprodLeftCut] at hx
      exact False.elim (hx.2 hx.1)
    · intro x
      have hx : x.val ∈ (B.underlying.piece j).carrier := by
        have hh := x.property
        change x.val ∈ ((A.underlying.coprod B.underlying).piece (Fin.natAdd A.underlying.tags j)).carrier ∧ _ at hh
        simpa only [GammaGroundFiniteFamily.coprod, Fin.addCases_right] using hh.1
      let b : B.underlying.Carrier := ⟨j, ⟨x.val, hx⟩⟩
      have hm : (gammaGroundGammaCoprodRightCutIso A.underlying B.underlying).hom.bijection.equiv
          ⟨Fin.natAdd A.underlying.tags j, x⟩ = b := by
        change gammaGroundFamilyCoprodDropEmpty B.underlying A.underlying.emptyPieces (fun _ => rfl) _ = b
        rw [← gammaGroundFamilyCoprodDropEmpty_inl B.underlying A.underlying.emptyPieces (fun _ => rfl) b]
        apply congrArg (gammaGroundFamilyCoprodDropEmpty B.underlying A.underlying.emptyPieces (fun _ => rfl))
        apply gammaGroundFamilyCarrier_ext _
        · exact finAddFlip_apply_natAdd j A.underlying.tags
        · rfl
      calc
        _ = (A.coprod B).combinedWeight
            (gammaGroundFamilyCoprodInr A.underlying B.underlying b) := rfl
        _ = B.combinedWeight b := gammaGroundMeasuredGammaCoprod_combined_right A B b
        _ = _ := congrArg B.combinedWeight hm.symm

theorem gammaGroundMeasuredGammaClass_coprod (A B : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaClass (A.coprod B) = gammaGroundMeasuredGammaClass A + gammaGroundMeasuredGammaClass B := by
  have hs := gammaGroundMeasuredGammaClass_scissor (A.coprod B)
    (gammaGroundGammaCoprodLeftCut A.underlying B.underlying)
    (gammaGroundGammaCoprodLeftCut_subset A.underlying B.underlying)
  have hA := gammaGroundMeasuredGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaCoprodLeftCutHom A B))
  have hB := gammaGroundMeasuredGammaClass_iso (asIso (show _ ⟶ _ from gammaGroundMeasuredGammaCoprodRightCutHom A B))
  rw [hA, hB] at hs
  exact hs.symm

theorem gammaGroundMeasuredGammaClass_surjective :
    Function.Surjective (gammaGroundMeasuredGammaClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundMeasuredGammaPresentation hc ground k)
    GammaGroundMeasuredGammaObject.coprod gammaGroundMeasuredGammaClass_coprod

end DiamondIntegral.Section3
