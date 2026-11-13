import «section 3».MeasuredGammaRVLift

/-! A genuine Gamma contraction witness gives a pointwise Gamma-measured
RV isomorphism of the full code lifts. No almost-everywhere RV convention
or parameter choice is introduced. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def gammaCodeFamilyBijection {A B : GammaObject hc S k} (F : FamilyBijection A.codeLift B.codeLift) :
    DefinableBijection A.rvLift.domain B.rvLift.domain :=
  (B.rvCodeBijection.comp (F.comp A.rvCodeBijection.symm)).rvRealization

theorem gammaCodeFamilyBijection_encode {A B : GammaObject hc S k}
    (F : FamilyBijection A.codeLift B.codeLift) (c : A.codeLift.Carrier) :
    (gammaCodeFamilyBijection F).map (A.rvEncodeCode c) = B.rvEncodeCode (F.equiv c) := by
  let G := B.rvCodeBijection.comp (F.comp A.rvCodeBijection.symm)
  calc
    _ = B.rvPieces.rvEncode (G.equiv (A.rvCodeBijection.equiv c)) :=
      rvFamilyMap_encode G.equiv G.definable (A.rvCodeBijection.equiv c)
    _ = _ := by
      apply congrArg B.rvPieces.rvEncode
      change B.rvCodeBijection.equiv
        (F.equiv (A.rvCodeBijection.equiv.symm (A.rvCodeBijection.equiv c))) = _
      rw [Equiv.symm_apply_apply]

def measuredGammaRVHom {A B : MeasuredGammaObject hc S k} (f : A ⟶ B) :
    MeasuredRVHom A.rvLift B.rvLift := by
  let F := Classical.choose f.underlying.contraction
  have hF := Classical.choose_spec f.underlying.contraction
  refine ⟨gammaCodeFamilyBijection F, ?_⟩
  intro a
  obtain ⟨c, rfl⟩ := A.underlying.rvEncodeCode_surjective a
  rw [gammaCodeFamilyBijection_encode, measuredGammaLift_combined, measuredGammaLift_combined, hF]
  exact f.preserves (A.underlying.decode c)

theorem measuredGammaHom_lift_iso {A B : MeasuredGammaObject hc S k} (f : A ⟶ B) :
    Nonempty (A.rvLift ≅ B.rvLift) := ⟨asIso (show A.rvLift ⟶ B.rvLift from measuredGammaRVHom f)⟩

theorem measuredFiniteGammaHom_lift_iso {A B : MeasuredFiniteGammaObject hc S k} (f : A ⟶ B) :
    Nonempty (A.resLift ≅ B.resLift) := by
  obtain ⟨e⟩ := measuredGammaHom_lift_iso f.hom
  exact ⟨(measuredResProperty S k).isoMk e⟩

end DiamondIntegral.Section3
