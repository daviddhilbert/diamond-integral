import «section 3».GammaGroundMeasuredGammaRVLift
/-! A genuine Gamma contraction witness gives a pointwise Gamma-measured
RV isomorphism of the full code lifts. No almost-everywhere RV convention
or parameter choice is introduced. -/

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

def gammaGroundGammaCodeFamilyBijection {A B : GammaGroundGammaObject hc ground k} (F : GammaGroundFamilyBijection A.codeLift B.codeLift) :
    GammaGroundBijection A.rvLift.domain B.rvLift.domain :=
  (B.rvCodeBijection.comp (F.comp A.rvCodeBijection.symm)).rvRealization

theorem gammaGroundGammaCodeFamilyBijection_encode {A B : GammaGroundGammaObject hc ground k}
    (F : GammaGroundFamilyBijection A.codeLift B.codeLift) (c : A.codeLift.Carrier) :
    (gammaGroundGammaCodeFamilyBijection F).map (A.rvEncodeCode c) = B.rvEncodeCode (F.equiv c) := by
  let G := B.rvCodeBijection.comp (F.comp A.rvCodeBijection.symm)
  calc
    _ = B.rvPieces.rvEncode (G.equiv (A.rvCodeBijection.equiv c)) :=
      gammaGroundRVFamilyMap_encode G.equiv G.definable (A.rvCodeBijection.equiv c)
    _ = _ := by
      apply congrArg B.rvPieces.rvEncode
      change B.rvCodeBijection.equiv
        (F.equiv (A.rvCodeBijection.equiv.symm (A.rvCodeBijection.equiv c))) = _
      rw [Equiv.symm_apply_apply]

def gammaGroundMeasuredGammaRVHom {A B : GammaGroundMeasuredGammaObject hc ground k} (f : A ⟶ B) :
    GammaGroundMeasuredRVHom A.rvLift B.rvLift := by
  let F := Classical.choose f.underlying.contraction
  have hF := Classical.choose_spec f.underlying.contraction
  refine ⟨gammaGroundGammaCodeFamilyBijection F, ?_⟩
  intro a
  obtain ⟨c, rfl⟩ := A.underlying.rvEncodeCode_surjective a
  rw [gammaGroundGammaCodeFamilyBijection_encode, gammaGroundMeasuredGammaLift_combined, gammaGroundMeasuredGammaLift_combined, hF]
  exact f.preserves (A.underlying.decode c)

theorem gammaGroundMeasuredGammaHom_lift_iso {A B : GammaGroundMeasuredGammaObject hc ground k} (f : A ⟶ B) :
    Nonempty (A.rvLift ≅ B.rvLift) := ⟨asIso (show A.rvLift ⟶ B.rvLift from gammaGroundMeasuredGammaRVHom f)⟩

theorem gammaGroundMeasuredFiniteGammaHom_lift_iso {A B : GammaGroundMeasuredFiniteGammaObject hc ground k} (f : A ⟶ B) :
    Nonempty (A.resLift ≅ B.resLift) := by
  obtain ⟨e⟩ := gammaGroundMeasuredGammaHom_lift_iso f.hom
  exact ⟨(gammaGroundMeasuredResProperty (hc := hc) (ground := ground) (k := k)).isoMk e⟩

end DiamondIntegral.Section3
