import «section 3».GammaGroundGammaCodeFormRestrictions
import «section 3».GammaGroundGammaVolumeCategories
import «section 3».GammaGroundGammaRVLift
import «section 3».GammaGroundGammaRESLift
import «section 3».GammaGroundRVFamilyDesc
/-! Gamma volume forms lift along every RV representative and the
explicit finite tags. The full invariant graphs remain over the same base. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundGammaObject.rvEncodeCode (A : GammaGroundGammaObject hc ground k) (c : A.codeLift.Carrier) : A.rvLift.domain :=
  A.rvPieces.rvEncode (A.rvCodeBijection.equiv c)

theorem GammaGroundGammaObject.rvEncodeCode_surjective (A : GammaGroundGammaObject hc ground k) :
    Function.Surjective A.rvEncodeCode := by
  intro a
  obtain ⟨b, rfl⟩ := A.rvPieces.rvEquiv.surjective a
  obtain ⟨c, rfl⟩ := A.rvCodeBijection.equiv.surjective b
  exact ⟨c, rfl⟩

def gammaGroundMeasuredGammaLiftForm (A : GammaGroundMeasuredGammaObject hc ground k) : GammaGroundVolumeForm hc ground A.underlying.rvLift.domain :=
  gammaGroundRVFamilyDesc A.underlying.rvPieces (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc))
    (fun i => gammaGroundGammaRVCodeForm (A.underlying.piece i) (A.form i))

def GammaGroundMeasuredGammaObject.rvLift (A : GammaGroundMeasuredGammaObject hc ground k) : GammaGroundMeasuredRVObject hc ground k :=
  ⟨A.underlying.rvLift, (gammaGroundMeasuredGammaLiftForm A)⟩

theorem gammaGroundMeasuredGammaLiftForm_code (A : GammaGroundMeasuredGammaObject hc ground k) (c : A.underlying.codeLift.Carrier) :
    gammaGroundFormValue (gammaGroundMeasuredGammaLiftForm A) (A.underlying.rvEncodeCode c) =
      A.weight (A.underlying.decode c) := by
  obtain ⟨i, c⟩ := c
  let P : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k) :=
    ⟨A.underlying.tags, fun j => (gammaGroundGammaCodeToRV (A.underlying.piece j)).image⟩
  let f (j : Fin A.underlying.tags) : GammaGroundMap (P.piece j) (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)) :=
    (A.form j).comp ((gammaGroundCodeDecode (A.underlying.piece j)).comp
      (gammaGroundGammaRVCodeBijection (A.underlying.piece j)).symm.map)
  have h := gammaGroundRVFamilyDesc_encode P (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)) f
    ⟨i, (gammaGroundGammaRVCodeBijection (A.underlying.piece i)).map c⟩
  have hv := congrArg (fun z : GammaGroundDefSet.univ hc ground (volumeGammaSpace hc) => z.val) h
  calc
    _ = gammaGroundFormValue (A.form i) (gammaGroundCodeDecode (A.underlying.piece i)
      ((gammaGroundGammaRVCodeBijection (A.underlying.piece i)).symm.map
        ((gammaGroundGammaRVCodeBijection (A.underlying.piece i)).map c))) := hv
    _ = _ := by
      rw [GammaGroundBijection.symm_apply_apply]
      rfl

def GammaGroundMeasuredFiniteGammaObject.resLift (A : GammaGroundMeasuredFiniteGammaObject hc ground k) : GammaGroundMeasuredRESObject hc ground k :=
  ⟨A.obj.rvLift, A.obj.underlying.rvLift_res A.property⟩

theorem gammaGroundRVFamilyTarget_encode (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k)) (a : A.Carrier) :
    A.rvTarget (A.rvEncode a) = ⟨a.2.val, Set.mem_univ _⟩ := by
  apply Subtype.ext
  funext i
  change rvAppend (rvFamilyTag a.1) a.2.val (Fin.natAdd A.tags i) = a.2.val i
  exact Fin.append_right _ _ _

theorem gammaGroundGammaRVLift_target_code (A : GammaGroundGammaObject hc ground k) (c : A.codeLift.Carrier) (j : Fin k) :
    (A.rvLift.target (A.rvEncodeCode c) j).val = gammaCodeTuple c.2.val j := by
  change (A.rvPieces.rvTarget (A.rvPieces.rvEncode (A.rvCodeBijection.equiv c))).val j = _
  rw [gammaGroundRVFamilyTarget_encode]
  rfl

theorem gammaGroundMeasuredGammaLift_combined (A : GammaGroundMeasuredGammaObject hc ground k) (c : A.underlying.codeLift.Carrier) :
    A.rvLift.combinedWeight (A.underlying.rvEncodeCode c) = A.combinedWeight (A.underlying.decode c) := by
  change gammaGroundFormValue (gammaGroundMeasuredGammaLiftForm A) (A.underlying.rvEncodeCode c) * _ = _
  rw [gammaGroundMeasuredGammaLiftForm_code]
  unfold GammaGroundMeasuredGammaObject.combinedWeight
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  apply Subtype.ext
  change Values.vrv (A.underlying.rvLift.target (A.underlying.rvEncodeCode c) j).val =
    Values.vrv (gammaCodeTuple c.2.val j)
  exact congrArg Values.vrv (gammaGroundGammaRVLift_target_code A.underlying c j)

end DiamondIntegral.Section3
