import «section 3».GammaCodeFormRestrictions
import «section 3».GammaVolumeCategories
import «section 3».GammaRVLift
import «section 3».GammaRESLift
import «section 3».RVFamilyDesc
import «section 3».RVFormGraphs

/-! Gamma volume forms lift along every RV representative and the
explicit finite tags. The full invariant graphs remain over the same base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def GammaObject.rvEncodeCode (A : GammaObject hc S k) (c : A.codeLift.Carrier) : A.rvLift.domain :=
  A.rvPieces.rvEncode (A.rvCodeBijection.equiv c)

theorem GammaObject.rvEncodeCode_surjective (A : GammaObject hc S k) :
    Function.Surjective A.rvEncodeCode := by
  intro a
  obtain ⟨b, rfl⟩ := A.rvPieces.rvEquiv.surjective a
  obtain ⟨c, rfl⟩ := A.rvCodeBijection.equiv.surjective b
  exact ⟨c, rfl⟩

def measuredGammaLiftForm (A : MeasuredGammaObject hc S k) : GammaVolumeForm hc A.underlying.rvLift.domain :=
  rvFamilyDesc A.underlying.rvPieces (DefSet.univ (volumeGammaSpace hc) S)
    (fun i => gammaRVCodeForm (A.underlying.piece i) (A.form i))

def MeasuredGammaObject.rvLift (A : MeasuredGammaObject hc S k) : MeasuredRVObject S k :=
  ⟨A.underlying.rvLift, (measuredGammaLiftForm A).toRVVolumeForm hc⟩

theorem measuredGammaLiftForm_code (A : MeasuredGammaObject hc S k) (c : A.underlying.codeLift.Carrier) :
    gammaFormValue (measuredGammaLiftForm A) (A.underlying.rvEncodeCode c) =
      A.weight (A.underlying.decode c) := by
  obtain ⟨i, c⟩ := c
  let P : FiniteFamily (rawRVSpace (M := M) k) S :=
    ⟨A.underlying.tags, fun j => (gammaCodeToRV (A.underlying.piece j)).image⟩
  let f (j : Fin A.underlying.tags) : Map (P.piece j) (DefSet.univ (volumeGammaSpace hc) S) :=
    (A.form j).comp ((codeDecode (A.underlying.piece j)).comp
      (gammaRVCodeBijection (A.underlying.piece j)).symm.map)
  have h := rvFamilyDesc_encode P (DefSet.univ (volumeGammaSpace hc) S) f
    ⟨i, (gammaRVCodeBijection (A.underlying.piece i)).map c⟩
  have hv := congrArg (fun z : DefSet.univ (volumeGammaSpace hc) S => z.val) h
  calc
    _ = gammaFormValue (A.form i) (codeDecode (A.underlying.piece i)
      ((gammaRVCodeBijection (A.underlying.piece i)).symm.map
        ((gammaRVCodeBijection (A.underlying.piece i)).map c))) := hv
    _ = _ := by
      rw [DefinableBijection.symm_apply_apply]
      rfl

def MeasuredFiniteGammaObject.resLift (A : MeasuredFiniteGammaObject hc S k) : MeasuredRESObject S k :=
  ⟨A.obj.rvLift, A.obj.underlying.rvLift_res A.property⟩

theorem rvFamilyTarget_encode (A : FiniteFamily (rawRVSpace (M := M) k) S) (a : A.Carrier) :
    A.rvTarget (A.rvEncode a) = ⟨a.2.val, Set.mem_univ _⟩ := by
  apply Subtype.ext
  funext i
  change rvAppend (rvFamilyTag a.1) a.2.val (Fin.natAdd A.tags i) = a.2.val i
  exact Fin.append_right _ _ _

theorem gammaRVLift_target_code (A : GammaObject hc S k) (c : A.codeLift.Carrier) (j : Fin k) :
    (A.rvLift.target (A.rvEncodeCode c) j).val = gammaCodeTuple c.2.val j := by
  change (A.rvPieces.rvTarget (A.rvPieces.rvEncode (A.rvCodeBijection.equiv c))).val j = _
  rw [rvFamilyTarget_encode]
  rfl

theorem measuredGammaLift_combined (A : MeasuredGammaObject hc S k) (c : A.underlying.codeLift.Carrier) :
    A.rvLift.combinedWeight (A.underlying.rvEncodeCode c) = A.combinedWeight (A.underlying.decode c) := by
  change gammaFormValue (measuredGammaLiftForm A) (A.underlying.rvEncodeCode c) * _ = _
  rw [measuredGammaLiftForm_code]
  unfold MeasuredGammaObject.combinedWeight
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  apply Subtype.ext
  change Values.vrv (A.underlying.rvLift.target (A.underlying.rvEncodeCode c) j).val =
    Values.vrv (gammaCodeTuple c.2.val j)
  exact congrArg Values.vrv (gammaRVLift_target_code A.underlying c j)

end DiamondIntegral.Section3
