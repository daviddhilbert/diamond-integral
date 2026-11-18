import «section 3».GammaMeasuredRVSyntax
import IntegrationSection6.GammaRecodingAgreements
import Section3.GammaRealMap

/-! Pull an RV-parameter family back along the actual RV map on VF
parameters. This uses the language map, with no section in either direction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

def gammaRVParameterCodes (p d : ℕ) (w : Fin d → M) : Fin d → M :=
  fun i => if i.val < p then rvCode (w i) else w i

theorem gammaRVParameterCodes_definable (B : Base (M := M)) (p d : ℕ) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin d) (Fin d) B.real (gammaRVParameterCodes p d) := by
  intro i
  by_cases hi : i.val < p
  · simpa only [gammaRVParameterCodes,if_pos hi] using rvCode_definable B.real i
  · simpa only [gammaRVParameterCodes,if_neg hi] using (rawProj B.real i)

theorem gammaRVParameterCodes_append (z : Fin p → M) (r : Fin a → M) :
    gammaRVParameterCodes p (p+a) (Fin.append z r) = Fin.append (fun i => rvCode (z i)) r := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [gammaRVParameterCodes,Fin.val_castAdd,if_pos j.isLt,Fin.append_left]
  · have hj : ¬ p+j.val < p := by omega
    simp only [gammaRVParameterCodes,Fin.val_natAdd,if_neg hj,Fin.append_right]

theorem gammaRVParameterCodes_relation (z : Fin p → M) (r : Fin a → M) (v : Fin b → M) :
    gammaRVParameterCodes p ((p+a)+b) (Fin.append (Fin.append z r) v) =
      Fin.append (Fin.append (fun i => rvCode (z i)) r) v := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp only [gammaRVParameterCodes,Fin.val_castAdd,if_pos j.isLt,Fin.append_left]
    · intro j
      have hj : ¬ p+j.val < p := by omega
      simp only [gammaRVParameterCodes,Fin.val_castAdd,Fin.val_natAdd,if_neg hj,Fin.append_left,Fin.append_right]
  · intro j
    have hj : ¬ (p+a)+j.val < p := by omega
    simp only [gammaRVParameterCodes,Fin.val_natAdd,if_neg hj,Fin.append_right]

def gammaRVParametersFromVF (B : Base (M := M)) (p : ℕ) :
    GammaParameterRecode B p p (fun _ => .rv) (fun _ => .vf) where
  domain {a} D := ⟨{w | gammaRVParameterCodes p (p+a) w ∈ D.val ∧
      w ∈ sortedUniverse (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin a => .rv))},
    D.property.preimage_real_map _ _ (gammaRVParameterCodes_definable B p (p+a))⟩
  relation {a b} R := ⟨{w | gammaRVParameterCodes p ((p+a)+b) w ∈ R.val ∧
      w ∈ sortedUniverse (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv))},
    R.property.preimage_real_map _ _ (gammaRVParameterCodes_definable B p ((p+a)+b))⟩

theorem gammaRVParameterCodes_vf (x : Fin p → VF (M := M)) :
    (fun i => rvCode (vfValues x i)) = rvValues (fun i => rv (x i)) := by
  funext i
  exact rvCode_eq (x i).val (x i).property

theorem gammaRVParametersFromVF_rows
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (x : Fin p → VF (M := M)) :
    GammaSchemaRowAgreement F (rvValues (fun i => rv (x i)))
      ((gammaRVParametersFromVF B p).object F) (vfValues x) := by
  apply gammaSchemaRowAgreement_of_typed
  · intro r
    have hSort : Fin.append (vfValues x) (rvValues r) ∈
        sortedUniverse (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin a => .rv)) := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left,sortEval,iVF,iRV,vfValues,rvValues] using (x j).property
      · simpa only [Fin.append_right,sortEval,iVF,iRV,vfValues,rvValues] using (r j).property
    change (_ ∈ F.domain) ↔ (gammaRVParameterCodes p (p+a) (Fin.append (vfValues x) (rvValues r)) ∈ F.domain ∧ _)
    rw [gammaRVParameterCodes_append,gammaRVParameterCodes_vf]
    exact (and_iff_left hSort).symm
  · intro r v
    have hSort : Fin.append (Fin.append (vfValues x) (rvValues r)) (rvValues v) ∈
        sortedUniverse (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin a => .rv)) (fun _ : Fin k => .rv)) := by
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left,sortEval,iVF,iRV,vfValues,rvValues] using (x j).property
        · simpa only [Fin.append_left,Fin.append_right,sortEval,iVF,iRV,vfValues,rvValues] using (r j).property
      · intro j
        simpa only [Fin.append_right,sortEval,iVF,iRV,vfValues,rvValues] using (v j).property
    change (_ ∈ F.volume) ↔ (gammaRVParameterCodes p ((p+a)+k)
      (Fin.append (Fin.append (vfValues x) (rvValues r)) (rvValues v)) ∈ F.volume ∧ _)
    rw [gammaRVParameterCodes_relation,gammaRVParameterCodes_vf]
    exact (and_iff_left hSort).symm

end DiamondIntegral.Section3
