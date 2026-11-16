import «section 6».ZeroExtendedScalarGraphSemantics

/-! Uniform first-order codes for both centripetal branches. The
focus and coefficient are explicit finite input coordinates, so these
codes assemble parameterized transition relations without choosing a
new real parameter. Their interpretation is the existing actual map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

abbrev ScalarStepCodeIndex (n r : ℕ) := (Fin n ⊕ Fin r) ⊕ (Fin 1 ⊕ Fin 1)

def scalarStepProduct (z : ScalarStepCodeIndex n r → M) : M :=
  iVFMul (z (.inr (.inr 0))) (z (.inr (.inl 0)))

def scalarStepDifference (j : Fin n) (z : ScalarStepCodeIndex n r → M) : M :=
  iVFAdd (z (.inl (.inl j))) (iVFNeg (z (.inr (.inl 0))))

def scalarStepCoreCode (j : Fin n) (z : ScalarStepCodeIndex n r → M) : Prop :=
  ¬ iLe (iRv (scalarStepDifference j z)) (iRv (scalarStepProduct z))

def scalarCentripetalCodes (j : Fin n) (z : ScalarStepCodeIndex n r → M) : Fin n ⊕ Fin (1+r) → M :=
  Sum.elim (fun i => if i=j then
    if scalarStepCoreCode j z then iVFAdd (scalarStepDifference j z) (scalarStepProduct z)
      else scalarStepDifference j z
    else z (.inl (.inl i)))
    (Fin.append (fun _ : Fin 1 => if scalarStepCoreCode j z then (branchTag (M := M) true).val
      else (branchTag (M := M) false).val) (fun i => z (.inl (.inr i))))

theorem scalarCentripetalCodes_definable (j : Fin n) :
    S.DefinableMap LRV (scalarCentripetalCodes (M := M) (r := r) j) := by
  let Z := ScalarStepCodeIndex n r
  have hProduct : S.DefinableFun LRV (scalarStepProduct (M := M) (n := n) (r := r)) :=
    scalarMulCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)
  have hDiff : S.DefinableFun LRV (scalarStepDifference (M := M) (r := r) j) :=
    scalarSubCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)
  have hCore : S.Definable LRV {z : Z → M | scalarStepCoreCode j z} :=
    (rvCode_compare_definable (rv_scalarCode_definable hDiff) (rv_scalarCode_definable hProduct)).compl
  have hOut := Set.DefinableFun.ite hCore (scalarAddCode_definable hDiff hProduct) hDiff
  have hTag := Set.DefinableFun.ite hCore (branchTag_definable S true) (branchTag_definable S false)
  rintro (i | i)
  · by_cases hi : i=j
    · simpa only [scalarCentripetalCodes,Sum.elim_inl,if_pos hi] using hOut
    · simpa only [scalarCentripetalCodes,Sum.elim_inl,if_neg hi] using
        (show S.DefinableFun LRV (fun z : Z → M => z (.inl (.inl i))) from Set.DefinableFun.proj LRV)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [scalarCentripetalCodes,Sum.elim_inr,Fin.append_left] using hTag
    · simpa only [scalarCentripetalCodes,Sum.elim_inr,Fin.append_right] using
        (show S.DefinableFun LRV (fun z : Z → M => z (.inl (.inr i))) from Set.DefinableFun.proj LRV)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem scalarCentripetalCodes_at {A : DefSet (rawMixedSpace (M := M) n r) S}
    (D : CentripetalData (G := G) A) (p : Mixed M n r) :
    scalarCentripetalCodes D.coordinate (Sum.elim (mixedValues p)
      (Sum.elim (fun _ : Fin 1 => (D.extendedFocus p).val) (fun _ : Fin 1 => D.coefficient.val)))=
        mixedValues (D.point p) := by
  rw [← D.codes_at p]
  rfl

end DiamondIntegral.Section6
