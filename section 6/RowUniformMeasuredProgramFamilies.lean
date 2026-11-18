import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFormCompatibleProgramLoci
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreComponentSemantics
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaCoreParameterSemantics
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormRVTraceBounds
import «section 6».RowGammaFormRVTraces
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaRVTraceValues
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowSequentialMeasuredCentripetalPrograms
import «section 6».UniformProgramFamilies

/-! (Row-form version for Remark 6.20, translated from `UniformMeasuredProgramFamilies`.)
 Actual uniform measured program families retain their full local
Gamma maps and graphs, open levels, component guards, terminal tests,
and complete measured RV rows with the same named uniform bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

structure UniformMeasuredProgramFamilyRow
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : CentripetalProgramTemplate (M := M) S 1 n s t)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s) extends UniformProgramFamily η T A P where
  forms : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter η b)) qR
  graphs : ∀ b : B,{z | Sum.elim (unaryFamilyParameter η b) z ∈ W.graph}=
    (rawMixedSpace n s).relation (rawRVSpace (M := M) qR) (forms b).graph
  levels : ∀ b : B,∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre (unaryFamilyParameter η b)).carrier ∧
    rowFormExtension (forms b) (x,u)=γ}
  admissible : ∀ b : B,unaryFamilyParameter η b ∈ T.measuredFormGoodRow A P W
  measuredRows : ∀ D ∈ T.measuredRVTraceRow A P W,∀ b c : B,b.val.2=c.val.2 →
    (D.2.fibre (unaryFamilyParameter η b)).carrier=(D.2.fibre (unaryFamilyParameter η c)).carrier
  measuredBound : ∀ D ∈ T.measuredRVTraceRow A P W,∀ b : B,∀ u ∈ (D.2.fibre (unaryFamilyParameter η b)).carrier,
    ∀ i,(radius⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ radius.val

namespace UniformMeasuredProgramFamilyRow
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}

def freeze {q : ℕ} {C : DefSet (rawMixedSpace (M := M) (n+1) q) S}
    (U : UniformMeasuredProgramFamilyRow (G := G) η T A P W) (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) :
    UniformMeasuredProgramFamilyRow (G := G) (D.unaryParameter hB η) T A P W where
  toUniformProgramFamily := U.toUniformProgramFamily.freeze D hB
  forms b := U.forms (D.unaryBaseFreeze hB b)
  graphs b := U.graphs (D.unaryBaseFreeze hB b)
  levels b := U.levels (D.unaryBaseFreeze hB b)
  admissible b := U.admissible (D.unaryBaseFreeze hB b)
  measuredRows V hV := D.unaryParameter_rows_constant hB η V.2 (U.measuredRows V hV)
  measuredBound V hV := D.unaryParameter_bound hB η V.2 U.radius (U.measuredBound V hV)

def sequential (U : UniformMeasuredProgramFamilyRow (G := G) η T A P W) :
    UniformMeasuredProgramFamilyRow (G := G) η T.toSequence.toProgram A P W where
  toUniformProgramFamily := {
    geometry := U.geometry
    pullback := U.pullback
    prepared b := (Set.ext_iff.mp (T.toSequence_sameData.preparedGood A P) _).mp (U.prepared b)
    rows D hD := U.rows D (by rw [T.toSequence_sameData.rvTrace]; exact hD)
    radius := U.radius
    named := U.named
    bound D hD := U.bound D (by rw [T.toSequence_sameData.rvTrace]; exact hD) }
  forms := U.forms
  graphs := U.graphs
  levels := U.levels
  admissible b := (Set.ext_iff.mp (T.toSequence_sameFormData_row.measuredFormGoodRow A P W) _).mp (U.admissible b)
  measuredRows D hD := U.measuredRows D (by rw [T.toSequence_sameFormData_row.measuredRVTraceRow]; exact hD)
  measuredBound D hD := U.measuredBound D (by rw [T.toSequence_sameFormData_row.measuredRVTraceRow]; exact hD)

end UniformMeasuredProgramFamilyRow
end DiamondIntegral.Section6
