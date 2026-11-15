import IntegrationSection5.ProductProgramKernel
import IntegrationSection5.StandardContractionLift

/-! The two volume coordinates are exactly the prepared VF values of the
two factors, in their original order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {b c : ℕ}
namespace ProductContractionProgram
variable {H : DefSet (M := M) S 2 0} {AD AE : DefSet (M := M) S 1 0}
variable {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
variable {d : Map AD BD} {e : Map AE BE}

theorem volumeIndex_zero (P : ProductContractionProgram (G := G) H AD AE BD BE d e) :
    P.program.volumeIndex 0 = Fin.natAdd 1 (suffixIndex P.retained_le 0) := by
  apply Fin.ext
  change (1+P.tail.arity)-(1+P.first.arity)+0 = 1+(P.tail.arity-(1+P.first.arity)+0)
  have h := P.retained_le
  omega

theorem volumeIndex_one (P : ProductContractionProgram (G := G) H AD AE BD BE d e) :
    P.program.volumeIndex 1 = 0 := by
  apply Fin.ext
  change (1+P.tail.arity)-(1+P.tail.arity)+0 = 0
  omega

theorem volume_formula (P : ProductContractionProgram (G := G) H AD AE BD BE d e) (a : H) :
    (rvObjectVolume P.program.contractionObject (P.program.rawContractionMap a)).val =
      ![rv (vfAt (d (P.dSource a)).val 0),rv (vfAt (e (P.eSource a)).val 0)] := by
  funext j
  fin_cases j
  · change (P.program.toMap a).val.2 (P.program.volumeIndex 0) = _
    rw [P.volumeIndex_zero]
    change (headKeyMap P.tail.target (P.tail.map (P.first.contractionMap a))).val.2
      (Fin.natAdd 1 (suffixIndex P.retained_le 0)) = _
    rw [headKeyMap_apply]
    change Fin.append (fun _ : Fin 1 => rv (vfAt (P.tail.map (P.first.contractionMap a)).val 0))
      (P.tail.map (P.first.contractionMap a)).val.2 (Fin.natAdd 1 (suffixIndex P.retained_le 0)) = _
    rw [Fin.append_right,specialRelative_oldLabels P.tail.special]
    change (headKeyMap P.first.target (P.first.map a)).val.2 0 = _
    rw [headKeyMap_apply]
    change rv (vfAt (P.first.map a).val 0) = rv (vfAt (d (P.dSource a)).val 0)
    exact congrArg (fun p : Point (M := M) 1 b => rv (vfAt p 0)) (P.first_square a)
  · change (P.program.toMap a).val.2 (P.program.volumeIndex 1) = _
    rw [P.volumeIndex_one]
    change (headKeyMap P.tail.target (P.tail.map (P.first.contractionMap a))).val.2 0 = _
    rw [headKeyMap_apply]
    change rv (vfAt (P.tail.map (P.first.contractionMap a)).val 0) = rv (vfAt (e (P.eSource a)).val 0)
    exact congrArg (fun p : Point (M := M) 1 c => rv (vfAt p 0)) (P.tail_square a)

end ProductContractionProgram
end IntegrationInACVF.Section5
