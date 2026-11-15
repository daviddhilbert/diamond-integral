import IntegrationSection5.RVSliceHeadCompletion
import IntegrationSection5.InactiveBranchHeadIso
import IntegrationSection5.RVSliceHeadImages
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {E : Set (Fin m → RV (M := M))}
variable {c : Point (M := M) 2 m → VF (M := M)}
namespace RVSliceHeadCompletion
variable {U : RVSliceTranslationPreparation (G := G) A E 0 c}

theorem nonrectangle_source_slice (C : RVSliceHeadCompletion U) :
    carrier (U.extendBase C.contains_codes).branch.target =
      {p | p ∈ carrier (U.extendBase C.contains_codes).target ∧ p.2 ∉ {s | s ∘ Fin.natAdd 1 ∉ E}} := by
  change carrier U.branch.target = {p | p ∈ carrier U.target ∧ ¬ ¬ p.2 ∘ Fin.natAdd 1 ∈ E}
  rw [U.active_image]
  ext p
  exact and_congr_right (fun _ => not_not.symm)

def nonrectangleImage (C : RVSliceHeadCompletion U) := C.completion.inactiveImage C.nonrectangle_source_slice

def nonrectangleHeadIso (C : RVSliceHeadCompletion U) :
    GammaIso G (carrier (headImage (U.extendBase C.contains_codes).branch.target))
      (carrier (headImage C.nonrectangleImage)) :=
  C.completion.inactiveHeadIso C.nonrectangle_source_slice U.branch.target_gamma

def originalLabelIndex (C : RVSliceHeadCompletion U) : Fin m → Fin (1+C.completion.arity) :=
  Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le C.completion.preparation.special) ∘ Fin.natAdd 1

theorem nonrectangle_head_slice (C : RVSliceHeadCompletion U) :
    carrier (headImage C.nonrectangleImage) =
      {p | p ∈ carrier C.preparation.contractedSet ∧ p.2 ∘ C.originalLabelIndex ∈ E} := by
  have hSource : carrier (U.extendBase C.contains_codes).branch.target =
      {p | p ∈ carrier (U.extendBase C.contains_codes).target ∧ p.2 ∈ {s | s ∘ Fin.natAdd 1 ∈ E}} := U.active_image
  have hLabels (a : (U.extendBase C.contains_codes).target) :
      (C.completion.preparation.map a).val.2 ∘
        suffixIndex (specialRelative_rvArity_le C.completion.preparation.special) = a.val.2 := by
    funext j
    exact specialRelative_oldLabels C.completion.preparation.special a j
  have hImage := restrictPointImage_rvSlice C.completion.preparation.map C.completion.preparation.bijective.2
    _ hLabels {s | s ∘ Fin.natAdd 1 ∈ E} hSource
    (C.completion.inactiveSourceSubset C.nonrectangle_source_slice)
  have hHead := headImage_rvSlice _ {s | s ∘ Fin.natAdd 1 ∈ E} hImage
  exact hHead

end RVSliceHeadCompletion
end IntegrationInACVF.Section5
