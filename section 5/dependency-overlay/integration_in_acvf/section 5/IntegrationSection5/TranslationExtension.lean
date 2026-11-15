import IntegrationSection5.GlobalNonrectangleHeads
import IntegrationSection5.RelativeSpecialExtension
import IntegrationSection5.GammaStandardProgramGraphs
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {n m : ℕ}
variable {A : Set (Point (M := M) n m)} {E : Set (Fin m → RV (M := M))}
variable {i : Fin n} {c : Point (M := M) n m → VF (M := M)} {R : Set M}

namespace CanonicalTranslationPreparation

def extendBase (T : CanonicalTranslationPreparation (G := G) A i c) (h : T.codes ⊆ R) :
    CanonicalTranslationPreparation (G := G) A i c where
  codes := R
  real_contains := fun x hx => h (T.real_contains hx)
  source := SpecialTransformations.Section5.extendBase T.source h
  target := SpecialTransformations.Section5.extendBase T.target h
  source_eq := T.source_eq
  map := extendPointMap T.map h
  special := specialRelativeBoundary_extendBase T.map h T.special
  graph := gamma_extendPointMap T.map h T.graph
  target_gamma := T.target_gamma
  formula p := T.formula ⟨p.val,p.property⟩

theorem extendBase_map (T : CanonicalTranslationPreparation (G := G) A i c) (h : T.codes ⊆ R)
    (p : (T.extendBase h).source) :
    ((T.extendBase h).map p).val = (T.map ⟨p.val,p.property⟩).val := rfl

end CanonicalTranslationPreparation
namespace RVSliceTranslationPreparation

def extendBase (U : RVSliceTranslationPreparation (G := G) A E i c) (h : U.branch.codes ⊆ R) :
    RVSliceTranslationPreparation (G := G) A E i c where
  branch := U.branch.extendBase h
  source := SpecialTransformations.Section5.extendBase U.source h
  source_eq := U.source_eq
  target := SpecialTransformations.Section5.extendBase U.target h
  map := extendPointMap U.map h
  special := specialRelativeBoundary_extendBase U.map h U.special
  graph := gamma_extendPointMap U.map h U.graph
  target_gamma := U.target_gamma
  formula p := U.formula ⟨p.val,p.property⟩
  active_image := U.active_image

theorem extendBase_map (U : RVSliceTranslationPreparation (G := G) A E i c) (h : U.branch.codes ⊆ R)
    (p : (U.extendBase h).source) :
    ((U.extendBase h).map p).val = (U.map ⟨p.val,p.property⟩).val := rfl

end RVSliceTranslationPreparation
end IntegrationInACVF.Section5
