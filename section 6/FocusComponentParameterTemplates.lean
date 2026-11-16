import «section 6».FocusGraphParameterTemplates
import «section 6».CoefficientParameterLoci
import «section 6».TaggedSourceParameterLoci
import «section 6».FocusSourceCodeSemantics
import «section 6».FocusLeadingTermParameterLoci
import «section 6».PointwiseProtectedFocusData
import «section 6».ContinuousFamilyFocusData

/-! One original-base template for a complete permitted component.
Its admissibility checks the whole focus family and finite named
metadata, together with all ambient and protected geometric conditions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k : ℕ}

structure FocusComponentParameterTemplate (S : Set M) (p n r : ℕ) where
  coordinate : Fin n
  active : RVSetParameterTemplate (M := M) S p r
  focus : ContinuousRVGraphTemplate (M := M) S p r n 1
  coefficient : ContinuousVFGraphTemplate (M := M) S p 0 1
  radius : GammaNameParameterTemplate (M := M) S p

namespace FocusComponentParameterTemplate
def geometricLocus (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : Set (FocusMetadataIndex (Fin p) → M) :=
  (coefficientCodeCondition (Fin p) ∩
    (focusSourceInvariantParameterLocus A.typedGraph (focusGraphParameterCode A T.active T.focus) T.coordinate ∩
      focusErasedCovarianceParameterLocus (focusGraphParameterCode A T.active T.focus) T.coordinate)) ∩
        ⋂ i,focusSourceInvariantParameterLocus (P i).typedGraph
          (focusGraphParameterCode (P i) T.active T.focus) T.coordinate

theorem geometricLocus_definable (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : S.Definable LRV (T.geometricLocus A P) :=
  (coefficientCodeCondition_definable.inter
    ((focusSourceInvariantParameterLocus_definable A.typedGraph A.typedGraph_definable
      _ (focusGraphParameterCode_definable A T.active T.focus) T.coordinate).inter
        (focusErasedCovarianceParameterLocus_definable _
          (focusGraphParameterCode_definable A T.active T.focus) T.coordinate))).inter
    (Set.definable_iInter_of_finite (fun i =>
      focusSourceInvariantParameterLocus_definable (P i).typedGraph (P i).typedGraph_definable
        _ (focusGraphParameterCode_definable (P i) T.active T.focus) T.coordinate))

def good (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : Set (Fin p → M) :=
  ((T.focus.good ∩ T.coefficient.good) ∩ T.radius.good) ∩
    (((taggedSourceParameterLocus A.typedGraph ∩
      focusIndependentParameterLocus (focusGraphParameterCode A T.active T.focus) T.coordinate) ∩
        focusLeadingTermParameterLocus (focusGraphParameterCode A T.active T.focus) T.coordinate) ∩
      focusMetadataParameterLocus T.coefficient T.radius (T.geometricLocus A P))

theorem good_definable (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : S.Definable LRV (T.good A P) :=
  ((T.focus.good_definable.inter T.coefficient.good_definable).inter T.radius.good_definable).inter
    ((((taggedSourceParameterLocus_definable A.typedGraph A.typedGraph_definable).inter
      (focusIndependentParameterLocus_definable _ (focusGraphParameterCode_definable A T.active T.focus) T.coordinate)).inter
        (focusLeadingTermParameterLocus_definable _ (focusGraphParameterCode_definable A T.active T.focus) T.coordinate)).inter
      (focusMetadataParameterLocus_definable T.coefficient T.radius _ (T.geometricLocus_definable A P)))

end FocusComponentParameterTemplate
end DiamondIntegral.Section6
