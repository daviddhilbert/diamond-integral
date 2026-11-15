import IntegrationSection5.HeadProjectionPadding
import IntegrationSection5.CompletedNonrectangleHead
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m b : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {H N : DefSet (M := M) S 2 m} {u : SpecialBijection A B}
variable {E : Set (Fin m → RV (M := M))}
namespace RVProductBranchCompletion

def inactivePadding (C : RVProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∉ E}) (hNΓ : GammaSetDefinable G (carrier N)) :
    RVProjectionPadding (G := G) (headImage (C.inactiveImage hN)) (headImage N)
      (headPaddingProjection (suffixIndex (specialRelative_rvArity_le C.preparation.special))) :=
  fixedVFHeadProjectionPadding (C.inactiveMap hN)
    (restrictPointMap_surjective C.preparation.map N (C.inactiveSourceSubset hN)) hNΓ
    (gamma_restrictPointImage C.preparation.map N (C.inactiveSourceSubset hN) hNΓ C.preparation_gamma)
    (gamma_restrictPointMap C.preparation.map N (C.inactiveSourceSubset hN) hNΓ C.preparation_gamma)
    (C.inactiveMap_vf hN) (suffixIndex (specialRelative_rvArity_le C.preparation.special))
    (C.inactiveMap_oldLabels hN) (C.inactiveMap_sameRV hN)
end RVProductBranchCompletion

namespace RVSliceHeadCompletion
variable {m : ℕ} {A : Set (Point (M := M) 2 m)} {E : Set (Fin m → RV (M := M))}
variable {c : Point (M := M) 2 m → VF (M := M)} {U : RVSliceTranslationPreparation (G := G) A E 0 c}

def nonrectanglePadding (C : RVSliceHeadCompletion U) :
    RVProjectionPadding (G := G) (headImage C.nonrectangleImage)
      (headImage (U.extendBase C.contains_codes).branch.target)
      (headPaddingProjection (suffixIndex (specialRelative_rvArity_le C.completion.preparation.special))) :=
  C.completion.inactivePadding C.nonrectangle_source_slice U.branch.target_gamma

end RVSliceHeadCompletion
end IntegrationInACVF.Section5
