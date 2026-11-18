import «section 3».GammaFrozenHeadPreparations
import «section 3».GammaSelectedHeadMeasuredBridge
import Integration7.HeadCoordinateFibreContraction
import IntegrationSection6.GammaGraphFormulaCongruence

/-! The actual selected RV fibre of a head contraction is the selected
RV object of its frozen unary preparation. Only equivalent full graph
formulas change; the native object and every volume coordinate are kept. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a k : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a}
variable (T : HeadPreparation U) (x : Fin n → VF (M := M))

theorem gammaFrozenHeadPreparation_contracted_mem (r : Fin (1+T.arity) → RV (M := M)) :
    (Fin.elim0,r) ∈ carrier (gammaFrozenHeadPreparation T x).contractedSet ↔
      (x,r) ∈ carrier T.contractedSet := by
  change (Fin.elim0,r) ∈ carrier ((headCoordinateFibrePreparation T x).extendBase (Set.subset_univ _)).contractedSet ↔ _
  rw [HeadPreparation.extendBase_contractedSet]
  exact head_coordinate_fibre_contraction_domain T x r

def gammaFrozenHeadSelectedPresentation (ρ : Fin k → Fin a)
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x) :
    GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (1+T.arity) (1+k)
      {r | (Fin.elim0,r) ∈ carrier (gammaFrozenHeadPreparation T x).contractedSet}
      (fun r y => (Fin.elim0,r) ∈ carrier (gammaFrozenHeadPreparation T x).contractedSet ∧
        r ∘ headVolumeIndex (gammaFrozenHeadPreparation T x) ρ = y) :=
  P.congrFormula (Set.ext (fun r => (gammaFrozenHeadPreparation_contracted_mem T x r).symm))
    (fun r y => and_congr (gammaFrozenHeadPreparation_contracted_mem T x r).symm Iff.rfl)

theorem gammaFrozenHeadSelectedPresentation_toGamma (ρ : Fin k → Fin a)
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x) :
    (gammaFrozenHeadSelectedPresentation T x ρ P).toGamma = P.toGamma :=
  P.congrFormula_toGamma _ _

def gammaFrozenHeadLabels (hU : GammaSetDefinable B (carrier U))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier)
    (p : extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)) :
    p.val.2 ∈ (Q.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left).carrier :=
  hLabels ⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩

end DiamondIntegral.Section3
