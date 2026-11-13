import «section 3».GammaCodeFormRestrictions
import «section 3».MeasuredGammaRVLift
import «section 3».GammaRVScissors
import «section 3».RVFamilyDescRestrictions

/-! The full measured Gamma lift commutes with restricting every tagged
piece and inheriting its original Gamma form. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem measuredGammaLiftForm_restrict (U : MeasuredGammaObject hc S k)
    (X : Fin U.underlying.tags → GammaPiece hc S k)
    (hX : ∀ i, (X i).carrier ⊆ (U.underlying.piece i).carrier) :
    measuredGammaLiftForm (U.restrict X hX) = (measuredGammaLiftForm U).comp
      (Map.inclusion (U.underlying.rvLift_restrict_subset X hX)) := by
  let P : FiniteFamily (rawRVSpace (M := M) k) S :=
    ⟨U.underlying.tags, fun i => (gammaCodeToRV (U.underlying.piece i)).image⟩
  let Y (i : Fin U.underlying.tags) : DefSet (rawRVSpace (M := M) k) S := (gammaCodeToRV (X i)).image
  let hY (i : Fin U.underlying.tags) : (Y i).carrier ⊆ (P.piece i).carrier := gammaRVCodeLift_mono (hX i)
  let f (i : Fin U.underlying.tags) : Map (P.piece i) (DefSet.univ (volumeGammaSpace hc) S) :=
    gammaRVCodeForm (U.underlying.piece i) (U.form i)
  have hf (i : Fin U.underlying.tags) :
      gammaRVCodeForm (X i) ((U.form i).comp (Map.inclusion (hX i))) =
        (f i).comp (Map.inclusion (hY i)) := gammaRVCodeForm_restrict (hX i) (U.form i)
  apply Map.ext
  intro a
  change rvFamilyDesc ⟨U.underlying.tags, Y⟩ (DefSet.univ (volumeGammaSpace hc) S)
      (fun i => gammaRVCodeForm (X i) ((U.form i).comp (Map.inclusion (hX i)))) a =
    rvFamilyDesc P (DefSet.univ (volumeGammaSpace hc) S) f
      (Map.inclusion (rvFamilyRealization_mono P.piece Y hY) a)
  calc
    _ = rvFamilyDesc ⟨U.underlying.tags, Y⟩ (DefSet.univ (volumeGammaSpace hc) S)
        (fun i => (f i).comp (Map.inclusion (hY i))) a := by
      exact congrArg (fun F : ∀ i, Map (Y i) (DefSet.univ (volumeGammaSpace hc) S) =>
        rvFamilyDesc ⟨U.underlying.tags, Y⟩ (DefSet.univ (volumeGammaSpace hc) S) F a) (funext hf)
    _ = _ := rvFamilyDesc_restrict P (DefSet.univ (volumeGammaSpace hc) S) f Y hY a

end DiamondIntegral.Section3
