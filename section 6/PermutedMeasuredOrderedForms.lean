import «section 6».MeasuredOrderedContractions
import «section 6».PermutedOrderedContractionLifts
import «section 6».TransportedGammaLevels

/-! Gamma forms for ordered programs in permuted VF coordinates.
The target form depends on the actual contracted RV labels; relabeling
the VF coordinates preserves its exact transport and open source levels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfRelabeling_gamma_levels_open
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n))
    (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∀ u γ,IsOpen {a : Fin n → VF M | (a,u) ∈ (reindexedVFSet A e).carrier ∧
      gammaFormExtension (ω.comp ((vfRelabeling A e).inverse (vfRelabeling_bijective A e))) (a,u)=γ} := by
  have hHome := vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ A e hA
  apply transported_gamma_levels_open (vfRelabeling A e) (vfRelabeling_bijective A e) le_rfl
    (fun p i => by rw [rvTailIndex_self]; rfl) hHome.inverseContinuous
    (fun u => ((reindexedVFSet_properInvariant A e hA).clopen_fibres hv u).isOpen) ω hLevels

namespace MeasuredOrderedProgram
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {e : Equiv.Perm (Fin n)}
variable {ω : Map (reindexedVFSet A e) (DefSet.univ (rawGammaPresentation (M := M)) S)}

def originalRVMap (F : MeasuredOrderedProgram (G := G) (reindexedVFSet A e) ω)
    (V : OrderedStandardContractionLift F.program) : Map V.originalTarget F.rvTarget :=
  (rvProjection (Map.id V.originalTarget)).corestrict (fun p => ((V.originalTarget_recover p.val).mp p.property).1)

def originalTargetForm (F : MeasuredOrderedProgram (G := G) (reindexedVFSet A e) ω)
    (V : OrderedStandardContractionLift F.program) := F.rvForm.comp (F.originalRVMap V)

theorem originalTargetForm_transport (F : MeasuredOrderedProgram (G := G) (reindexedVFSet A e) ω)
    (V : OrderedStandardContractionLift F.program) (p : A) :
    (F.originalTargetForm V (V.originalMap p)).val=(ω (vfRelabeling A e p)).val := by
  have he : F.originalRVMap V (V.originalMap p)=F.program.toMap (vfRelabeling A e p) := by
    apply Subtype.ext
    exact Prod.ext (by funext i; exact i.elim0) (V.originalMap_labels p)
  change (F.rvForm (F.originalRVMap V (V.originalMap p))).val=_
  rw [he]
  exact F.factor _

theorem originalTargetForm_same_tags (F : MeasuredOrderedProgram (G := G) (reindexedVFSet A e) ω)
    (V : OrderedStandardContractionLift F.program) (p z : V.originalTarget) (hTags : p.val.2=z.val.2) :
    F.originalTargetForm V p=F.originalTargetForm V z := by
  apply congrArg F.rvForm
  apply Subtype.ext
  exact Prod.ext (by funext i; exact i.elim0) hTags

end MeasuredOrderedProgram
end DiamondIntegral.Section6
