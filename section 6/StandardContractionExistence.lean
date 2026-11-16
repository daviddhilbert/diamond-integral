import «section 6».AllDimensionalOrderedContractions
import «section 6».NormalizedOrderedContractionLifts

/-! Standard-contraction existence in every VF dimension, with the permitted
preliminary normalization and every coordinate order. The actual object
contains the complete program, lift and map on the original source. -/

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

structure StandardContraction (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n)) where
  normalization : ZeroCenteredData A
  arity : ℕ
  rvTarget : DefSet (rawMixedSpace (M := M) 0 arity) S
  program : OrderedStandardContractionProgram (G := G) S (reindexedVFSet normalization.map.image e) rvTarget
  lift : OrderedStandardContractionLift program

namespace StandardContraction
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {e : Equiv.Perm (Fin n)}

def target (F : StandardContraction (G := G) A e) := F.lift.originalTarget

def map (F : StandardContraction (G := G) A e) : Map A F.target :=
  F.normalization.normalizedOrderedMap F.lift

def contraction (F : StandardContraction (G := G) A e) : Map A F.rvTarget :=
  F.lift.originalContraction.comp F.normalization.bijection

theorem labels (F : StandardContraction (G := G) A e) (p : A) :
    (F.map p).val.2=(F.contraction p).val.2 := F.lift.originalMap_labels _

theorem contraction_surjective (h00 : M ⊨ Axioms.ACVF00) (F : StandardContraction (G := G) A e) :
    Function.Surjective F.contraction :=
  (F.program.surjective.comp (vfRelabeling_bijective F.normalization.map.image e).surjective).comp
    (F.normalization.bijective h00).surjective

theorem proper (F : StandardContraction (G := G) A e) : ProperInvariant S F.target.carrier :=
  F.lift.originalTarget_proper

theorem doublyBounded (F : StandardContraction (G := G) A e) : VFDoublyBounded F.target.carrier :=
  F.lift.originalTarget_doublyBounded

theorem pullback (F : StandardContraction (G := G) A e) : IsRVPullback F.target.carrier :=
  F.lift.originalTarget_pullback

theorem recover_target (F : StandardContraction (G := G) A e) (p : Mixed M n F.arity) :
    p ∈ F.target.carrier ↔ (Fin.elim0,p.2) ∈ F.rvTarget.carrier ∧
      ∀ i,rv M (p.1 i)=p.2 (F.program.volumeIndex (e.symm i)) := F.lift.originalTarget_recover p

theorem homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : StandardContraction (G := G) A e) : ProperCovariantHomeomorphism F.map :=
  F.normalization.normalizedOrderedMap_homeomorphism h00 hc linear hκ hs hv hsmall hΓ F.lift

theorem unit_derivative_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hn : 0 < n) (F : StandardContraction (G := G) A e) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧ ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt F.map p :=
  F.normalization.normalizedOrderedMap_unit_derivative_ae h00 hc hκ hs hv hsmall hn F.lift

end StandardContraction

theorem lemma_6_27
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (e : Equiv.Perm (Fin n)) : Nonempty (StandardContraction (G := G) A e) := by
  obtain ⟨D,q,U,T,⟨V⟩⟩ := lemma_6_27_normalized h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA e
  exact ⟨⟨D,q,U,T,V⟩⟩

end DiamondIntegral.Section6
