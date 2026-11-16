import «section 6».NormalizedOrderedContractionLifts

/-! Full binary standard-contraction existence with the permitted
preliminary normalization and any coordinate order. The public object
contains the actual program, its lift and the map on the original source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure BinaryStandardContraction (A : DefSet (rawMixedSpace (M := M) 2 r) S) (e : Equiv.Perm (Fin 2)) where
  normalization : ZeroCenteredData A
  arity : ℕ
  rvTarget : DefSet (rawMixedSpace (M := M) 0 arity) S
  program : OrderedStandardContractionProgram (G := G) S (reindexedVFSet normalization.map.image e) rvTarget
  lift : OrderedStandardContractionLift program

namespace BinaryStandardContraction
variable {A : DefSet (rawMixedSpace (M := M) 2 r) S} {e : Equiv.Perm (Fin 2)}

def target (F : BinaryStandardContraction (G := G) A e) := F.lift.originalTarget

def map (F : BinaryStandardContraction (G := G) A e) : Map A F.target :=
  F.normalization.normalizedOrderedMap F.lift

def contraction (F : BinaryStandardContraction (G := G) A e) : Map A F.rvTarget :=
  F.lift.originalContraction.comp F.normalization.bijection

theorem labels (F : BinaryStandardContraction (G := G) A e) (p : A) :
    (F.map p).val.2=(F.contraction p).val.2 := F.lift.originalMap_labels _

theorem contraction_surjective (h00 : M ⊨ Axioms.ACVF00) (F : BinaryStandardContraction (G := G) A e) :
    Function.Surjective F.contraction :=
  (F.program.surjective.comp (vfRelabeling_bijective F.normalization.map.image e).surjective).comp
    (F.normalization.bijective h00).surjective

theorem proper (F : BinaryStandardContraction (G := G) A e) : ProperInvariant S F.target.carrier :=
  F.lift.originalTarget_proper

theorem doublyBounded (F : BinaryStandardContraction (G := G) A e) : VFDoublyBounded F.target.carrier :=
  F.lift.originalTarget_doublyBounded

theorem pullback (F : BinaryStandardContraction (G := G) A e) : IsRVPullback F.target.carrier :=
  F.lift.originalTarget_pullback

theorem recover_target (F : BinaryStandardContraction (G := G) A e) (p : Mixed M 2 F.arity) :
    p ∈ F.target.carrier ↔ (Fin.elim0,p.2) ∈ F.rvTarget.carrier ∧
      ∀ i,rv M (p.1 i)=p.2 (F.program.volumeIndex (e.symm i)) := F.lift.originalTarget_recover p

theorem homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : BinaryStandardContraction (G := G) A e) : ProperCovariantHomeomorphism F.map :=
  F.normalization.normalizedOrderedMap_homeomorphism h00 hc linear hκ hs hv hsmall hΓ F.lift

theorem unit_derivative_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (F : BinaryStandardContraction (G := G) A e) :
    ∃ E : DefSet (rawMixedSpace (M := M) 2 r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < 2 ∧ ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt F.map p :=
  F.normalization.normalizedOrderedMap_unit_derivative_ae h00 hc hκ hs hv hsmall (by decide) F.lift

end BinaryStandardContraction

theorem lemma_6_27_binary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (e : Equiv.Perm (Fin 2)) : Nonempty (BinaryStandardContraction (G := G) A e) := by
  obtain ⟨D,q,U,T,⟨V⟩⟩ := lemma_6_27_binary_normalized h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA e
  exact ⟨⟨D,q,U,T,V⟩⟩

end DiamondIntegral.Section6
