import «section 6».BranchedShearDimensionInduction
import «section 6».OrderedContractionLiftProperties
import «section 6».PermutedOrderedContractionLifts

/-! Ordered standard-contraction existence in every VF dimension.
Actual first stages and the whole recursive lift are constructed for
all doubly bounded proper sources. Arbitrary proper sources and every
coordinate order use the permitted zero-centered normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem ordered_standard_program_all_dimensions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) (n : ℕ) :
    ∀ r,∀ A : DefSet (rawMixedSpace (M := M) n r) S,ProperInvariant S A.carrier → VFDoublyBounded A.carrier →
      ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
        Nonempty (OrderedStandardContractionProgram (G := G) S A U) := by
  induction n with
  | zero =>
    intro r A hA hD
    exact ⟨r,A,⟨.zero A⟩⟩
  | succ n ih =>
    intro r A hA hD
    obtain ⟨T⟩ := exists_shear_contraction_stage_all_dimensions h00 hc linear hκ hs hv S V hsmall hΓ
      hV hVS hSV hnt A hA hD
    obtain ⟨q,U,⟨tail⟩⟩ := ih T.stage.arity T.stage.contracted T.stage.contracted_proper T.stage.contracted_doublyBounded
    exact ⟨q,U,⟨.step T.stage tail⟩⟩

theorem lemma_6_27_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S A U,Nonempty (OrderedStandardContractionLift T) := by
  obtain ⟨q,U,⟨T⟩⟩ := ordered_standard_program_all_dimensions h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt n r A hA hD
  exact ⟨q,U,T,exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ T hA⟩

theorem contraction_any_order_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (hD : VFDoublyBounded A.carrier) (e : Equiv.Perm (Fin n)) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet A e) U,
        Nonempty (OrderedStandardContractionLift T) :=
  lemma_6_27_doublyBounded h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    (reindexedVFSet A e) (reindexedVFSet_properInvariant A e hA) (reindexedVFSet_doublyBounded A e hD)

theorem lemma_6_27_normalized
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) (e : Equiv.Perm (Fin n)) :
    ∃ D : ZeroCenteredData A,∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U,
        Nonempty (OrderedStandardContractionLift T) := by
  obtain ⟨D⟩ := exists_zeroCentered_data h00 hc linear hκ hs hv V S hsmall hΓ hV hVS hSV hnt A hA
  obtain ⟨q,U,T,hLift⟩ := contraction_any_order_doublyBounded h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt D.map.image (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded e
  exact ⟨D,q,U,T,hLift⟩

end DiamondIntegral.Section6
