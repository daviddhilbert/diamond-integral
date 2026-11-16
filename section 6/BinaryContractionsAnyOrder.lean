import «section 6».BinaryOrderedContractions
import «section 6».PermutedOrderedContractionLifts

/-! Every binary coordinate order has an actual program and full lift.
Arbitrary proper sources use exactly the preliminary normalization
permitted in the paper, followed by the prescribed coordinate order. -/

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

theorem binary_contraction_any_order_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) (e : Equiv.Perm (Fin 2)) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet A e) U,
        Nonempty (OrderedStandardContractionLift T) :=
  lemma_6_27_binary_doublyBounded h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    (reindexedVFSet A e) (reindexedVFSet_properInvariant A e hA) (reindexedVFSet_doublyBounded A e hAD)

theorem lemma_6_27_binary_normalized
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (e : Equiv.Perm (Fin 2)) :
    ∃ D : ZeroCenteredData A,∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U,
        Nonempty (OrderedStandardContractionLift T) := by
  obtain ⟨D⟩ := exists_zeroCentered_data h00 hc linear hκ hs hv V S hsmall hΓ hV hVS hSV hnt A hA
  obtain ⟨q,U,T,hLift⟩ := binary_contraction_any_order_doublyBounded h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt D.map.image (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded e
  exact ⟨D,q,U,T,hLift⟩

end DiamondIntegral.Section6
