import «section 6».ReindexedUnaryHomeChains
import «section 6».BoundedOrderedUnaryChains
import «section 6».PermutedOrderedContractionLifts

/-! The full lift in the original coordinate order has the transported
finite relatively unary composition, including all intermediate bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def changeSourceMap (f : Map A B) (he : A=C) : Map C B := he ▸ f

theorem changeSourceMap_value (f : Map A B) (he : A=C) (p : C) :
    (changeSourceMap f he p).val=(f ⟨p.val,he.symm ▸ p.property⟩).val := by
  cases he
  rfl

def RetainedUnaryHomeChain.changeSource {f : Map A B} {π : Fin r → Fin s}
    (F : RetainedUnaryHomeChain (G := G) S f π) (he : A=C) :
    RetainedUnaryHomeChain (G := G) S (changeSourceMap f he) π := by
  cases he
  exact F

theorem RetainedUnaryHomeChain.doublyBounded_changeSource {f : Map A B} {π : Fin r → Fin s}
    (F : RetainedUnaryHomeChain (G := G) S f π) (he : A=C) :
    (F.changeSource he).DoublyBounded ↔ F.DoublyBounded := by
  cases he
  rfl

variable {e : Equiv.Perm (Fin n)} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet A e) U}

theorem OrderedStandardContractionLift.originalMap_conjugation (V : OrderedStandardContractionLift T) :
    changeSourceMap (reindexVFConjugate V.map e.symm) (reindexedVFSet_inverse A e)=V.originalMap := by
  apply Map.ext
  intro p
  apply Subtype.ext
  rw [changeSourceMap_value,reindexVFConjugate_value,originalMap_value]
  have hInput : reindexVFInverseMap (reindexedVFSet A e) e.symm
      ⟨p.val,(reindexedVFSet_inverse A e).symm ▸ p.property⟩=vfRelabeling A e p := Subtype.ext rfl
  rw [hInput]

theorem OrderedStandardContractionLift.originalMap_bounded_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : OrderedStandardContractionLift T) (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) :
    ∃ F : RetainedUnaryHomeChain (G := G) S V.originalMap T.oldLabels,F.DoublyBounded := by
  obtain ⟨F,hF⟩ := V.bounded_relatively_unary_chain h00 hc linear hκ hs hv hsmall hΓ
    (reindexedVFSet_properInvariant A e hA) (reindexedVFSet_doublyBounded A e hAD)
  let H := F.reindex h00 hc linear hκ hs hv hsmall hΓ e.symm
  let K := H.changeSource (reindexedVFSet_inverse A e)
  refine ⟨K.changeMap V.originalMap_conjugation,?_⟩
  apply (K.doublyBounded_changeMap _).mpr
  apply (H.doublyBounded_changeSource _).mpr
  exact F.doublyBounded_reindex h00 hc linear hκ hs hv hsmall hΓ e.symm hF

end DiamondIntegral.Section6
