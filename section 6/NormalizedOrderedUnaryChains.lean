import «section 6».RVDisplacementUnaryChains
import «section 6».PermutedOrderedUnaryChains
import «section 6».NormalizedOrderedContractionLifts

/-! The permitted preliminary zero-centered normalization factors into
actual relatively unary maps in every positive VF dimension. Combining
this with a given ordered program gives the full finite composition on
the original source, in its original coordinate order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
namespace ZeroCenteredData

theorem relatively_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hn : 0<n) (D : ZeroCenteredData A) :
    ∃ F : RetainedUnaryHomeChain (G := G) S D.bijection (Fin.natAdd n),VFDoublyBounded A.carrier → F.DoublyBounded := by
  have hRetain (p : A) (i : Fin r) : (D.bijection p).val.2 (Fin.natAdd n i)=p.val.2 i := by
    change D.tags p.val.2 (D.core p.val) (Fin.natAdd n i)=p.val.2 i
    simp only [tags,Fin.append_right]
  obtain ⟨F,hF⟩ := unary_chain_of_rv_displacements h00 hc linear hκ hs hv hsmall hΓ hn D.bijection
    (D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ) (Fin.natAdd n) hRetain (D.rv_displacement h00)
  exact ⟨F,fun hAD => hF hAD D.image_vfDoublyBounded⟩

theorem normalizedOrderedMap_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hn : 0<n) (D : ZeroCenteredData A) {e : Equiv.Perm (Fin n)}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U}
    (V : OrderedStandardContractionLift T) :
    ∃ F : RetainedUnaryHomeChain (G := G) S (D.normalizedOrderedMap V) (T.oldLabels ∘ Fin.natAdd n),
      VFDoublyBounded A.carrier → F.DoublyBounded := by
  obtain ⟨F,hF⟩ := D.relatively_unary_chain h00 hc linear hκ hs hv hsmall hΓ hn
  obtain ⟨H,hH⟩ := V.originalMap_bounded_unary_chain h00 hc linear hκ hs hv hsmall hΓ
    (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded
  exact ⟨.comp F H,fun hAD => ⟨hF hAD,hH⟩⟩

end ZeroCenteredData
end DiamondIntegral.Section6
