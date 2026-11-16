import «section 6».ProperPreparation

/-! The full Proposition 6.19 over the manuscript's actual VF-generated
field base, retaining smallness, saturation, the accepted Gamma input
and nontriviality of the valuation on the specified field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem proposition_6_19_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) (S : Set M))
    (hA : ProperInvariant (S : Set M) A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) (S : Set M))
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant (S : Set M) (P i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) n s) (S : Set M), ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant (S : Set M) B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (f.restrict (hPA i)).image (f.restrict (hPA i)).toImage ∧
        IsRVPullback (f.restrict (hPA i)).image.carrier := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B₀ hnt
  exact proposition_6_19 h00 hc linear hκ hs hv (vfFieldNames B₀.field) hsmall hΓ
    hV hVS hSV hnt' A hA hARV P hPA hP

end DiamondIntegral.Section6
