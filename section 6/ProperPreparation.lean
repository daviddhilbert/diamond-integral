import «section 6».DimensionPreparation
import «section 6».ProtectedInitialPreparation

/-! Proposition 6.19 in every VF arity, with one actual special
covariant bijection and its literal restrictions to every protected
proper invariant set. No disjointness or covering hypothesis is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem proposition_6_19
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) n s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (f.restrict (hPA i)).image (f.restrict (hPA i)).toImage ∧
        IsRVPullback (f.restrict (hPA i)).image.carrier := by
  obtain ⟨A₀,f₀,hf₀,hA₀,hD₀,hRP₀,hTag₀,hPieces₀⟩ := exists_initial_preparation_protecting_family
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA P hPA hP
  let P₀ (i : Fin k) := (f₀.restrict (hPA i)).image
  have hP₀A₀ (i : Fin k) : (P₀ i).carrier ⊆ A₀.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (f₀ ⟨p.val,hPA i p.property⟩).property
  obtain ⟨F⟩ := synchronized_preparation_all_dimensions h00 hc linear hκ hs hv n
    S V hsmall hΓ hV hVS hSV hnt k _ A₀ hA₀ hD₀ (hRP₀ hARV) P₀ hP₀A₀ (fun i => (hPieces₀ i).2)
  let g := F.map.comp f₀
  refine ⟨F.arity,F.target,g,.comp hf₀ F.chain.toChain.toSpecial,F.proper,F.doublyBounded,F.pullback,fun i => ?_⟩
  have hFi := (F.chain.atPiece i).literal_restriction h00 (hP₀A₀ i)
  have hComp := SpecialCovariantChain.comp (hPieces₀ i).1 hFi
  have hImage : (F.map.restrict (hP₀A₀ i)).image=(g.restrict (hPA i)).image :=
    image_eq_of_surjective_liesOver g
      ((F.map.restrict (hP₀A₀ i)).toImage.comp (f₀.restrict (hPA i)).toImage)
      (hComp.bijective h00).surjective (hPA i) (fun _ => rfl)
  exact ⟨hComp.restriction_of_liesOver h00 g (hPA i) (fun _ => rfl),hImage ▸ F.prepared i⟩

end DiamondIntegral.Section6
