import «section 6».BinaryBaseProperPreparation
import «section 6».ComplementDisplacementMaps

/-! Prepare an arbitrary doubly bounded proper binary source while
retaining the actual base-displacement certificate. Source membership
is protected inside its RV hull; no RV-pullback source is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_displacement_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) :
    ∃ s,∃ B : DefSet (rawMixedSpace (M := M) 2 s) S,∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧ RVCoordinateDisplacement f 0 ∧
      ∃ k : Fin s,∀ p ∈ B.carrier,rv M (p.1 (Fin.last 1))=p.2 k := by
  let H : DefSet (rawMixedSpace (M := M) 2 r) S := ⟨rvHull A.carrier,hA.rvHull.definable⟩
  have hHD : VFDoublyBounded H.carrier := by
    obtain ⟨γ,hγ⟩ := hAD
    refine ⟨γ,fun p hp i => ?_⟩
    obtain ⟨z,hz,hVF,_⟩ := (mem_rvHull_iff A.carrier p).mp hp
    have he := congrArg Values.vrv (congrFun hVF i)
    change vfValue (z.1 i)=vfValue (p.1 i) at he
    rw [← he]
    exact hγ z hz i
  let H₀ := (regularizeMap H).image
  let R := (regularizeMap A).image
  let a₀ := regularization A
  have ha₀ : SpecialCovariantChain (G := G) A R a₀ := .regularize A hA hAD
  have hRH : R.carrier ⊆ H₀.carrier := by
    rintro q ⟨p,hp⟩
    exact ⟨⟨p.val,subset_rvHull A.carrier p.property⟩,hp⟩
  have hR := regularization_properInvariant h00 hc hκ hs hv A hA hAD
  have hH₀ := regularization_properInvariant h00 hc hκ hs hv H hA.rvHull hHD
  have hTag : ∀ p ∈ H₀.carrier,∀ z ∈ H₀.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
    rw [show H₀.carrier=regularize '' H.carrier from regularization_carrier H]
    exact regularized_tagged _
  let j : Fin (2+r) := Fin.castAdd r (Fin.last 1)
  have hLeading : ∀ p ∈ H₀.carrier,rv M (p.1 (Fin.last 1))=p.2 j := by
    rintro p ⟨b,hb⟩
    rw [← hb]
    change rv M ((regularize b.val).1 (Fin.last 1))=(regularize b.val).2 j
    simp only [j,regularize,Fin.append_left]
    rfl
  obtain ⟨s,Z,g,hg,hZ,hZD,hZRP,hDisp,hPieces⟩ := binary_tagged_preparation_with_base_displacement
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt H₀ hH₀ (regularized_vfDoublyBounded hHD)
    (regularization_rvPullback H (rvHull_idempotent A.carrier)) hTag j hLeading
    (fun _ : Fin 1 => R) (fun _ => hRH) (fun _ => hR)
  let B₀ := (g.restrict hRH).image
  let f₀ := (g.restrict hRH).toImage.comp a₀
  have hf₀ : SpecialCovariantChain (G := G) A B₀ f₀ := .comp ha₀ (hPieces 0).1
  have hB₀sub : B₀.carrier ⊆ Z.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (g ⟨p.val,hRH p.property⟩).property
  have hB₀D : VFDoublyBounded B₀.carrier := hZD.mono hB₀sub
  have hB₀Home := hf₀.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  have hB₀ := hB₀Home.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hB₀Home.bijective.surjective
  have hDisp₀ : RVCoordinateDisplacement f₀ (0 : Fin 2) := by
    intro p z he
    exact hDisp ⟨(a₀ p).val,hRH (a₀ p).property⟩ ⟨(a₀ z).val,hRH (a₀ z).property⟩ he
  let B := (regularizeMap B₀).image
  let b₀ := regularization B₀
  have hb₀ : SpecialCovariantChain (G := G) B₀ B b₀ := .regularize B₀ hB₀ hB₀D
  obtain ⟨hArity,hRetain⟩ := hb₀.retainsRV
  have hDispB : RVCoordinateDisplacement b₀ (0 : Fin 2) := .of_fixed 0 (fun _ => rfl)
  refine ⟨2+s,B,b₀.comp f₀,.comp hf₀ hb₀,
    regularization_properInvariant h00 hc hκ hs hv B₀ hB₀ hB₀D,
    regularized_vfDoublyBounded hB₀D,regularization_rvPullback B₀ (hPieces 0).2,
    hDisp₀.comp hDispB (rvTailIndex hArity) hRetain,Fin.castAdd s (Fin.last 1),?_⟩
  rintro p ⟨b,hb⟩
  rw [← hb]
  change rv M ((regularize b.val).1 (Fin.last 1))=(regularize b.val).2 (Fin.castAdd s (Fin.last 1))
  simp only [regularize,Fin.append_left]
  rfl

end DiamondIntegral.Section6
