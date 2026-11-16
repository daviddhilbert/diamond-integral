import «section 6».UnaryLabelCenters

/-! A finite original-base exceptional set can be distinguished by
retained RV labels using an actual special covariant prefix. The ambient
source stays proper, doubly bounded, tagged and an RV-pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unary_special_finite_center_separation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (hE : E.carrier.Finite) :
    ∃ s : ℕ,∃ B : DefSet (rawMixedSpace (M := M) 1 s) S,∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      (∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) ∧
      ∀ p q : (f.restrict hEA).image,p.val.2=q.val.2 → p=q := by
  let R : UnaryRootFamily A := {
    roots := E
    subset := hEA
    finite := fun u => hE.preimage (by
      intro x hx y hy he
      exact congrArg (fun z : Mixed M 1 r => z.1 0) he) }
  obtain ⟨s,B,f,hProcess,hChain,hB,hBD,hBTag,hBRV,hSeparate⟩ := R.exists_separating_process
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hA hD hTag
  refine ⟨s,B,f,hChain,hB,hBD,hBRV hRV,hBTag,fun p q he => ?_⟩
  obtain ⟨x,hx⟩ := p.property
  obtain ⟨y,hy⟩ := q.property
  let xA : A := ⟨x.val,hEA x.property⟩
  let yA : A := ⟨y.val,hEA y.property⟩
  have hxyTags : (f xA).val.2=(f yA).val.2 := by
    have hxTags := congrArg (fun z : Mixed M 1 s => z.2) hx
    have hyTags := congrArg (fun z : Mixed M 1 s => z.2) hy
    exact hxTags.trans (he.trans hyTags.symm)
  have hxy : xA=yA := hSeparate xA x.property yA y.property hxyTags
  apply Subtype.ext
  exact hx.symm.trans ((congrArg (fun a : A => (f a).val) hxy).trans hy)

end DiamondIntegral.Section6
