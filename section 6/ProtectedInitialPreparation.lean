import «section 6».UnaryProperPreparationCore
import «section 6».ZeroCenteredPullbacks

/-! The original-base preliminary preparation can simultaneously protect
any finite proper invariant family, in every VF arity. Its regularized
image is doubly bounded and tagged; RV-pullbacks remain RV-pullbacks. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_protected_zeroCentered_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ D : ZeroCenteredData A, ∀ i, ∃ E : ZeroCenteredData (C i), ∀ p, E.point p = D.point p := by
  let H : Fin (k+1) → Set (Mixed M n r) := Fin.cons A.carrier (fun i => (C i).carrier)
  have hH : ∀ i, ProperInvariant S (H i) := Fin.cases hA hC
  obtain ⟨δ,hδ,hδ0,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  obtain ⟨c,hc0,hcdef,hcδ⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ0 hδ
  let D : ZeroCenteredData A := ⟨hA,c,hc0,hcdef,fun u => (hInv 0 u).larger_radius (fun _ => hcδ.le)⟩
  refine ⟨D,fun i => ?_⟩
  let E : ZeroCenteredData (C i) := ⟨hC i,c,hc0,hcdef,fun u => (hInv i.succ u).larger_radius (fun _ => hcδ.le)⟩
  exact ⟨E,fun _ => rfl⟩

def zeroPreparationMap {A : DefSet (rawMixedSpace (M := M) n r) S} (D : ZeroCenteredData A) :=
  (regularization D.map.image).comp D.bijection

theorem zeroPreparationMap_chain {A : DefSet (rawMixedSpace (M := M) n r) S} (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    SpecialCovariantChain (G := G) A (regularizeMap D.map.image).image (zeroPreparationMap D) :=
  .comp (.zeroCentered A D) (.regularize D.map.image (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded)

theorem exists_initial_preparation_protecting_family
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ B : DefSet (rawMixedSpace (M := M) n (n+(n+r))) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧
      (IsRVPullback A.carrier → IsRVPullback B.carrier) ∧
      (∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        ProperInvariant S (f.restrict (hCA i)).image.carrier := by
  obtain ⟨D,hProtected⟩ := exists_protected_zeroCentered_data h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt A hA C hC
  let B := (regularizeMap D.map.image).image
  let f := zeroPreparationMap D
  have hf := zeroPreparationMap_chain (G := G) D h00 hc hκ hs hv
  have hB : ProperInvariant S B.carrier := regularization_properInvariant h00 hc hκ hs hv _
    (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded
  have hBD : VFDoublyBounded B.carrier := regularized_vfDoublyBounded D.image_vfDoublyBounded
  have hBRV : IsRVPullback A.carrier → IsRVPullback B.carrier :=
    fun h => regularization_rvPullback _ (D.image_rvPullback h)
  have htag : ∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
    rw [show B.carrier = regularize '' D.map.image.carrier from regularization_carrier _]
    exact regularized_tagged _
  refine ⟨B,f,hf,hB,hBD,hBRV,htag,fun i => ?_⟩
  obtain ⟨E,hEpoint⟩ := hProtected i
  have hg := zeroPreparationMap_chain (G := G) E h00 hc hκ hs hv
  have hpoint (p : C i) : (zeroPreparationMap E p).val = (f ⟨p.val,hCA i p.property⟩).val :=
    congrArg regularize (hEpoint p.val)
  have he := image_eq_of_surjective_liesOver f (zeroPreparationMap E) (hg.bijective h00).surjective (hCA i) hpoint
  refine ⟨hg.restriction_of_liesOver h00 f (hCA i) hpoint,?_⟩
  rw [← he]
  exact regularization_properInvariant h00 hc hκ hs hv _
    (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded

end DiamondIntegral.Section6
