import «section 6».SeparatedPairedCorePreparation

/-! A finite actual paired center family with separated old labels has
whole-ambient paired core preparations over the original base. All
offsets, smallness bounds and whole-core matching are constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem exists_named_finite_paired_core_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hATag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (hFinite : E.carrier.Finite)
    (hUS : ∀ p q : E,p.val.2=q.val.2 → p=q)
    (hUT : ∀ p q : E,(f ⟨p.val,hEA p.property⟩).val.2=(f ⟨q.val,hEA q.property⟩).val.2 → p=q) :
    Nonempty (PairedAmbientCorePreparation (G := G) f E hEA) := by
  letI : Fintype E := hFinite.fintype
  let aMap := mixedVFHeadMap E
  let bMap := (mixedVFHeadMap B).comp (f.restrict hEA)
  let K := scalarFocusImage aMap ∪ scalarFocusImage bMap
  have hK : S.Definable₁ LRV (Subtype.val '' K) := by
    change S.Definable₁ LRV (Subtype.val '' (scalarFocusImage aMap ∪ scalarFocusImage bMap))
    rw [Set.image_union]
    exact (scalarFocusImage_definable aMap).union (scalarFocusImage_definable bMap)
  have hFiniteK : K.Finite := (Set.finite_range _).union (Set.finite_range _)
  have hNZ : ∀ x ∈ K,x ≠ 0 := by
    intro x hx
    rcases hx with (⟨p,rfl⟩ | ⟨p,rfl⟩)
    · exact hAD.nonzero (hEA p.property) 0
    · exact hBD.nonzero (f ⟨p.val,hEA p.property⟩).property 0
  obtain ⟨t,ht0,htDef,htPos,htAbove⟩ := exists_named_vf_above_finite_family h00 hc hv V hV hVS hSV hnt K hK hFiniteK hNZ
  let ρ := finiteValue t ht0
  have hρ := finiteValue_named t ht0 htDef (S := S)
  obtain ⟨D⟩ := exists_uniform_finite_paired_cores h00 hc hκ.le hs hsmall hv V hV hVS hSV hnt f hf
    hARV hAD E hEA hFinite ρ ρ hρ hρ
  have hSmallS (p : E) : vfValue (p.val.1 0) < vfValue ((D.sourceOffset p).val 0) :=
    (htAbove (p.val.1 0) (Or.inl ⟨p,rfl⟩)).trans (D.sourceFloor p)
  have hSmallT (p : E) : vfValue ((f ⟨p.val,hEA p.property⟩).val.1 0) < vfValue ((D.targetOffset p).val 0) :=
    (htAbove ((f ⟨p.val,hEA p.property⟩).val.1 0) (Or.inr ⟨p,rfl⟩)).trans (D.targetFloor p)
  exact paired_ambient_core_preparation_of_small_offsets h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    f hf.bijective hA hAD hARV hATag hB hBD hBRV hBTag E hEA hUS hUT ρ ρ D hSmallS hSmallT

end DiamondIntegral.Section6
