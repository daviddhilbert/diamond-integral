import «section 6».FiniteVFPairedCores
import «section 6».SeparatedUnaryOffsetCores
import «section 6».UnaryFiniteFieldImages

/-! Separated paired offsets for a finite VF projection with arbitrary
bounded retained RV labels. Only the finite scalar centre images are
used in the separating-radius choice. -/

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

theorem exists_separated_unary_offset_cores_finiteVF
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hEVF : (Prod.fst '' E.carrier).Finite) (hERV : RVSupportDoublyBounded E.carrier)
    (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    Nonempty (SeparatedUnaryOffsetCores f E hEA α β) := by
  let aMap := mixedVFHeadMap E
  let bMap := (mixedVFHeadMap B).comp (f.restrict hEA)
  let H := scalarFocusImage aMap ∪ scalarFocusImage bMap
  have hH : S.Definable₁ LRV (Subtype.val '' H) := by
    rw [Set.image_union]
    exact (scalarFocusImage_definable aMap).union (scalarFocusImage_definable bMap)
  have hAFin : (scalarFocusImage aMap).Finite := by
    apply (hEVF.image (fun x : Fin 1 → VF M => x 0)).subset
    rintro x ⟨p,rfl⟩
    exact ⟨p.val.1,⟨p.val,p.property,rfl⟩,rfl⟩
  have hBFin : (scalarFocusImage bMap).Finite := by
    apply ((unaryFieldImage_finite hc hκ hs hsmall f E.carrier hEVF).image
      (fun x : Fin 1 → VF M => x 0)).subset
    rintro x ⟨p,rfl⟩
    exact ⟨(f ⟨p.val,hEA p.property⟩).val.1,⟨⟨p.val,hEA p.property⟩,p.property,rfl⟩,rfl⟩
  have hHFin : H.Finite := hAFin.union hBFin
  obtain ⟨t,ht0,htNamed,htPos,hSeparate⟩ := exists_named_separating_radius h00 hc hv
    V hV hVS hSV hnt H hH hHFin
  let ρ := finiteValue t ht0
  have hρ := finiteValue_named t ht0 htNamed (S := S)
  obtain ⟨D⟩ := exists_uniform_paired_cores_finiteVF h00 hc linear hκ hs hv hsmall hΓ V hV hVS hSV hnt
    f hf hRV hD E hEA hEVF hERV (max α ρ) (max β ρ)
    (gamma_max_named α ρ hα hρ) (gamma_max_named β ρ hβ hρ)
  have hSource (p : E) : ρ≤finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p) :=
    (le_max_right _ _).trans (show max α ρ<finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p) from D.sourceFloor p).le
  have hTarget (p : E) : ρ≤finiteValue ((D.targetOffset p).val 0) (D.targetNonzero p) :=
    (le_max_right _ _).trans (show max β ρ<finiteValue ((D.targetOffset p).val 0) (D.targetNonzero p) from D.targetFloor p).le
  refine ⟨{
    sourceOffset := D.sourceOffset
    targetOffset := D.targetOffset
    sourceNonzero := D.sourceNonzero
    targetNonzero := D.targetNonzero
    sourceFloor := fun p => (show α.val≤(max α ρ).val from le_max_left _ _).trans_lt (D.sourceFloor p)
    targetFloor := fun p => (show β.val≤(max β ρ).val from le_max_left _ _).trans_lt (D.targetFloor p)
    sourceDisc := D.sourceDisc
    targetDisc := D.targetDisc
    image := D.image
    sourceSeparated := ?_
    targetSeparated := ?_ }⟩
  · intro p q hpq
    apply unaryTaggedDisc_disjoint_of_separated_scalar_discs p.val q.val _ _ ρ
      (fun he => hpq (Subtype.ext he)) (hSource p) (hSource q)
    exact hSeparate _ (Or.inl ⟨p,rfl⟩) _ (Or.inl ⟨q,rfl⟩)
  · intro p q hpq
    have hne : (f ⟨p.val,hEA p.property⟩).val≠(f ⟨q.val,hEA q.property⟩).val := by
      intro he
      have h := hf.bijective.injective (Subtype.ext he)
      have hValue := congrArg (fun a : A => a.val) h
      exact hpq (Subtype.ext hValue)
    apply unaryTaggedDisc_disjoint_of_separated_scalar_discs _ _ _ _ ρ hne (hTarget p) (hTarget q)
    exact hSeparate _ (Or.inr ⟨p,rfl⟩) _ (Or.inr ⟨q,rfl⟩)

end DiamondIntegral.Section6
