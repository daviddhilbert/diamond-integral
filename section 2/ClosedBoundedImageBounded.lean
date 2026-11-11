import «section 2».ClosedBoundedImageClosed
import «section 2».InfinityApproach

/-!
# Boundedness of the image in Lemma 2.48

Failure of a common output bound gives a definable escaping family.
Finite choices in the closed bounded source have a finite affine limit;
relative continuity gives a finite output limit, contradicting escape.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem closed_bounded_image_bounded_vf_core
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) (hAcl : IsClosed A)
    (hAb : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) (hfcont : ContinuousOn f A) :
    ∃ γ : Gamma M, ∀ y ∈ f '' A, ∀ i, γ.val ≤ vfValue (y i) := by
  classical
  by_contra hB
  let P := vfPullback A f (vfEscape (f '' A))
  have hP : S.Definable LRV (vfCorrespondenceGraph curveSource P) :=
    vfPullback_graph_definable A f hf curveSource _
      (vfEscape_graph_definable curveSource (curveSource_definable S) (f '' A)
        (vf_map_image_definable A f hf))
  have hPne : ∀ c ∈ curveSource, (P c).Nonempty := by
    intro c hcU
    obtain ⟨y,hy⟩ := vfEscape_nonempty_of_unbounded (f '' A) hB c (curveSource_nonzero c hcU)
    obtain ⟨x,hx,he⟩ := hy.1
    refine ⟨x,hx,?_⟩
    rwa [he]
  obtain ⟨F,hF,hfin,hsub,hne⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V S hV hVS hSV
    hnt hsmall curveSource (curveSource_definable S) P hP hPne
  have hFA : ∀ c ∈ curveSource, F c ⊆ A := fun c _ x hx => (hsub c hx).1
  obtain ⟨L,hLf,hLA,hL,hLdef⟩ := lemma_2_45 hc hs hsmall hv curveSource F A hAcl hAb hF
    (fun c _ => hfin c) hFA
  have hImage : HasMinimalLimitSet curveSource 0 (fun c => f '' F c) (f '' L) :=
    hL.image_of_continuousWithinAt hv hLf A hFA f (fun a ha => hfcont a (hLA ha))
  apply hImage.1.no_reciprocal_escape (hLf.image f)
    (fun c hcU => ((hne c).mpr hcU).image f)
  rintro c hcU _ ⟨x,hx,rfl⟩
  obtain ⟨i,hi⟩ := (hsub c hx).2.2
  exact ⟨i,(vfInfinitySide_iff (c 0) (f x i) (curveSource_nonzero c hcU)).mp hi⟩

theorem lemma_2_48_image_bounded_vf_generated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (A : Set (Fin n → VF M)) (hA : (S : Set M).Definable LRV (vfValues '' A)) (hAcl : IsClosed A)
    (hAb : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : (S : Set M).Definable LRV (vfCorrespondenceGraph A (fun x => {f x})))
    (hfcont : ContinuousOn f A) :
    ∃ γ : Gamma M, ∀ y ∈ f '' A, ∀ i, γ.val ≤ vfValue (y i) := by
  let p : Fin 0 → VF M := Fin.elim0
  obtain ⟨hV,hVT,hTV,hntV⟩ := VFGeneratedFieldBase.parameter_core Valued.v S B hnt p
  exact closed_bounded_image_bounded_vf_core h00 hc hs hv
    (vfFieldNames B.field ∪ Set.range (vfValues p)) ((S : Set M) ∪ Set.range (vfValues p))
    hV hVT hTV hntV (small_union_range hκ (S : Set M) hsmall (vfValues p))
    A (hA.mono Set.subset_union_left) hAcl hAb f (hf.mono Set.subset_union_left) hfcont

end DiamondIntegral.Section2
