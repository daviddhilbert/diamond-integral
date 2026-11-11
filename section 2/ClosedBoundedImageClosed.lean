import «section 2».ClosedBoundedLimitCore
import «section 2».CorrespondencePullback
import «section 2».ParameterCores

/-!
# Closedness of the image in Lemma 2.48

Elementarity and finite choice construct the family of inverse images of
shrinking target balls. The bounded finite-limit theorem and relative
continuity put every affine image-closure point in the image. The final
wrapper here has the explicitly recorded VF-generated base scope.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem closed_bounded_image_mem_vf_core
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
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) (hfcont : ContinuousOn f A)
    (b : Fin m → VF M) (hbS : ∀ i, (b i).val ∈ S) (hb : b ∈ closure (f '' A)) :
    b ∈ f '' A := by
  let P := vfPullback A f (vfApproach (f '' A) b)
  have hP : S.Definable LRV (vfCorrespondenceGraph curveSource P) :=
    vfPullback_graph_definable A f hf curveSource _
      (vfApproach_graph_definable curveSource (curveSource_definable S) (f '' A)
        (vf_map_image_definable A f hf) b hbS)
  have hPne : ∀ c ∈ curveSource, (P c).Nonempty := by
    intro c hcU
    obtain ⟨y,hy⟩ := vfApproach_nonempty_of_mem_closure hv (f '' A) b hb c (curveSource_nonzero c hcU)
    obtain ⟨x,hx,he⟩ := hy.1
    refine ⟨x,hx,?_⟩
    rwa [he]
  obtain ⟨F,hF,hfin,hsub,hne⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V S hV hVS hSV
    hnt hsmall curveSource (curveSource_definable S) P hP hPne
  have hFA : ∀ c ∈ curveSource, F c ⊆ A := fun c _ x hx => (hsub c hx).1
  obtain ⟨L,hLf,hLA,hL,hLdef⟩ := lemma_2_45 hc hs hsmall hv curveSource F A hAcl hAb hF
    (fun c _ => hfin c) hFA
  exact image_mem_of_approaching_finite_limit hv A f hfcont F L hL hLf hLA hFA
    (fun c hcU => (hne c).mpr hcU) b (fun c _ x hx => (hsub c hx).2.2)

/-- The closed-image conclusion of 2.48 in the VF-generated real-base
scope. Temporary naming of an arbitrary closure point is constructed. -/
theorem lemma_2_48_image_closed_vf_generated
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
    (hfcont : ContinuousOn f A) : IsClosed (f '' A) := by
  apply isClosed_of_closure_subset
  intro b hb
  obtain ⟨hV,hVT,hTV,hntV⟩ := VFGeneratedFieldBase.parameter_core Valued.v S B hnt b
  exact closed_bounded_image_mem_vf_core h00 hc hs hv
    (vfFieldNames B.field ∪ Set.range (vfValues b)) ((S : Set M) ∪ Set.range (vfValues b))
    hV hVT hTV hntV (small_union_range hκ (S : Set M) hsmall (vfValues b))
    A (hA.mono Set.subset_union_left) hAcl hAb f (hf.mono Set.subset_union_left) hfcont
    b (fun i => Or.inr (Set.mem_range_self i)) hb

end DiamondIntegral.Section2
