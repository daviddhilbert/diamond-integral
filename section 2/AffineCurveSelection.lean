import «section 2».CurveGluing
import «section 2».CurveSource
import «section 2».FiniteVFSubset

/-!
# The affine case of Lemma 2.46

All components of the approved proof are assembled: algebraic-closure
modelhood, finite-valued choice, generic unary continuity, a same-base
clopen neighbourhood and extension by a finite nonempty constant set.
Projective boundary points with infinite coordinates are not covered by
the affine statement in this module.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_2_46_affine_core
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) {n : ℕ}
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (b : Fin n → VF M) (hbS : ∀ i, (b i).val ∈ S) (hb : b ∈ closure A) :
    ∃ F : (Fin 1 → VF M) → Set (Fin n → VF M),
      S.Definable LRV (vfCorrespondenceGraph curveSource F) ∧
      (∀ c, (F c).Finite) ∧
      (∀ c ∈ curveSource, (F c).Nonempty ∧ F c ⊆ A) ∧
      (∀ c ∈ curveSource, HasMinimalLimitSet curveSource c F (F c)) ∧
      HasMinimalLimitSet curveSource 0 F {b} := by
  obtain ⟨F,hF,hfin,hvalues,hlim,E,hEU,hEf,hE,hcont⟩ :=
    exists_affine_approach_germ h00 hc hκ hs hv V S hV hVS hSV hnt hsmall
      curveSource (curveSource_definable S) curveSource_nonzero curveSource_accumulates
      A hA b hbS hb
  have hneA : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he,closure_empty] at hb
    exact hb.elim
  obtain ⟨C,hCA,hCf,hCne,hC⟩ := exists_nonempty_finite_definable_vf_subset
    Valued.v hv hc h00 V S hV hVS hSV hnt A hA hneA
  exact finite_exception_curve_extension hv curveSource (curveSource_definable S)
    (curveSource_isOpen hv) curveSource_nonzero A b F hF hfin hvalues hlim
    E hEU hEf hE hcont C hCf hCne hCA hC

/-- Lemma 2.46 at every affine closure point, over the original VF-generated
base plus exactly b. Modelhood, choice and continuity exceptions are not
additional premises. The remaining infinite-coordinate case is separate. -/
theorem lemma_2_46_affine
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (S : Set M) < κ) {n : ℕ}
    (A : Set (Fin n → VF M)) (hA : (S : Set M).Definable LRV (vfValues '' A))
    (b : Fin n → VF M) (hb : b ∈ closure A) :
    ∃ F : (Fin 1 → VF M) → Set (Fin n → VF M),
      ((S : Set M) ∪ Set.range (vfValues b)).Definable LRV (vfCorrespondenceGraph curveSource F) ∧
      (∀ c, (F c).Finite) ∧
      (∀ c ∈ curveSource, (F c).Nonempty ∧ F c ⊆ A) ∧
      (∀ c ∈ curveSource, HasMinimalLimitSet curveSource c F (F c)) ∧
      HasMinimalLimitSet curveSource 0 F {b} := by
  let V := vfFieldNames B.field ∪ Set.range (vfValues b)
  let T : Set M := (S : Set M) ∪ Set.range (vfValues b)
  have hV : ∀ x ∈ V, iVF x := by
    rintro x (hx | ⟨i,rfl⟩)
    · obtain ⟨a,ha,rfl⟩ := hx
      exact a.property
    · exact (b i).property
  have hVT : V ⊆ T := Set.union_subset_union B.fieldNames_subset (Set.Subset.refl _)
  have hTV : T ⊆ algebraicClosureSet V := by
    rintro x (hx | hx)
    · obtain ⟨σ,hσ⟩ := B.definable_over_fieldNames x hx
      exact ⟨σ,hσ.algebraic.mono Set.subset_union_left⟩
    · exact subset_algebraicClosureSet V (Or.inr hx)
  have hntV : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1 := by
    obtain ⟨x,hx0,hxv⟩ := hnt
    have hname : x.val.val ∈ V := Or.inl ⟨x.val,x.property,rfl⟩
    have hxV : x.val ∈ vfAlgebraicClosureField V :=
      (mem_vfAlgebraicClosureField V x.val).mpr
        (definableClosureAt_of_mem (σ := .vf) hname x.val.property).algebraic
    refine ⟨⟨x.val,hxV⟩,?_,hxv⟩
    intro he
    have heval : x.val = 0 := congrArg (fun y : vfAlgebraicClosureField V => y.val) he
    exact hx0 (Subtype.ext heval)
  exact lemma_2_46_affine_core h00 hc hκ hs hv V T hV hVT hTV hntV
    (small_union_range hκ (S : Set M) hsmall (vfValues b)) A
    (hA.mono Set.subset_union_left) b (fun i => Or.inr (Set.mem_range_self i)) hb

end DiamondIntegral.Section2
