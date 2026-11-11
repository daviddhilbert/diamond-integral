import «section 2».FiniteChoice
import «section 2».Bases
import Section4.RealPresentations

/-!
# Finite-valued choice over VF-generated bases

The already checked algebraic-closure elementary-substructure theorem
supplies the pointwise algebraic witnesses. The finite-choice theorem then
gives their complete graph over the original base. This is the modelhood
and compactness step in the approved curve-selection argument.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M]

/-- The finite-tuple version of the standard elementary-substructure
definable-witness criterion, including the empty tuple. -/
theorem elementary_meets_definable_tuple (C : LRV.ElementarySubstructure M) {n : ℕ}
    (A : Set (Fin n → M)) (hne : A.Nonempty) (hA : (C : Set M).Definable LRV A) :
    ∃ a ∈ A, ∀ i, a i ∈ (C : Set M) := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨φ,hφ⟩ := hA
  have hφa : φ.Realize a := by simpa [hφ] using ha
  let ψ : LRV[[(C : Set M)]].Sentence := (φ.relabel Sum.inr).iExs
  have hψM : ψ.Realize M := by
    simpa only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
      Formula.realize_relabel, Sum.elim_comp_inr, ψ] using
      (⟨a,hφa⟩ : ∃ w : Fin n → M, φ.Realize w)
  have hψC : ψ.Realize C := by
    rwa [← Formula.realize_equivSentence_symm_con, ← C.subtype.map_formula,
      Formula.realize_equivSentence_symm]
  simp only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
    Formula.realize_relabel, Sum.elim_comp_inr, ψ] at hψC
  obtain ⟨w,hw⟩ := hψC
  have hw' : φ.Realize (Subtype.val ∘ w) := by
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv,
      ← C.subtype.map_boundedFormula] at hw
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv]
    convert hw using 1
    funext i
    cases i <;> rfl
  exact ⟨Subtype.val ∘ w, by simpa [hφ] using hw', fun i => (w i).property⟩

variable [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem acl_meets_definable_tuple (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (V S : Set M) (hV : ∀ a ∈ V, iVF a)
    (hS : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    {n : ℕ} (A : Set (Fin n → M)) (hA : S.Definable LRV A) (hne : A.Nonempty) :
    ∃ a ∈ A, ∀ i, RawClosure.AlgebraicOver V (a i) := by
  let C : LRV.ElementarySubstructure M :=
    ⟨algebraicClosureSubstructure hc V,
      canonical_algebraicClosureSubstructure_elementary v hv hc h00 V hV hnt⟩
  obtain ⟨a,ha,halg⟩ := elementary_meets_definable_tuple C A hne (hA.mono hS)
  refine ⟨a,ha,fun i => ?_⟩
  obtain ⟨σ,hσ⟩ := halg i
  exact hσ.raw_finite_witness

include hv in
private theorem nontrivial_acl_mono {V W : Set M} (hVW : V ⊆ W)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1) :
    ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ v x.val ≠ 1 := by
  obtain ⟨x,hx0,hxv⟩ := hnt
  have hxW : x.val ∈ vfAlgebraicClosureField W :=
    (mem_vfAlgebraicClosureField W x.val).mpr
      (((mem_vfAlgebraicClosureField V x.val).mp x.property).mono hVW)
  refine ⟨⟨x.val,hxW⟩, ?_, hxv⟩
  intro he
  have heval : x.val = 0 := congrArg (fun y : vfAlgebraicClosureField W => y.val) he
  exact hx0 (Subtype.ext heval)

private theorem tuple_fibre_definable (S : Set M) {n m : ℕ}
    (P : Set ((Fin n → M) × (Fin m → M))) (hP : FiniteChoice.RelationDefinable S P)
    (a : Fin n → M) :
    (S ∪ Set.range a).Definable LRV {b : Fin m → M | (a,b) ∈ P} := by
  let E := S ∪ Set.range a
  have hf : E.DefinableMap LRV (fun b : Fin m → M => Sum.elim a b) := by
    intro i
    cases i with
    | inl j => exact LRV.definableFun_const (Fin m) (Or.inr (Set.mem_range_self j))
    | inr j => exact Set.DefinableFun.proj LRV
  exact (hP.mono Set.subset_union_left).preimage_map hf

include hv in
/-- The base has a pure-VF algebraic core; no extra representative names
are retained in the resulting finite-valued graph. -/
theorem definable_finite_choice_vf_core (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hs : Saturated M κ)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) {n m : ℕ}
    (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (hAvf : ∀ a ∈ A, ∀ i, iVF (a i))
    (P : Set ((Fin n → M) × (Fin m → M))) (hP : FiniteChoice.RelationDefinable S P)
    (hne : ∀ a ∈ A, ∃ b, (a,b) ∈ P) :
    ∃ F : (Fin n → M) → Set (Fin m → M),
      FiniteChoice.RelationDefinable S {p | p.2 ∈ F p.1} ∧
      (∀ a, (F a).Finite) ∧ (∀ a b, b ∈ F a → (a,b) ∈ P) ∧
      ∀ a, (F a).Nonempty ↔ a ∈ A := by
  apply FiniteChoice.definable_finite_choice hs S hsmall A hA P hP
  intro a ha
  let W := V ∪ Set.range a
  have hW : ∀ x ∈ W, iVF x := by
    rintro x (hx | ⟨i,rfl⟩)
    · exact hV x hx
    · exact hAvf a ha i
  have hS' : S ∪ Set.range a ⊆ algebraicClosureSet W := by
    rintro x (hx | hx)
    · exact algebraicClosureSet_mono Set.subset_union_left (hSV hx)
    · exact subset_algebraicClosureSet W (Or.inr hx)
  obtain ⟨b,hb,halg⟩ := acl_meets_definable_tuple v hv hc h00 W (S ∪ Set.range a) hW hS'
    (nontrivial_acl_mono v hv Set.subset_union_left hnt)
    {b | (a,b) ∈ P} (tuple_fibre_definable S P hP a) (hne a ha)
  refine ⟨b,hb,fun i => ?_⟩
  obtain ⟨U,hU,hUf,hbU⟩ := halg i
  exact ⟨U,hU.mono (Set.union_subset_union hVS (Set.Subset.refl _)),hUf,hbU⟩

include hv in
/-- Naming a finite VF tuple preserves the algebraic-core construction.
The resulting graph uses exactly the old base and the named tuple. -/
theorem definable_finite_choice_vf_parameters
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    {q : ℕ} (p : Fin q → VF M)
    (hsmall : Cardinal.mk ↥(S ∪ Set.range (SpecialTransformations.Section4.vfValues p)) < κ)
    {n m : ℕ} (A : Set (Fin n → M))
    (hA : (S ∪ Set.range (SpecialTransformations.Section4.vfValues p)).Definable LRV A)
    (hAvf : ∀ a ∈ A, ∀ i, iVF (a i))
    (P : Set ((Fin n → M) × (Fin m → M)))
    (hP : FiniteChoice.RelationDefinable
      (S ∪ Set.range (SpecialTransformations.Section4.vfValues p)) P)
    (hne : ∀ a ∈ A, ∃ b, (a,b) ∈ P) :
    ∃ F : (Fin n → M) → Set (Fin m → M),
      FiniteChoice.RelationDefinable
        (S ∪ Set.range (SpecialTransformations.Section4.vfValues p)) {z | z.2 ∈ F z.1} ∧
      (∀ a, (F a).Finite) ∧ (∀ a b, b ∈ F a → (a,b) ∈ P) ∧
      ∀ a, (F a).Nonempty ↔ a ∈ A := by
  let W := V ∪ Set.range (SpecialTransformations.Section4.vfValues p)
  have hW : ∀ x ∈ W, iVF x := by
    rintro x (hx | ⟨i,rfl⟩)
    · exact hV x hx
    · exact (p i).property
  have hSW : S ∪ Set.range (SpecialTransformations.Section4.vfValues p) ⊆ algebraicClosureSet W := by
    rintro x (hx | hx)
    · exact algebraicClosureSet_mono Set.subset_union_left (hSV hx)
    · exact subset_algebraicClosureSet W (Or.inr hx)
  exact definable_finite_choice_vf_core v hv hc h00 hs W _ hW
    (Set.union_subset_union hVS (Set.Subset.refl _)) hSW
    (nontrivial_acl_mono v hv Set.subset_union_left hnt) hsmall A hA hAvf P hP hne

include hv in
/-- The VF-generation hypothesis supplies the algebraic core, rather than
leaving modelhood or pointwise algebraic choice as an additional premise. -/
theorem definable_finite_choice_vf_generated
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ v x.val ≠ 1)
    (hsmall : Cardinal.mk (S : Set M) < κ) {n m : ℕ}
    (A : Set (Fin n → M)) (hA : (S : Set M).Definable LRV A)
    (hAvf : ∀ a ∈ A, ∀ i, iVF (a i))
    (P : Set ((Fin n → M) × (Fin m → M))) (hP : FiniteChoice.RelationDefinable (S : Set M) P)
    (hne : ∀ a ∈ A, ∃ b, (a,b) ∈ P) :
    ∃ F : (Fin n → M) → Set (Fin m → M),
      FiniteChoice.RelationDefinable (S : Set M) {p | p.2 ∈ F p.1} ∧
      (∀ a, (F a).Finite) ∧ (∀ a b, b ∈ F a → (a,b) ∈ P) ∧
      ∀ a, (F a).Nonempty ↔ a ∈ A := by
  have hV : ∀ x ∈ vfFieldNames B.field, iVF x := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hSV : (S : Set M) ⊆ algebraicClosureSet (vfFieldNames B.field) := by
    intro x hx
    obtain ⟨σ,hσ⟩ := B.definable_over_fieldNames x hx
    exact ⟨σ,hσ.algebraic⟩
  have hnt' : ∃ x : vfAlgebraicClosureField (vfFieldNames B.field), x ≠ 0 ∧ v x.val ≠ 1 := by
    obtain ⟨x,hx0,hxv⟩ := hnt
    have hname : x.val.val ∈ vfFieldNames B.field := ⟨x.val,x.property,rfl⟩
    have hx : x.val ∈ vfAlgebraicClosureField (vfFieldNames B.field) :=
      (mem_vfAlgebraicClosureField _ x.val).mpr
        (definableClosureAt_of_mem (σ := .vf) hname x.val.property).algebraic
    refine ⟨⟨x.val,hx⟩, ?_, hxv⟩
    intro he
    have heval : x.val = 0 := congrArg
      (fun y : vfAlgebraicClosureField (vfFieldNames B.field) => y.val) he
    exact hx0 (Subtype.ext heval)
  exact definable_finite_choice_vf_core v hv hc h00 hs (vfFieldNames B.field) (S : Set M)
    hV B.fieldNames_subset hSV hnt' hsmall A hA hAvf P hP hne

end DiamondIntegral.Section2
