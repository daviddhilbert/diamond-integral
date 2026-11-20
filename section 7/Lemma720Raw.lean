import «section 7».Lemma720Second
import IntegrationSection4.FamilyPositionRefinement
import Section4.CanonicalNormalization

/-! Lemma 7.20, step 4: the bridge from Section 6 maps on unary mixed sets to the
raw scalar families of the upstream Section 4 cell lemmas.

* `overBase_of_definable`, `definable_of_overBase`: over the full base `⟨S, ∅⟩`
  (no imaginary parameters), upstream `OverBase` is ordinary `S`-definability.
* For a definable set `B ⊆ VF × RVᵃ` and a definable map `ε : B → VF`, the raw
  family `rawDom B` (indexed by the raw label tuple) and the raw function
  `rawFun ε` have an upstream definable graph (`rawFun_graph`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}

/-- The full base with real part `S` and no imaginary parameters. -/
abbrev fullBase (S : Set M) : FullBaseAtomicity.Base (M := M) := ⟨S, ∅⟩

theorem overBase_of_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {ι : Type} [Finite ι] {X : Set (ι → M)} (h : S.Definable LRV X) :
    FullBaseAtomicity.OverBase (fullBase S) X := by
  apply FullBaseAtomicity.OverBase.of_real
  rw [canonical_normalize_eq hc]
  exact h

theorem definable_of_overBase (hc : CanonicalStructure.IsCanonical (M := M))
    {ι : Type} [Finite ι] {X : Set (ι → M)} (h : FullBaseAtomicity.OverBase (fullBase S) X) :
    S.Definable LRV X := by
  let p := @ParameterPresentation.presentation M sM hM
  have h' : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι X := by
    letI := CanonicalStructure.normalize (M := M)
    exact (ImaginaryParameters.OverBase.empty_iff_real (p := p) rfl).mp h
  rw [canonical_normalize_eq hc] at h'
  exact h'

section Raw
variable (B : DefSet (rawMixedSpace (M := M) 1 a) S)

/-- The raw codes of the graph of a map into `VF`. -/
def rawGraph (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    Set ((Fin 1 ⊕ Fin a) ⊕ Fin 1 → M) :=
  (rawMixedSpace (M := M) 1 a).relation (rawVFSpace (M := M) 1) f.graph

theorem rawGraph_definable (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    S.Definable LRV (rawGraph B f) := f.graph_definable

theorem mem_rawGraph_iff (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (z : (Fin 1 ⊕ Fin a) ⊕ Fin 1 → M) :
    z ∈ rawGraph B f ↔ ∃ q : B, Sum.elim (mixedValues q.val) (vfValues (f q).val) = z := by
  constructor
  · rintro ⟨hx, hy, q, hq, hfq⟩
    have he₁ : mixedValues q.val = z ∘ Sum.inl := by rw [hq]; exact mixedValues_decode _
    have he₂ : vfValues (f q).val = z ∘ Sum.inr := by rw [hfq]; exact vfValues_decode _
    exact ⟨q, by funext i; cases i with
      | inl i => exact congrFun he₁ i
      | inr i => exact congrFun he₂ i⟩
  · rintro ⟨q, rfl⟩
    refine ⟨mixedValues_mem_domain q.val, ⟨(f q).val, rfl⟩, q, ?_, ?_⟩
    · exact (decode_mixedValues q.val).symm
    · exact (decode_vfValues (f q).val).symm

/-- The raw domain over a raw label tuple `p`. -/
def rawDom (p : Fin a → M) : Set M :=
  {x | ∃ q : B, (q.val.1 0).val = x ∧ rvValues q.val.2 = p}

theorem rawDom_vf (p : Fin a → M) : rawDom B p ⊆ {x | iVF x} := by
  rintro x ⟨q, rfl, -⟩
  exact (q.val.1 0).property

theorem point_unique {p : Fin a → M} {x : M} {q q' : B}
    (hq : (q.val.1 0).val = x ∧ rvValues q.val.2 = p) (hq' : (q'.val.1 0).val = x ∧ rvValues q'.val.2 = p) :
    q = q' := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact Subtype.ext (hq.1.trans hq'.1.symm)
  · exact rvValues_injective (hq.2.trans hq'.2.symm)

/-- The raw function: the value of `f` at the unique point over `(p, x)`. -/
def rawFun (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : Fin a → M) (x : M) : M :=
  if h : ∃ q : B, (q.val.1 0).val = x ∧ rvValues q.val.2 = p then ((f h.choose).val 0).val else x

theorem rawFun_point (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (q : B) :
    rawFun B f (rvValues q.val.2) (q.val.1 0).val = ((f q).val 0).val := by
  have h : ∃ q' : B, (q'.val.1 0).val = (q.val.1 0).val ∧ rvValues q'.val.2 = rvValues q.val.2 :=
    ⟨q, rfl, rfl⟩
  rw [rawFun, dif_pos h, point_unique B h.choose_spec ⟨rfl, rfl⟩]

theorem rawFun_vf (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : Fin a → M) (x : M)
    (hx : x ∈ rawDom B p) : iVF (rawFun B f p x) := by
  obtain ⟨q, rfl, rfl⟩ := hx
  rw [rawFun_point]
  exact ((f q).val 0).property

/-- **The raw graph is upstream-definable over the full base.** -/
theorem rawFun_graph (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    IntegrationInACVF.Section4.FiniteScalarFamilies.Graph (fullBase S) (rawDom B) (rawFun B f) := by
  apply overBase_of_definable hc
  let ψ (z : (Fin a ⊕ Fin 1) ⊕ Fin 1 → M) : (Fin 1 ⊕ Fin a) ⊕ Fin 1 → M :=
    Sum.elim (Sum.elim (fun _ => z (.inl (.inr 0))) (fun i => z (.inl (.inl i)))) (fun _ => z (.inr 0))
  have hψ : S.DefinableMap LRV ψ := by
    rintro ((i | i) | i) <;> exact Set.DefinableFun.proj LRV
  convert (rawGraph_definable B f).preimage_map hψ using 1
  ext z
  rw [Set.mem_preimage, mem_rawGraph_iff]
  constructor
  · rintro ⟨⟨q, hqx, hqp⟩, hz⟩
    refine ⟨q, ?_⟩
    funext i
    rcases i with ((i | i) | i)
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact hqx
    · exact congrFun hqp i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change ((f q).val 0).val = z (.inr 0)
      rw [hz, ← hqx, ← hqp]
      exact (rawFun_point B f q).symm
  · rintro ⟨q, hq⟩
    have h1 : (q.val.1 0).val = z (.inl (.inr 0)) := congrFun hq (.inl (.inl 0))
    have h2 : rvValues q.val.2 = z ∘ Sum.inl ∘ Sum.inl := by
      funext i
      exact congrFun hq (.inl (.inr i))
    have h3 : ((f q).val 0).val = z (.inr 0) := congrFun hq (.inr 0)
    refine ⟨⟨q, h1, h2⟩, ?_⟩
    rw [← h1, ← h2, rawFun_point]
    exact h3.symm

end Raw

end DiamondIntegral.Section7.Lemma720
