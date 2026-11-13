import Section3.RawBarycentricCode
import Section3.TupleRelations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.Barycentre
open SpecialTransformations.Section3.RawClosure.Tuple
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}

/-- The finite VF row is used when its size is bounded by N; all other
rows are replaced by the empty set. This is a definable truncation. -/
def boundedVFFibre (R : Set ((Fin m → M) × M))
    (hVF : ∀ t x, (t,x) ∈ R → iVF x) (N : ℕ) (t : Fin m → M) : Finset (VFType (M := M)) :=
  if h : {x | (t,x) ∈ R}.Finite ∧ {x | (t,x) ∈ R}.ncard ≤ N then
    h.1.toFinset.attach.map
      { toFun := fun x => ⟨x.val,hVF t x.val (h.1.mem_toFinset.mp x.property)⟩
        inj' := by intro x y h; exact Subtype.ext (congrArg (fun v : VFType (M := M) => v.val) h) }
  else ∅

omit [M ⊨ Axioms.ACVF] in
theorem boundedVFFibre_card_le (R : Set ((Fin m → M) × M))
    (hVF : ∀ t x, (t,x) ∈ R → iVF x) (N : ℕ) (t : Fin m → M) :
    (boundedVFFibre R hVF N t).card ≤ N := by
  unfold boundedVFFibre
  split_ifs with h
  · rw [Finset.card_map,Finset.card_attach]
    exact (Set.ncard_eq_toFinset_card _ h.1) ▸ h.2
  · exact Nat.zero_le N

omit [M ⊨ Axioms.ACVF] in
theorem boundedVFFibre_mem (R : Set ((Fin m → M) × M))
    (hVF : ∀ t x, (t,x) ∈ R → iVF x) (N : ℕ) (t : Fin m → M) (x : VFType (M := M)) :
    x ∈ boundedVFFibre R hVF N t ↔
      (t,x.val) ∈ R ∧ t ∉ RawClosure.Tuple.HasMore R N := by
  have hc : t ∉ RawClosure.Tuple.HasMore R N ↔
      {x | (t,x) ∈ R}.Finite ∧ {x | (t,x) ∈ R}.ncard ≤ N :=
    by
      change (¬ ∃ u : Fin (N+1) → M, Function.Injective u ∧ ∀ i, (t,u i) ∈ R) ↔ _
      exact RawClosure.no_inj_iff_finite_ncard_le (s := {x | (t,x) ∈ R}) (k := N)
  unfold boundedVFFibre
  split_ifs with h
  · rw [Finset.mem_map]
    constructor
    · rintro ⟨y,_,hy⟩
      exact ⟨(congrArg (fun v : VFType (M := M) => (t,v.val)) hy) ▸ h.1.mem_toFinset.mp y.property,hc.mpr h⟩
    · rintro ⟨hx,_⟩
      exact ⟨⟨x.val,h.1.mem_toFinset.mpr hx⟩,Finset.mem_attach _ _,Subtype.ext rfl⟩
  · simp only [Finset.notMem_empty,false_iff,not_and]
    intro _ hh
    exact h (hc.mp hh)

omit [M ⊨ Axioms.ACVF] in
/-- The entire graph of the truncated finite family is definable over
the same real base, including at parameter values with infinite rows. -/
theorem boundedVFFibre_definable (S : Set M)
    (R : Set ((Fin m → M) × M)) (hR : RelationDefinable S R)
    (hVF : ∀ t x, (t,x) ∈ R → iVF x) (N : ℕ) :
    RelationDefinable S (finiteFibreRelation (boundedVFFibre R hVF N)) := by
  have hcount := (RawClosure.Tuple.hasMore_definable S R hR N).compl
  have hd := hR.inter (hcount.preimage_comp (Sum.inl : Fin m → Fin m ⊕ Fin 1))
  change S.Definable LRV {w : Fin m ⊕ Fin 1 → M | ∃ x ∈ boundedVFFibre R hVF N (w ∘ Sum.inl), x.val = w (.inr 0)}
  convert hd using 1
  ext w
  symm
  change ((w ∘ Sum.inl,w (.inr 0)) ∈ R ∧ w ∘ Sum.inl ∉ RawClosure.Tuple.HasMore R N) ↔
    ∃ x ∈ boundedVFFibre R hVF N (w ∘ Sum.inl), x.val = w (.inr 0)
  constructor
  · intro hw
    exact ⟨⟨w (.inr 0),hVF _ _ hw.1⟩,(boundedVFFibre_mem R hVF N _ _).mpr hw,rfl⟩
  · rintro ⟨x,hx,he⟩
    have h := (boundedVFFibre_mem R hVF N _ x).mp hx
    exact ⟨he ▸ h.1,h.2⟩

/-- Canonical barycentric codes of uniformly bounded finite VF rows
are definable functions, with no row elements named as parameters. -/
theorem boundedVFFibre_code_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (R : Set ((Fin m → M) × M)) (hR : RelationDefinable S R)
    (hVF : ∀ t x, (t,x) ∈ R → iVF x) (N : ℕ) (j : Fin N) :
    S.DefinableFun LRV (fun w : Fin m ⊕ Fin 1 → M =>
      rawCode N (boundedVFFibre R hVF N) (w ∘ Sum.inl) (w (.inr 0)) j) :=
  rawCode_definable h00 S N (boundedVFFibre R hVF N)
    (boundedVFFibre_definable S R hR hVF N) N (boundedVFFibre_card_le R hVF N) j

/-- The canonical code is injective on every row retained by the bound. -/
theorem boundedVFFibre_code_injective (h00 : M ⊨ Axioms.ACVF00)
    (R : Set ((Fin m → M) × M)) (hVF : ∀ t x, (t,x) ∈ R → iVF x)
    (N : ℕ) (t : Fin m → M) :
    Set.InjOn (fun x : VFType (M := M) => rawCode N (boundedVFFibre R hVF N) t x.val)
      {x | x ∈ boundedVFFibre R hVF N t} := by
  intro x hx y hy he
  apply code_injective_of_card_le h00 N (boundedVFFibre R hVF N t)
    ((boundedVFFibre_card_le R hVF N t).trans (Nat.le_succ N)) hx hy
  funext j
  have h := congrFun he j
  simpa only [rawCode_eq_code] using h
end DiamondIntegral.Section3
