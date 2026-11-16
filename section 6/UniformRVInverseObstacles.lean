import «section 6».UniformAlgebraicExceptions
import «section 2».FiniteFibres

/-! Original-base uniform finite exceptional sets for unary RV inverse
fibres, with arbitrary finite real parameter tuples. The scalar exchange
and finite-exception theorem is specialized only at the actual enlarged
small base; compactness then removes those temporary names uniformly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def unaryRVReverseFamily (A : Set ((Fin (n+1) → M) × M)) : Set ((Fin (n+1) → M) × M) :=
  {p | (Fin.snoc (Fin.init p.1) p.2,p.1 (Fin.last n)) ∈ A}

theorem unaryRVReverseFamily_definable
    (A : Set ((Fin (n+1) → M) × M)) (hA : RawClosure.Tuple.RelationDefinable S A) :
    RawClosure.Tuple.RelationDefinable S (unaryRVReverseFamily A) := by
  let F (z : Fin (n+1) ⊕ Fin 1 → M) : Fin (n+1) ⊕ Fin 1 → M :=
    Sum.elim (Fin.snoc (Fin.init (z ∘ Sum.inl)) (z (.inr 0))) (fun _ => z (.inl (Fin.last n)))
  have hF : S.DefinableMap LRV F := by
    rintro (j | j)
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [F,Sum.elim_inl,Fin.snoc_last] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inr (0 : Fin 1) : Fin (n+1) ⊕ Fin 1)))
      · simpa only [F,Sum.elim_inl,Fin.snoc_castSucc,Fin.init,Function.comp_apply] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl k.castSucc : Fin (n+1) ⊕ Fin 1)))
    · exact Set.DefinableFun.proj LRV
  exact hA.preimage_map hF

theorem rvFamily_scalar_slice_definable
    (A : Set ((Fin (n+1) → M) × M)) (hA : RawClosure.Tuple.RelationDefinable S A) (t : Fin n → M) :
    (S ∪ Set.range t).Definable₂ LRV {p : M × M | (Fin.snoc t p.1,p.2) ∈ A} := by
  let T := S ∪ Set.range t
  let F (z : Fin 2 → M) : Fin (n+1) ⊕ Fin 1 → M :=
    Sum.elim (Fin.snoc t (z 0)) (fun _ => z 1)
  have hF : T.DefinableMap LRV F := by
    rintro (j | j)
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [F,Sum.elim_inl,Fin.snoc_last] using
          (Set.DefinableFun.proj (L := LRV) (A := T) (i := (0 : Fin 2)))
      · simpa only [F,Sum.elim_inl,Fin.snoc_castSucc] using
          (LRV.definableFun_const (Fin 2) (show t k ∈ T from Or.inr (Set.mem_range_self k)))
    · exact Set.DefinableFun.proj LRV
  exact (hA.mono Set.subset_union_left).preimage_map hF

theorem exists_uniform_rv_inverse_obstacles
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : Set ((Fin (n+1) → M) × M)) (hA : RawClosure.Tuple.RelationDefinable S A)
    (hSort : ∀ (t : Fin n → M) (x y : M), (Fin.snoc t x,y) ∈ A → iRV x ∧ iRV y)
    (hFinite : ∀ (t : Fin n → M) (x : M), {y | (Fin.snoc t x,y) ∈ A}.Finite) :
    ∃ E : RawClosure.Tuple.GoodRelation (n := n) S, ∃ N : ℕ,
      ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
        {x | (Fin.snoc t x,y) ∈ A}.Finite ∧ {x | (Fin.snoc t x,y) ∈ A}.ncard ≤ N := by
  have hEither (p : Fin (n+1) → M) :
      {x | (p,x) ∈ unaryRVReverseFamily A}.Finite ∨
        RawClosure.AlgebraicOver (S ∪ Set.range (Fin.init p)) (p (Fin.last n)) := by
    by_cases hf : {x | (p,x) ∈ unaryRVReverseFamily A}.Finite
    · exact Or.inl hf
    · right
      let t := Fin.init p
      let y := p (Fin.last n)
      let T := S ∪ Set.range t
      let R : Set (M × M) := {q | (Fin.snoc t q.1,q.2) ∈ A}
      have hR := rvFamily_scalar_slice_definable A hA t
      have hSmallT : Cardinal.mk T < κ := small_union_range hκ S hsmall t
      obtain ⟨x,hx⟩ := (Set.Infinite.nonempty hf)
      have hyRV : iRV y := (hSort t x y hx).2
      obtain ⟨E,hEF,hED,hEB,hInf⟩ := lemma_2_15_rv hc hκ hs h00 T hSmallT
        {b | iRV b} (definableAt_sort T .rv) R hR
        (fun a b h => hSort t a b h) (fun a => hFinite t a)
      have hyE : y ∈ E := (hInf y hyRV).mp hf
      exact ⟨E,hED.raw_definable,hEF,hyE⟩
  obtain ⟨E,N,hE⟩ := uniform_algebraic_exceptions hs hsmall (unaryRVReverseFamily A)
    (unaryRVReverseFamily_definable A hA) hEither
  refine ⟨E,N,fun t y hy => ?_⟩
  have h := hE (Fin.snoc t y) (by simpa only [Fin.init_snoc,Fin.snoc_last] using hy)
  simpa only [unaryRVReverseFamily,Fin.init_snoc,Fin.snoc_last,Set.mem_setOf_eq] using h

end DiamondIntegral.Section6
