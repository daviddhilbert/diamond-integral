import «section 2».UnaryValueGerms
import Section3.DefinableConstants

/-! Total definable extensions of a unary partial VF map, and replacement
of one value by its limit. These constructions only use named real data. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open scoped Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def scalarPartialGraph (A : Set (VF M)) (f : VF M → VF M) : Set (Fin 2 → M) :=
  {z | ∃ x ∈ A, x.val = z 0 ∧ (f x).val = z 1}

noncomputable def scalarZeroExtension (A : Set (VF M)) (f : VF M → VF M) (x : VF M) : VF M :=
  if x ∈ A then f x else 0

theorem scalarZeroExtension_on {A : Set (VF M)} {f : VF M → VF M} {x : VF M} (hx : x ∈ A) :
    scalarZeroExtension A f x = f x := ite_eq_left hx

theorem scalarZeroExtension_definable (S : Set M) (A : Set (VF M))
    (hA : S.Definable₁ LRV (Subtype.val '' A)) (f : VF M → VF M)
    (hf : S.Definable LRV (scalarPartialGraph A f)) :
    S.Definable LRV (unaryScalarGraph (scalarZeroExtension A f)) := by
  have hs := ((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
  have hDom := hA.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
  have hzero : S.DefinableFun LRV (fun _ : Fin 2 → M => (0 : VF M).val) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hz := (Set.DefinableFun.proj LRV (i := (1 : Fin 2))).ofPred_eq hzero
  convert hf.union ((hs.inter hDom.compl).inter hz) using 1
  ext z
  change (∃ x : VF M, x.val = z 0 ∧ (scalarZeroExtension A f x).val = z 1) ↔
    (∃ x ∈ A, x.val = z 0 ∧ (f x).val = z 1) ∨
      ((iVF (z 0) ∧ z 0 ∉ Subtype.val '' A) ∧ z 1 = (0 : VF M).val)
  constructor
  · rintro ⟨x,hx0,hx1⟩
    by_cases hx : x ∈ A
    · exact Or.inl ⟨x,hx,hx0,by simpa only [scalarZeroExtension,ite_eq_left hx] using hx1⟩
    · refine Or.inr ⟨⟨hx0 ▸ x.property,?_⟩,?_⟩
      · rintro ⟨y,hy,he⟩
        exact hx ((Subtype.ext (he.trans hx0.symm) : y = x) ▸ hy)
      · simpa only [scalarZeroExtension,ite_eq_right hx] using hx1.symm
  · rintro (⟨x,hx,hx0,hx1⟩ | ⟨⟨hVF,hnot⟩,hz1⟩)
    · exact ⟨x,hx0,by simpa only [scalarZeroExtension,ite_eq_left hx] using hx1⟩
    · let x : VF M := ⟨z 0,hVF⟩
      have hx : x ∉ A := fun h => hnot ⟨x,h,rfl⟩
      exact ⟨x,rfl,by simpa only [scalarZeroExtension,ite_eq_right hx] using hz1.symm⟩

theorem unaryScalarGraph_update_definable (S : Set M) (f : VF M → VF M)
    (hf : S.Definable LRV (unaryScalarGraph f)) (a b : VF M) (ha : a.val ∈ S) (hb : b.val ∈ S) :
    S.Definable LRV (unaryScalarGraph (Function.update f a b)) := by
  have hca : S.DefinableFun LRV (fun _ : Fin 2 → M => a.val) :=
    SpecialTransformations.DefinableConstants.constant (Set.Definable.singleton_of_mem LRV ha)
  have hcb : S.DefinableFun LRV (fun _ : Fin 2 → M => b.val) :=
    SpecialTransformations.DefinableConstants.constant (Set.Definable.singleton_of_mem LRV hb)
  have hx := (Set.DefinableFun.proj LRV (i := (0 : Fin 2))).ofPred_eq hca
  have hy := (Set.DefinableFun.proj LRV (i := (1 : Fin 2))).ofPred_eq hcb
  convert (hf.sdiff hx).union (hx.inter hy) using 1
  ext z
  change (∃ x : VF M, x.val = z 0 ∧ (Function.update f a b x).val = z 1) ↔
    ((∃ x : VF M, x.val = z 0 ∧ (f x).val = z 1) ∧ z 0 ≠ a.val) ∨
      (z 0 = a.val ∧ z 1 = b.val)
  constructor
  · rintro ⟨x,hx0,hx1⟩
    by_cases he : x = a
    · subst x
      exact Or.inr ⟨hx0.symm,by simpa only [Function.update_self] using hx1.symm⟩
    · exact Or.inl ⟨⟨x,hx0,by simpa only [Function.update_of_ne he] using hx1⟩,
        fun hz => he (Subtype.ext (hx0.trans hz))⟩
  · rintro (⟨⟨x,hx0,hx1⟩,hz⟩ | ⟨hx0,hx1⟩)
    · have he : x ≠ a := fun h => hz (hx0.symm.trans (congrArg Subtype.val h))
      exact ⟨x,hx0,by simpa only [Function.update_of_ne he] using hx1⟩
    · exact ⟨a,hx0.symm,by simpa only [Function.update_self] using hx1.symm⟩

end DiamondIntegral.Section2
