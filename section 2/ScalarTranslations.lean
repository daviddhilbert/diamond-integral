import «section 2».ScalarExtensions
import Section3.GammaBaseTools

/-! Translating the output of a definable unary VF germ by a named point
keeps its complete graph over the same real parameter set. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem unaryScalarGraph_sub_definable (S : Set M) (f : VF M → VF M)
    (hf : S.Definable LRV (unaryScalarGraph f)) (b : VF M) (hb : b.val ∈ S) :
    S.Definable LRV (unaryScalarGraph (fun x => f x-b)) := by
  have hcb : S.DefinableFun LRV (fun _ : Fin 2 → M => b.val) :=
    SpecialTransformations.DefinableConstants.constant (Set.Definable.singleton_of_mem LRV hb)
  have hadd : S.DefinableFun LRV (fun z : Fin 2 → M => iVFAdd (z 1) b.val) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
      (show S.DefinableMap LRV (fun z : Fin 2 → M => ![z 1,b.val]) from by
        intro j
        fin_cases j
        · exact Set.DefinableFun.proj LRV
        · exact hcb)
  let W (z : Fin 2 → M) : Fin 2 → M := ![z 0,iVFAdd (z 1) b.val]
  have hW : S.DefinableMap LRV W := by
    intro j
    fin_cases j
    · exact Set.DefinableFun.proj LRV
    · exact hadd
  have hs := (GammaParameters.sortedUniverse_definable S (fun _ : Fin 2 => .vf)).raw_definable
  convert hs.inter (hf.preimage_map hW) using 1
  ext z
  change (∃ x : VF M, x.val = z 0 ∧ (f x-b).val = z 1) ↔
    ((∀ j : Fin 2, iVF (z j)) ∧ ∃ x : VF M, x.val = z 0 ∧ (f x).val = iVFAdd (z 1) b.val)
  constructor
  · rintro ⟨x,hx0,hx1⟩
    refine ⟨?_,x,hx0,?_⟩
    · intro j
      fin_cases j
      · exact hx0 ▸ x.property
      · exact hx1 ▸ (f x-b).property
    · rw [← hx1]
      exact congrArg Subtype.val (sub_add_cancel (f x) b).symm
  · rintro ⟨hz,x,hx0,hxf⟩
    let y : VF M := ⟨z 1,hz 1⟩
    have he : f x = y+b := Subtype.ext hxf
    have hsub : f x-b = y := sub_eq_iff_eq_add.mpr he
    exact ⟨x,hx0,congrArg (fun w : VF M => w.val) hsub⟩

theorem unaryScalarGraph_input_shift_definable (S : Set M) (f : VF M → VF M)
    (hf : S.Definable LRV (unaryScalarGraph f)) (a : VF M) (ha : a.val ∈ S) :
    S.Definable LRV (unaryScalarGraph (fun x => f (a+x))) := by
  have hca : S.DefinableFun LRV (fun _ : Fin 2 → M => a.val) :=
    SpecialTransformations.DefinableConstants.constant (Set.Definable.singleton_of_mem LRV ha)
  have hadd : S.DefinableFun LRV (fun z : Fin 2 → M => iVFAdd a.val (z 0)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
      (show S.DefinableMap LRV (fun z : Fin 2 → M => ![a.val,z 0]) from by
        intro j
        fin_cases j
        · exact hca
        · exact Set.DefinableFun.proj LRV)
  let W (z : Fin 2 → M) : Fin 2 → M := ![iVFAdd a.val (z 0),z 1]
  have hW : S.DefinableMap LRV W := by
    intro j
    fin_cases j
    · exact hadd
    · exact Set.DefinableFun.proj LRV
  have hs := (GammaParameters.sortedUniverse_definable S (fun _ : Fin 2 => .vf)).raw_definable
  convert hs.inter (hf.preimage_map hW) using 1
  ext z
  change (∃ x : VF M, x.val = z 0 ∧ (f (a+x)).val = z 1) ↔
    ((∀ j : Fin 2, iVF (z j)) ∧ ∃ y : VF M, y.val = iVFAdd a.val (z 0) ∧ (f y).val = z 1)
  constructor
  · rintro ⟨x,hx0,hx1⟩
    refine ⟨?_,a+x,?_,hx1⟩
    · intro j
      fin_cases j
      · exact hx0 ▸ x.property
      · exact hx1 ▸ (f (a+x)).property
    · rw [← hx0]
      rfl
  · rintro ⟨hz,y,hy,hfy⟩
    let x : VF M := ⟨z 0,hz 0⟩
    have he : y = a+x := Subtype.ext hy
    exact ⟨x,rfl,he ▸ hfy⟩

end DiamondIntegral.Section2
