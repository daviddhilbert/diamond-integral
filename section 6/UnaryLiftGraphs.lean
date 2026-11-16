import «section 6».UnaryFinitaryLifting

/-! The finitary lift has its complete VF correspondence graph over S.
Projecting the retained RV label neither introduces parameters nor
loses the unique output in each prescribed target RV disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryFinitaryLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {R : M → M → Prop}
variable {hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))}}

theorem fibre_graph_definable (T : UnaryFinitaryLift R hR) :
    S.Definable LRV (vfCorrespondenceGraph Set.univ
      (fun a : Fin 1 → VF M => {b : Fin 1 → VF M | b 0 ∈ T.fibre (a 0)})) := by
  let J := Fin 1 ⊕ Fin 1
  let K := J ⊕ Fin 1
  let args (z : K → M) : Fin 2 → M := ![z (.inl (.inl 0)),z (.inr 0)]
  have hargs : S.DefinableMap LRV args := by
    intro j
    fin_cases j <;> exact Set.DefinableFun.proj LRV
  have hcenter := T.definable.comp hargs
  have heq := hcenter.ofPred_eq
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl (.inr 0) : K)))
  let relargs (z : K → M) : Fin 1 ⊕ Fin 1 → M :=
    Sum.elim (fun _ => iRv (z (.inl (.inl 0)))) (fun _ => z (.inr 0))
  have hRelArgs : S.DefinableMap LRV relargs := by
    rintro (i | i)
    · exact rv_scalarCode_definable (Set.DefinableFun.proj LRV)
    · exact Set.DefinableFun.proj LRV
  have hRel := hR.preimage_map hRelArgs
  have hVF := (vfRawUniverse_definable S 1).preimage_comp
    (fun _ : Fin 1 => (.inl (.inl (0 : Fin 1)) : K))
  have h := (hVF.inter (hRel.inter heq)).exists_of_finite
  convert h using 1
  ext z
  change (∃ a ∈ (Set.univ : Set (Fin 1 → VF M)),
    ∃ b ∈ {b : Fin 1 → VF M | b 0 ∈ T.fibre (a 0)}, Sum.elim (vfValues a) (vfValues b) = z) ↔
    ∃ q : Fin 1 → M, (∀ i : Fin 1, iVF (z (.inl 0))) ∧
      R (iRv (z (.inl 0))) (q 0) ∧ (T.center ![z (.inl 0),q 0]).val = z (.inr 0)
  constructor
  · rintro ⟨a,_,b,⟨v,hv,hb⟩,he⟩
    have ha : (a 0).val = z (.inl 0) := congrFun he (.inl 0)
    have hbval : (b 0).val = z (.inr 0) := congrFun he (.inr 0)
    refine ⟨(fun _ => v),(fun _ => by rw [← ha]; exact (a 0).property),?_,?_⟩
    · rwa [← ha]
    · rw [← ha]
      exact (congrArg Subtype.val hb).trans hbval
  · rintro ⟨q,hVF,hRel,hval⟩
    let a : Fin 1 → VF M := fun _ => ⟨z (.inl 0),hVF 0⟩
    let b : Fin 1 → VF M := fun _ => T.center ![z (.inl 0),q 0]
    refine ⟨a,Set.mem_univ _,b,⟨q 0,hRel,rfl⟩,?_⟩
    funext j
    cases j with
    | inl j => fin_cases j; rfl
    | inr j => fin_cases j; exact hval

end DiamondIntegral.Section6.UnaryFinitaryLift
