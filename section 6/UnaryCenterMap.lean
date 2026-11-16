import «section 6».UnaryRVRelation

/-! Actual unary center maps retain the prescribed output RV label.
Their full graph is defined over the original real base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def unaryCenterPoint (f : (Fin 2 → M) → VF M) (p : Mixed M 1 1) : Mixed M 1 1 :=
  ((fun _ => f (Fin.snoc (vfValues p.1) (p.2 0).val)),p.2)

def unaryCenterCodes (f : (Fin 2 → M) → VF M) (z : Fin 1 ⊕ Fin 1 → M) : Fin 1 ⊕ Fin 1 → M :=
  Sum.elim (fun _ => (f ![z (.inl 0),z (.inr 0)]).val) (z ∘ Sum.inr)

theorem unaryCenterPoint_values (f : (Fin 2 → M) → VF M) (p : Mixed M 1 1) :
    mixedValues (unaryCenterPoint f p) = unaryCenterCodes f (mixedValues p) := by
  funext i
  cases i with
  | inl i =>
    fin_cases i
    change (f (Fin.snoc (vfValues p.1) (p.2 0).val)).val = (f ![(p.1 0).val,(p.2 0).val]).val
    congr 2
    funext j
    fin_cases j <;> rfl
  | inr i => rfl

def unaryCenterMap (f : (Fin 2 → M) → VF M) (hf : S.DefinableFun LRV (fun z => (f z).val))
    (A : DefSet (rawMixedSpace (M := M) 1 1) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) 1 1) S) := by
  let P := rawMixedSpace (M := M) 1 1
  let F := unaryCenterCodes f
  have hF : S.DefinableMap LRV F := by
    rintro (i | i)
    · fin_cases i
      have harg : S.DefinableMap LRV (fun z : Fin 1 ⊕ Fin 1 → M => ![z (.inl 0),z (.inr 0)]) := by
        intro j
        fin_cases j <;> exact Set.DefinableFun.proj LRV
      exact hf.comp harg
    · exact Set.DefinableFun.proj LRV
  have hcode (z : P.domain) : mixedValues (unaryCenterPoint f (P.decode z)) = F z.val :=
    (unaryCenterPoint_values f (P.decode z)).trans (congrArg F (mixedValues_decode z))
  have hdom (z : P.domain) : F z.val ∈ P.domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  exact Map.ofCodes A (unaryCenterPoint f) F hF hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨F z.val,hdom z⟩).trans (hcode z).symm))

theorem unaryCenterMap_apply (f : (Fin 2 → M) → VF M)
    (hf : S.DefinableFun LRV (fun z => (f z).val))
    (A : DefSet (rawMixedSpace (M := M) 1 1) S) (p : A) :
    (unaryCenterMap f hf A p).val = unaryCenterPoint f p.val := rfl

theorem unaryCenterMap_prescribed (f : (Fin 2 → M) → VF M)
    (hf : S.DefinableFun LRV (fun z => (f z).val)) (R : M → M → Prop)
    (hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))})
    (hval : ∀ a : Fin 1 → VF M, ∀ v, R (iRv (a 0).val) v →
      iRv (f (Fin.snoc (vfValues a) v)).val = v)
    (p : unaryRVRelationDomain R hR) :
    rv M ((unaryCenterMap f hf (unaryRVRelationDomain R hR) p).val.1 0) = p.val.2 0 :=
  Subtype.ext (hval p.val.1 (p.val.2 0).val p.property)

end DiamondIntegral.Section6
