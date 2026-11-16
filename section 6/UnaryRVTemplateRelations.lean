import «section 6».RVSetParameterTemplates
import «section 6».FrozenUnaryRVDataPreparation

/-! Complete unary membership relations for an arbitrary parameterized
RV family. Their output is allowed to be unbounded. The carried old
labels do not change the complete parameter row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r q : ℕ}

def unaryRVTemplateRelationIndex : Fin 1 ⊕ Fin q → Fin 1 ⊕ Fin (r+q) :=
  Sum.elim (fun _ => .inl 0) (fun i => .inr (Fin.natAdd r i))

def unaryRVTemplateRelation (V : RVSetParameterTemplate (M := M) S 1 q) (r : ℕ) :
    DefSet (rawMixedSpace (M := M) 1 (r+q)) S := by
  let P := rawMixedSpace (M := M) 1 (r+q)
  refine ⟨{x | mixedValues x ∘ unaryRVTemplateRelationIndex ∈ V.graph},?_⟩
  change S.Definable LRV (P.preimage _)
  convert (P.definable_domain S).inter (V.definable.preimage_comp unaryRVTemplateRelationIndex) using 1
  ext z
  constructor
  · rintro ⟨hz,hzV⟩
    change mixedValues (P.decode ⟨z,hz⟩) ∘ unaryRVTemplateRelationIndex ∈ V.graph at hzV
    rw [mixedValues_decode] at hzV
    exact ⟨hz,hzV⟩
  · rintro ⟨hz,hzV⟩
    refine ⟨hz,?_⟩
    change mixedValues (P.decode ⟨z,hz⟩) ∘ unaryRVTemplateRelationIndex ∈ V.graph
    rw [mixedValues_decode]
    exact hzV

theorem unaryRVTemplateRelation_row (V : RVSetParameterTemplate (M := M) S 1 q) (p : Mixed M 1 r) :
    unaryRVDataRow (unaryRVTemplateRelation V r) p=(V.fibre (fun _ => (p.1 0).val)).carrier := by
  ext u
  change mixedValues (p.1,Fin.append p.2 u) ∘ unaryRVTemplateRelationIndex ∈ V.graph ↔ _
  have he : mixedValues (p.1,Fin.append p.2 u) ∘ unaryRVTemplateRelationIndex=
      Sum.elim (fun _ : Fin 1 => (p.1 0).val) (rvValues u) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp only [unaryRVTemplateRelationIndex,Function.comp_apply,mixedValues,Sum.elim_inr,rvValues,Fin.append_right]
  rw [he]
  rfl

theorem frozenUnaryRVTemplateRelation_row
    (V : RVSetParameterTemplate (M := M) S 1 q)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (p : Mixed M 1 r) :
    FMT.frozenUnaryValue balls centers (unaryRVDataRow (unaryRVTemplateRelation V r)) p=
      (V.fibre (fun _ => (FMT.vfFamilyFreeze balls centers (p.1 0)).val)).carrier := by
  unfold FMT.frozenUnaryValue
  rw [unaryRVTemplateRelation_row]

end DiamondIntegral.Section6
