import «section 5».OriginalPredicateSyntax
import IntegrationSection6.GammaRowBijectionPromotion
import «section 5».RESBijectionPromotion

/-! Arbitrary actual RV row bijections promote to complete original-base
graph schemata. No finite-value assumption is imposed on either domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem original_rv_bijection_schema_at_parameter
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (D : GammaDomainFormula B p a sp) (F : GammaDomainFormula B p b sp)
    (e : {x : Fin a → M // Fin.append z x ∈ D.val} ≃ {y : Fin b → M // Fin.append z y ∈ F.val})
    (hgraph : DefinableOverBase ⟨B.real ∪ Set.range z,B.gamma⟩
      (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv))
      {w | ∃ u : {x : Fin a → M // Fin.append z x ∈ D.val}, w = Fin.append u.val (e u).val}) :
    ∃ H : GammaRelationFormula B p a b sp,
      bijectiveMapRowValid sp (fun _ : Fin b => .rv) D.val F.val H.val z := by
  let W : Set (Fin (a+b) → M) :=
    {w | ∃ u : {x : Fin a → M // Fin.append z x ∈ D.val}, w = Fin.append u.val (e u).val}
  obtain ⟨Q,hQ,hrow⟩ := gamma_sorted_tuple_relation_promotion B sp
    (fun _ : Fin a => .rv) (fun _ : Fin b => .rv) z hz W hgraph
  refine ⟨⟨Q,hQ⟩,bijectiveMapRowValid_of_equiv (sy := fun _ : Fin b => .rv) (D := D.val) (E := F.val) z hz e ?_⟩
  intro x y
  refine (hrow x y).trans ?_
  constructor
  · rintro ⟨u,hu⟩
    have hx := congrArg (fun w => w ∘ Fin.castAdd b) hu
    have hy := congrArg (fun w => w ∘ Fin.natAdd a) hu
    refine ⟨u,?_,?_⟩
    · simpa only [Function.comp_def,Fin.append_left] using hx.symm
    · funext j
      have hj := congrFun hy j
      have ht : (e u).val j = y j := by
        simpa only [Function.comp_def,Fin.append_right] using hj.symm
      exact ht
  · rintro ⟨u,hu,hv⟩
    refine ⟨u,?_⟩
    rw [← hu,← hv]
    rfl

end DiamondIntegral.Section5
