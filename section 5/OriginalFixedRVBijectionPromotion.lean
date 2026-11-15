import «section 5».OriginalRVBijectionPromotion
import «section 5».NativeRVSetValues
import «section 5».RESFixedBijectionPromotion

/-! A fixed pair of original-domain schemata retains any actual native
RV bijection at the displayed parameter as a full original-base graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem original_fixed_rv_bijection_schema_at_parameter
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (D : GammaDomainFormula B p a sp) (F : GammaDomainFormula B p b sp)
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) b))
    (hD : {v | Fin.append z v ∈ D.val} = rawDomain A)
    (hF : {v | Fin.append z v ∈ F.val} = rawDomain C)
    (f : GammaGroundBijection A C) :
    ∃ H : GammaRelationFormula B p a b sp,
      bijectiveMapRowValid sp (fun _ : Fin b => .rv) D.val F.val H.val z := by
  let PA := Section3RVChartBridge.chart (nativeRVObjectOfGammaSet A)
  let PC := Section3RVChartBridge.chart (nativeRVObjectOfGammaSet C)
  let h := nativeRVObjectUnderlyingIso (U := nativeRVObjectOfGammaSet A) (V := nativeRVObjectOfGammaSet C) f
  let es : PA.domain ≃ {v | Fin.append z v ∈ D.val} := Set.equivOfEq hD.symm
  let et : PC.domain ≃ {v | Fin.append z v ∈ F.val} := Set.equivOfEq hF.symm
  let e := es.symm.trans (h.equiv.trans et)
  let W : Set (Fin (a+b) → M) := {w | ∃ u : PA.domain, w = Fin.append u.val (h.equiv u).val}
  have hW : DefinableOverBase ⟨B.real ∪ Set.range z,B.gamma⟩
      (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv)) W :=
    joined_equiv_graph_append_definable h.equiv
      (fun x hx i => PA.domain_definable.proper x hx i)
      (fun y hy i => PC.domain_definable.proper y hy i) h.graph_definable
  have he (x : Fin a → M) (y : Fin b → M) :
      Fin.append x y ∈ W ↔ ∃ u : {v | Fin.append z v ∈ D.val}, u.val = x ∧ (e u).val = y := by
    constructor
    · rintro ⟨u,hu⟩
      have hu' : Fin.append x y = Fin.append (m := a) (n := b) u.val (h.equiv u).val := hu
      have hx := congrArg (fun w => w ∘ Fin.castAdd b) hu'
      have hy := congrArg (fun w => w ∘ Fin.natAdd a) hu'
      refine ⟨es u,?_,?_⟩
      · change u.val = x
        simpa only [Function.comp_def,Fin.append_left] using hx.symm
      · change (et (h.equiv (es.symm (es u)))).val = y
        rw [es.symm_apply_apply]
        change (h.equiv u).val = y
        simpa only [Function.comp_def,Fin.append_right] using hy.symm
    · rintro ⟨u,hu,hv⟩
      refine ⟨es.symm u,?_⟩
      change Fin.append x y = Fin.append u.val (h.equiv (es.symm u)).val
      rw [← hu,← hv]
      rfl
  obtain ⟨Q,hQ,hrow⟩ := gamma_sorted_tuple_relation_promotion B sp
    (fun _ : Fin a => .rv) (fun _ : Fin b => .rv) z hz W hW
  exact ⟨⟨Q,hQ⟩,bijectiveMapRowValid_of_equiv (sy := fun _ : Fin b => .rv)
    (D := D.val) (E := F.val) z hz e (fun x y => (hrow x y).trans (he x y))⟩

end DiamondIntegral.Section5
