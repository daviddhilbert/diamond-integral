import «section 5».RESBijectionPromotion
import «section 5».RESExpressionBijections
import IntegrationSection6.GammaRowBijectionPromotion

/-! Every actual underlying RES bijection at a parameter admits a full
original-base graph schema, with actual finite value bounds on both rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 DiamondIntegral.Section4.FiniteTupleBlocks


variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def nativeSchemaUnderlyingIso (z : Fin p → M)
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (hF : F.Valid hc z) (hG : G.Valid hc z)
    (f : GammaGroundBijection (F.object hc z hF).obj.domain (G.object hc z hG).obj.domain) :
    RVUnderlyingIsomorphisms.Iso (F.chart hc z hF).toChart (G.chart hc z hG).toChart :=
  RVUnderlyingIsomorphisms.ofMap _ _ (Section3RVCodeBridge.rawMap f.map)
    (Section3RVCodeBridge.rawMap_definable f.map) (Section3RVCodeBridge.rawMap_bijective f.map f.bijective)

theorem res_fixed_bijection_schema_at_parameter
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (hF : F.Valid hc z) (hG : G.Valid hc z)
    (f : RVUnderlyingIsomorphisms.Iso (F.chart hc z hF).toChart (G.chart hc z hG).toChart) :
    ∃ H : RESBijectionSchema F G, H.Valid hc z := by
  let A := F.chart hc z hF
  let C := G.chart hc z hG
  let es := Set.equivOfEq (F.chart_domain hc z hF)
  let et := Set.equivOfEq (G.chart_domain hc z hG)
  let e := es.symm.trans (f.equiv.trans et)
  let W : Set (Fin (a+b) → M) := {w | ∃ u : A.domain, w = Fin.append u.val (f.equiv u).val}
  have hW : DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩
      (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv)) W :=
    joined_equiv_graph_append_definable f.equiv
      (fun x hx i => A.domain_definable.proper x hx i)
      (fun y hy i => C.domain_definable.proper y hy i) f.graph_definable
  have he (x : Fin a → M) (y : Fin b → M) :
      Fin.append x y ∈ W ↔ ∃ u : F.rowDomain z, u.val = x ∧ (e u).val = y := by
    constructor
    · rintro ⟨u, hu⟩
      have hu' : Fin.append x y = Fin.append (m := a) (n := b) u.val (f.equiv u).val := hu
      have hx := congrArg (fun w => w ∘ Fin.castAdd b) hu'
      have hy := congrArg (fun w => w ∘ Fin.natAdd a) hu'
      refine ⟨es u, ?_, ?_⟩
      · change u.val = x
        simpa only [Function.comp_def, Fin.append_left] using hx.symm
      · change (et (f.equiv (es.symm (es u)))).val = y
        rw [es.symm_apply_apply]
        change (f.equiv u).val = y
        simpa only [Function.comp_def, Fin.append_right] using hy.symm
    · rintro ⟨u, hu, hv⟩
      refine ⟨es.symm u, ?_⟩
      change Fin.append x y = Fin.append u.val (f.equiv (es.symm u)).val
      rw [← hu, ← hv]
      rfl
  obtain ⟨Q, hQ, hrow⟩ := gamma_sorted_tuple_relation_promotion B sp
    (fun _ : Fin a => .rv) (fun _ : Fin b => .rv) z hz W hW
  let H : RESBijectionSchema F G := ⟨⟨Q, hQ⟩⟩
  exact ⟨H, hF, hG, bijectiveMapRowValid_of_equiv (sy := fun _ : Fin b => .rv)
    (D := F.domain.val) (E := G.domain.val) z hz e (fun x y => (hrow x y).trans (he x y))⟩

theorem res_expression_bijection_schema_at_parameter
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (E : RESExpressionSchema B p sp a) (F : RESExpressionSchema B p sp b)
    (hE : E.Valid hc z) (hF : F.Valid hc z)
    (f : GammaGroundBijection
      (E.setSchema.object hc z (E.setSchema_valid hc z hE)).obj.domain
      (F.setSchema.object hc z (F.setSchema_valid hc z hF)).obj.domain) :
    ∃ H : RESExpressionBijectionSchema E F, H.Valid hc z := by
  obtain ⟨H, _, _, hbij⟩ := res_fixed_bijection_schema_at_parameter B sp z hz E.setSchema F.setSchema
    (E.setSchema_valid hc z hE) (F.setSchema_valid hc z hF)
    (nativeSchemaUnderlyingIso z E.setSchema F.setSchema _ _ f)
  exact ⟨⟨H.graph⟩, hE, hF, hbij⟩

end DiamondIntegral.Section5
