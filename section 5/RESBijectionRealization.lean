import «section 5».RESBijectionSchemata
import «section 5».GammaJoinedRowGraphs
import «section 4».Section3RVChartBridge
import «section 4».RESDimensionFreeReduction
import IntegrationSection6.GammaSortedBijectionRealization

/-! A valid native RES graph schema realizes an actual underlying chart
bijection and therefore an equality in the actual ungraded RES quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 DiamondIntegral.Section4.FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def RESSetSchema.chart (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (z : Fin p → M) (h : F.Valid hc z) :
    RVMeasuredCharts.RESChart ⟨B.real ∪ Set.range z, B.gamma⟩ a :=
  Section3RVChartBridge.chartRES (F.object hc z h)

theorem RESSetSchema.chart_domain (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (z : Fin p → M) (h : F.Valid hc z) :
    (F.chart hc z h).domain = F.rowDomain z :=
  Section3RVCodeBridge.rawDomain_ofRaw (F.rowDomain z) (F.row_domain_definable z)

def RESBijectionSchema.rawEquiv (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (H : RESBijectionSchema F G) (z : Fin p → M) (h : H.Valid hc z) :
    F.rowDomain z ≃ G.rowDomain z :=
  h.2.2.equiv (fun y hy j => by
    simpa only [Fin.append_right] using G.domain.property.proper _ hy (Fin.natAdd p j))

theorem RESBijectionSchema.rawEquiv_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (H : RESBijectionSchema F G) (z : Fin p → M) (h : H.Valid hc z)
    (x : Fin a → M) (y : Fin b → M) :
    Fin.append (Fin.append z x) y ∈ H.graph.val ↔
      ∃ u : F.rowDomain z, u.val = x ∧ (H.rawEquiv hc z h u).val = y :=
  h.2.2.equiv_graph _ x y

theorem RESBijectionSchema.raw_joined_graph_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (H : RESBijectionSchema F G) (z : Fin p → M) (h : H.Valid hc z) :
    DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩ (fun _ : Fin (b + a) => .rv)
      {w | ∃ u : F.rowDomain z, w = join b a u.val (H.rawEquiv hc z h u).val} := by
  have hg := joinedRelationRow_definable H.graph z
  convert hg using 1
  ext w
  change (∃ u : F.rowDomain z, w = join b a u.val (H.rawEquiv hc z h u).val) ↔
    Fin.append (Fin.append z (w ∘ headIndex b a)) (w ∘ tailIndex b a) ∈ H.graph.val
  rw [H.rawEquiv_graph hc z h]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, (funext (join_head b a _ _)).symm, (funext (join_tail b a _ _)).symm⟩
  · rintro ⟨u, hu, hv⟩
    refine ⟨u, ?_⟩
    calc
      w = join b a (w ∘ headIndex b a) (w ∘ tailIndex b a) := (join_reconstruct b a w).symm
      _ = _ := by rw [← hu, ← hv]

def RESBijectionSchema.chartIso (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (H : RESBijectionSchema F G) (z : Fin p → M) (h : H.Valid hc z) :
    RVUnderlyingIsomorphisms.Iso (F.chart hc z h.1).toChart (G.chart hc z h.2.1).toChart := by
  let es := Set.equivOfEq (F.chart_domain hc z h.1)
  let et := Set.equivOfEq (G.chart_domain hc z h.2.1)
  let e := H.rawEquiv hc z h
  let e' := es.trans (e.trans et.symm)
  refine ⟨e', ?_⟩
  have he : {w : Fin (b + a) → M | ∃ u : (F.chart hc z h.1).domain,
      w = join b a u.val (e' u).val} =
      {w : Fin (b + a) → M | ∃ u : F.rowDomain z, w = join b a u.val (e u).val} := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨es u, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨es.symm u, ?_⟩
      change join b a u.val (e u).val = join b a (es.symm u).val (et.symm (e (es (es.symm u)))).val
      rw [es.apply_symm_apply]
      rfl
  change DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩ (fun _ : Fin (b+a) => .rv)
    {w | ∃ u : (F.chart hc z h.1).domain, w = join b a u.val (e' u).val}
  rw [he]
  exact H.raw_joined_graph_definable hc z h

theorem RESBijectionSchema.native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (H : RESBijectionSchema F G) (z : Fin p → M) (h : H.Valid hc z) :
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass (F.chart hc z h.1)) =
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass (G.chart hc z h.2.1)) :=
  congrArg (RESDimensionFreeReduction.quotient ⟨B.real ∪ Set.range z, B.gamma⟩)
    (RESDimensionFreeRing.objectClass_iso _ _ (H.chartIso hc z h))

end DiamondIntegral.Section5
