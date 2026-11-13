import «section 4».RESChartRing
import «section 4».RVForgetScissors
import «section 4».RVWeightScaling

/-! A concrete ordinary RES chart ring. Volume labels on the generators
are redundant and are ignored by the actual underlying definable
isomorphism relation. The measured-to-ordinary forgetful ring map is
constructed from proved preservation of every relation. Grading and
finite-coproduct category identification remain separate obligations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESOrdinaryRing
open RVMeasuredCharts RVMeasuredProductProperties RVForgetScissors

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Generator (B : Base (M := M)) := RESChartRing.Generator B

def symbol {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : FreeCommRing (Generator B) := RESChartRing.symbol a

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (symbol (RESChartRing.unit B) - 1)
  | product {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
      Relation B (symbol (resProduct a b) - symbol a * symbol b)
  | iso {k : ℕ} (a b : RESChart B k) (F : UnderlyingIso a.toChart b.toChart) : Relation B (symbol a - symbol b)
  | empty {k : ℕ} (a : RESChart B k) (h : a.domain = ∅) : Relation B (symbol a)
  | scissor {k : ℕ} (a b c d : RESChart B k) (h : RVForgetScissors.Scissor a.toChart b.toChart c.toChart d.toChart) :
      Relation B (symbol c + symbol d - symbol a - symbol b)

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Generator B)) := Ideal.span {r | Relation B r}

def Ring (B : Base (M := M)) := FreeCommRing (Generator B) ⧸ relationIdeal B
  deriving CommRing

def objectClass {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : Ring B :=
  Ideal.Quotient.mk (relationIdeal B) (symbol a)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit (B : Base (M := M)) : objectClass (RESChartRing.unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem objectClass_product {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    objectClass (resProduct a b) = objectClass a * objectClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {B : Base (M := M)} {k : ℕ} {a b : RESChart B k} (F : UnderlyingIso a.toChart b.toChart) :
    objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b F)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} {k : ℕ} (a : RESChart B k) (ha : a.domain = ∅) :
    objectClass a = 0 := relation_zero B _ (Relation.empty a ha)

theorem objectClass_scissor {B : Base (M := M)} {k : ℕ} (a b c d : RESChart B k)
    (h : RVForgetScissors.Scissor a.toChart b.toChart c.toChart d.toChart) :
    objectClass c + objectClass d = objectClass a + objectClass b := by
  have hr := relation_zero B _ (Relation.scissor a b c d h)
  rw [map_sub, map_sub, map_add, sub_sub] at hr
  exact sub_eq_zero.mp hr

def forgetInvariant (B : Base (M := M)) : RESChartRing.Invariant B (Ring B) where
  value _ a := objectClass a
  unit := objectClass_unit B
  product _ _ a b := objectClass_product a b
  iso _ _a _b F := objectClass_iso (ofMeasured F)
  empty _ a ha := objectClass_empty a ha
  scissor _ a b c d h := objectClass_scissor a b c d (measured_scissor _ _ _ _ h)

def forget (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B := RESChartRing.lift B (forgetInvariant B)

theorem forget_objectClass (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    forget B (RESChartRing.objectClass a) = objectClass a := RESChartRing.lift_objectClass B (forgetInvariant B) a

def trivialVolume {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Chart B k :=
  {a with volume := fun _ => 1
          volume_definable := constant_volume_definable B a.domain a.domain_definable 1 (GammaGroupNames.one_definable_base B)}

def trivialRES {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : RESChart B k :=
  ⟨trivialVolume a.toChart, a.finite_values⟩

def trivialIso {B : Base (M := M)} {k : ℕ} (a : Chart B k) : UnderlyingIso a (trivialVolume a) :=
  ofMap a (trivialVolume a) id (RVSharpCharts.identity_graph_definable B a.domain a.domain_definable)
    ⟨(fun _ h => h), (fun _ _ _ _ h => h), (fun y hy => ⟨y, hy, rfl⟩)⟩

theorem objectClass_trivial {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : objectClass a = objectClass (trivialRES a) :=
  objectClass_iso (trivialIso a.toChart)

theorem forget_weightedUnit (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : forget B (RESChartRing.objectClass (weightedRESUnit B γ hγ)) = 1 :=
  (forget_objectClass B _).trans ((objectClass_trivial (weightedRESUnit B γ hγ)).trans (objectClass_unit B))

theorem scaled_class {B : Base (M := M)} {k : ℕ} (a : RESChart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : objectClass (RVWeightScaling.scaledRES a γ hγ) = objectClass a :=
  (objectClass_trivial (RVWeightScaling.scaledRES a γ hγ)).trans (objectClass_trivial a).symm

end DiamondIntegral.Section4.RESOrdinaryRing
