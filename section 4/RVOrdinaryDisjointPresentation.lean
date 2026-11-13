import «section 4».RVOrdinaryFamilyPresentation
import «section 4».RVOrdinaryGrading

/-! The intrinsic ordinary RV ring defined by actual isomorphisms,
products and tagged disjoint unions is ring-isomorphic to the existing
RV scissor presentation, preserving every actual RV object class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryDisjointPresentation
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev family (B : Base (M := M)) := RVAdmissibleFamilies.all B
abbrev Ring (B : Base (M := M)) := RVOrdinaryFamilyPresentation.Ring (family B)

def toObject {B : Base (M := M)} {k : ℕ} (a : Chart B k) : RVOrdinaryFamilyPresentation.Object (family B) k :=
  ⟨a, trivial⟩

def fromObject {B : Base (M := M)} {k : ℕ} (a : RVOrdinaryFamilyPresentation.Object (family B) k) : Chart B k :=
  a.val

def objectClass {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Ring B :=
  RVOrdinaryFamilyPresentation.objectClass (family B) (toObject a)

def toChartInvariant (B : Base (M := M)) :
    RVOrdinaryFamilyPresentation.Invariant (family B) (RVOrdinaryRing.Ring B) where
  value _ a ha := RVOrdinaryRing.objectClass a
  unit := RVOrdinaryRing.objectClass_unit B
  product _ _ a b ha hb := RVOrdinaryRing.objectClass_product a b
  iso _ _ _ _ _ f := RVOrdinaryRing.objectClass_iso f
  empty _ a ha h := RVOrdinaryRing.objectClass_empty a h
  coproduct _ a b ha hb :=
    RVTaggedCoproductProperties.ordinary_class_coproduct a b

def toChartRing (B : Base (M := M)) : Ring B →+* RVOrdinaryRing.Ring B :=
  RVOrdinaryFamilyPresentation.lift (family B) (toChartInvariant B)

theorem toChartRing_class (B : Base (M := M)) {k : ℕ} (a : Chart B k) :
    toChartRing B (objectClass a) = RVOrdinaryRing.objectClass a :=
  RVOrdinaryFamilyPresentation.lift_objectClass (family B) (toChartInvariant B) (toObject a)

def fromChartInvariant (B : Base (M := M)) : RVOrdinaryRing.Invariant B (Ring B) where
  value _ a := objectClass a
  unit := RVOrdinaryFamilyPresentation.objectClass_unit (family B)
  product _ _ a b := RVOrdinaryFamilyPresentation.objectClass_product (family B) (toObject a) (toObject b)
  iso _ a b f := RVOrdinaryFamilyPresentation.objectClass_iso (family B) (a := toObject a) (b := toObject b) f
  empty _ a h := RVOrdinaryFamilyPresentation.objectClass_empty (family B) (toObject a) h
  scissor _ a b c d h := RVOrdinaryFamilyPresentation.objectClass_scissor (family B)
    (toObject a) (toObject b) (toObject c) (toObject d) h

def fromChartRing (B : Base (M := M)) : RVOrdinaryRing.Ring B →+* Ring B := RVOrdinaryRing.lift B (fromChartInvariant B)

theorem fromChartRing_class (B : Base (M := M)) {k : ℕ} (a : Chart B k) :
    fromChartRing B (RVOrdinaryRing.objectClass a) = objectClass a :=
  RVOrdinaryRing.lift_objectClass B (fromChartInvariant B) a

theorem to_from (B : Base (M := M)) : (toChartRing B).comp (fromChartRing B) = RingHom.id _ := by
  apply RVOrdinaryRing.hom_ext B
  intro k a
  change toChartRing B (fromChartRing B (RVOrdinaryRing.objectClass a)) = RVOrdinaryRing.objectClass a
  rw [fromChartRing_class, toChartRing_class]

theorem from_to (B : Base (M := M)) : (fromChartRing B).comp (toChartRing B) = RingHom.id _ := by
  apply RVOrdinaryFamilyPresentation.hom_ext (family B)
  intro k a
  change fromChartRing B (toChartRing B (objectClass (fromObject a))) = objectClass (fromObject a)
  rw [toChartRing_class, fromChartRing_class]

def equivalence (B : Base (M := M)) : Ring B ≃+* RVOrdinaryRing.Ring B :=
  RingEquiv.ofBijective (toChartRing B) ⟨(by
    intro x y h
    have he := congrArg (fromChartRing B) h
    exact (RingHom.congr_fun (from_to B) x).symm.trans (he.trans (RingHom.congr_fun (from_to B) y))), (by
    intro y
    exact ⟨fromChartRing B y, RingHom.congr_fun (to_from B) y⟩)⟩

end DiamondIntegral.Section4.RVOrdinaryDisjointPresentation
