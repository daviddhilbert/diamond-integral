import «section 4».RVFamilyDisjointPresentation
import «section 4».RESGrading

/-! The intrinsic measured RES ring defined by actual isomorphisms,
products and tagged disjoint unions is ring-isomorphic to the existing
RES scissor presentation, preserving every actual RES object class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESDisjointPresentation
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev family (B : Base (M := M)) := RVAdmissibleFamilies.res B
abbrev Ring (B : Base (M := M)) := RVFamilyDisjointPresentation.Ring (family B)

def toObject {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : RVFamilyDisjointPresentation.Object (family B) k :=
  ⟨a.toChart, a.finite_values⟩

def fromObject {B : Base (M := M)} {k : ℕ} (a : RVFamilyDisjointPresentation.Object (family B) k) : RESChart B k :=
  ⟨a.val, a.property⟩

def objectClass {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : Ring B :=
  RVFamilyDisjointPresentation.objectClass (family B) (toObject a)

def toChartInvariant (B : Base (M := M)) :
    RVFamilyDisjointPresentation.Invariant (family B) (RESChartRing.Ring B) where
  value _ a ha := RESChartRing.objectClass (⟨a, ha⟩ : RESChart B _)
  unit := RESChartRing.objectClass_unit B
  product _ _ a b ha hb := RESChartRing.objectClass_product (⟨a, ha⟩ : RESChart B _) (⟨b, hb⟩ : RESChart B _)
  iso _ _ _ _ _ f := RESChartRing.objectClass_iso f
  empty _ a ha h := RESChartRing.objectClass_empty (⟨a, ha⟩ : RESChart B _) h
  coproduct _ a b ha hb :=
    RVTaggedCoproductClasses.res_coproduct_class (⟨a, ha⟩ : RESChart B _) (⟨b, hb⟩ : RESChart B _)

def toChartRing (B : Base (M := M)) : Ring B →+* RESChartRing.Ring B :=
  RVFamilyDisjointPresentation.lift (family B) (toChartInvariant B)

theorem toChartRing_class (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    toChartRing B (objectClass a) = RESChartRing.objectClass a :=
  RVFamilyDisjointPresentation.lift_objectClass (family B) (toChartInvariant B) (toObject a)

def fromChartInvariant (B : Base (M := M)) : RESChartRing.Invariant B (Ring B) where
  value _ a := objectClass a
  unit := RVFamilyDisjointPresentation.objectClass_unit (family B)
  product _ _ a b := RVFamilyDisjointPresentation.objectClass_product (family B) (toObject a) (toObject b)
  iso _ a b f := RVFamilyDisjointPresentation.objectClass_iso (family B) (a := toObject a) (b := toObject b) f
  empty _ a h := RVFamilyDisjointPresentation.objectClass_empty (family B) (toObject a) h
  scissor _ a b c d h := RVFamilyDisjointPresentation.objectClass_scissor (family B)
    (toObject a) (toObject b) (toObject c) (toObject d) h

def fromChartRing (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B := RESChartRing.lift B (fromChartInvariant B)

theorem fromChartRing_class (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    fromChartRing B (RESChartRing.objectClass a) = objectClass a :=
  RESChartRing.lift_objectClass B (fromChartInvariant B) a

theorem to_from (B : Base (M := M)) : (toChartRing B).comp (fromChartRing B) = RingHom.id _ := by
  apply RESRingCoaction.hom_ext B
  intro k a
  change toChartRing B (fromChartRing B (RESChartRing.objectClass a)) = RESChartRing.objectClass a
  rw [fromChartRing_class, toChartRing_class]

theorem from_to (B : Base (M := M)) : (fromChartRing B).comp (toChartRing B) = RingHom.id _ := by
  apply RVFamilyDisjointPresentation.hom_ext (family B)
  intro k a
  change fromChartRing B (toChartRing B (objectClass (fromObject a))) = objectClass (fromObject a)
  rw [toChartRing_class, fromChartRing_class]

def equivalence (B : Base (M := M)) : Ring B ≃+* RESChartRing.Ring B :=
  RingEquiv.ofBijective (toChartRing B) ⟨(by
    intro x y h
    have he := congrArg (fromChartRing B) h
    exact (RingHom.congr_fun (from_to B) x).symm.trans (he.trans (RingHom.congr_fun (from_to B) y))), (by
    intro y
    exact ⟨fromChartRing B y, RingHom.congr_fun (to_from B) y⟩)⟩

end DiamondIntegral.Section4.RESDisjointPresentation
