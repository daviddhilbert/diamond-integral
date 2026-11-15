import «section 4».RESOrdinaryUniversal
import «section 4».RESDimensionFreeReduction
import «section 5».RealGammaGroundElimination

/-! The ordinary and reduced ungraded RES rings depend only on actual
sorted definability. Gamma names definable over the real ground can thus
be eliminated without extending that ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)),
  DefinableOverBase B sn A → DefinableOverBase C sn A)

def resGroundTransferChart {k : ℕ} (a : Chart B k) : Chart C k where
  arity := a.arity
  domain := a.domain
  domain_definable := H _ _ a.domain_definable
  coordinate := a.coordinate
  coordinate_definable := H _ _ a.coordinate_definable
  coordinate_proper := a.coordinate_proper
  finite_fibres := a.finite_fibres
  volume := fun _ => 1
  volume_definable := constant_volume_definable C a.domain (H _ _ a.domain_definable) 1
    (GammaGroupNames.one_definable_base C)

def resGroundTransferObject {k : ℕ} (a : RESChart B k) : RESChart C k :=
  ⟨resGroundTransferChart H a.toChart,a.finite_values⟩

def resGroundTransferIso {k l : ℕ} {a : Chart B k} {b : Chart B l}
    (f : RVUnderlyingIsomorphisms.Iso a b) :
    RVUnderlyingIsomorphisms.Iso (resGroundTransferChart H a) (resGroundTransferChart H b) :=
  ⟨f.equiv,H _ _ f.graph_definable⟩

def resGroundTransferInvariant : RESOrdinaryRing.Invariant B (RESOrdinaryRing.Ring C) where
  value _ a := RESOrdinaryRing.objectClass (resGroundTransferObject H a)
  unit := by
    exact (RESOrdinaryRing.objectClass_iso (RVForgetScissors.ofMap _ _ id
      (RVSharpCharts.identity_graph_definable C _ (H _ _ (RESChartRing.unit B).domain_definable))
      (Set.bijOn_id _))).trans (RESOrdinaryRing.objectClass_unit C)
  product _ _ a b := by
    exact (RESOrdinaryRing.objectClass_iso (RVForgetScissors.ofMap
      (resGroundTransferObject H (RVMeasuredProductProperties.resProduct a b)).toChart
      (RVMeasuredProductProperties.resProduct (resGroundTransferObject H a) (resGroundTransferObject H b)).toChart id
      (RVSharpCharts.identity_graph_definable C _ (H _ _ (RVMeasuredProductProperties.resProduct a b).domain_definable))
      (Set.bijOn_id _))).trans (RESOrdinaryRing.objectClass_product (resGroundTransferObject H a) (resGroundTransferObject H b))
  iso _ _ _ f := RESOrdinaryRing.objectClass_iso (RVUnderlyingIsomorphisms.toFixed
    (resGroundTransferIso H (RVUnderlyingIsomorphisms.ofFixed f)))
  empty _ a h := RESOrdinaryRing.objectClass_empty (resGroundTransferObject H a) h
  scissor _ a b c d h := RESOrdinaryRing.objectClass_scissor _ _ _ _ h

def resGroundTransferOrdinary : RESOrdinaryRing.Ring B →+* RESOrdinaryRing.Ring C :=
  RESOrdinaryRing.lift B (resGroundTransferInvariant H)

theorem resGroundTransferOrdinary_class {k : ℕ} (a : RESChart B k) :
    resGroundTransferOrdinary H (RESOrdinaryRing.objectClass a) =
      RESOrdinaryRing.objectClass (resGroundTransferObject H a) :=
  RESOrdinaryRing.lift_objectClass B (resGroundTransferInvariant H) a

def resGroundTransferGamma (α : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) : GammaDefinableClosureAtBase C α :=
  H _ _ hα

def resGroundTransferFibreIso (α : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) : RVForgetScissors.UnderlyingIso
    (resGroundTransferObject H (RESFibreObjects.fibre B α 1 hα (GammaGroupNames.one_definable_base B))).toChart
    (RESFibreObjects.fibre C α 1 (resGroundTransferGamma H α hα) (GammaGroupNames.one_definable_base C)).toChart :=
  RVForgetScissors.ofMap _ _ id
    (RVSharpCharts.identity_graph_definable C _ (H _ _ (RESFibreObjects.fibre B α 1 hα
      (GammaGroupNames.one_definable_base B)).domain_definable)) (Set.bijOn_id _)

def resGroundTransferToReduced : RESOrdinaryRing.Ring B →+* RESDimensionFreeReduction.Ring C :=
  (RESDimensionFreeReduction.fromOrdinary C).comp (resGroundTransferOrdinary H)

theorem resGroundTransfer_degreeIdeal : RESDimensionFreeRing.degreeIdeal B ≤
    RingHom.ker (resGroundTransferToReduced H) := by
  apply Ideal.span_le.mpr
  rintro x ⟨k,l,a,b,f,rfl⟩
  change RESDimensionFreeReduction.fromOrdinary C (resGroundTransferOrdinary H (_ - _)) = 0
  rw [map_sub,resGroundTransferOrdinary_class,resGroundTransferOrdinary_class,map_sub]
  exact sub_eq_zero.mpr (congrArg (RESDimensionFreeReduction.quotient C)
    (RESDimensionFreeRing.objectClass_iso _ _ (resGroundTransferIso H f)))

theorem resGroundTransfer_fibreIdeal : RESOrdinaryReduction.fibreIdeal B ≤
    RingHom.ker (resGroundTransferToReduced H) := by
  apply Ideal.span_le.mpr
  rintro x ⟨α,hα,rfl⟩
  change RESDimensionFreeReduction.fromOrdinary C (resGroundTransferOrdinary H (_ - _)) = 0
  simp only [RESFibreObjects.torus]
  rw [map_sub,resGroundTransferOrdinary_class,resGroundTransferOrdinary_class,
    RESOrdinaryRing.objectClass_iso (resGroundTransferFibreIso H α hα),
    RESOrdinaryRing.objectClass_iso (resGroundTransferFibreIso H 1 (GammaGroupNames.one_definable_base B)),map_sub]
  exact sub_eq_zero.mpr (congrArg (RESDimensionFreeReduction.fromGradedReduced C)
    (RESOrdinaryReduction.fibre_class C α 1 (resGroundTransferGamma H α hα)
      (GammaGroupNames.one_definable_base C)))

def resGroundTransferUngradedReduced : RESDimensionFreeRing.Ring B →+* RESDimensionFreeReduction.Ring C :=
  Ideal.Quotient.lift (RESDimensionFreeRing.degreeIdeal B) (resGroundTransferToReduced H)
    (fun _ h => resGroundTransfer_degreeIdeal H h)

theorem resGroundTransferUngradedReduced_kills : RESDimensionFreeReduction.fibreIdeal B ≤
    RingHom.ker (resGroundTransferUngradedReduced H) := by
  apply Ideal.map_le_iff_le_comap.mpr
  exact resGroundTransfer_fibreIdeal H

def resGroundTransferReduced : RESDimensionFreeReduction.Ring B →+* RESDimensionFreeReduction.Ring C :=
  Ideal.Quotient.lift (RESDimensionFreeReduction.fibreIdeal B) (resGroundTransferUngradedReduced H)
    (fun _ h => resGroundTransferUngradedReduced_kills H h)

def eliminateRealGammaRES (B : Base (M := M))
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ) :
    RESDimensionFreeReduction.Ring B →+* RESDimensionFreeReduction.Ring (EmptyGammaGround.base B.real) :=
  resGroundTransferReduced (fun sn A h => (realGammaGround_definable_iff B hγ sn A).mp h)

end DiamondIntegral.Section5
