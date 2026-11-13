import «section 4».Section3RVRestrictionBridge
import «section 4».RVDisjointPresentation
import «section 4».RVOrdinaryDisjointPresentation

/-! Native strict scissors give the actual chart ring cut relations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVChartCuts
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions Section3RVCodeBridge Section3RVRestrictionBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def insideIso {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hs : I ⊆ a.domain) :
    Iso (inside a I hI).toChart (restrict a I hI hs).toChart :=
  RVScissorComponents.sameDomainIso _ _ (Set.inter_eq_right.mpr hs) (fun _ _ => rfl)

theorem measured_cut {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hs : I ⊆ a.domain) :
    RVChartRing.objectClass (restrict a I hI hs).toChart + RVChartRing.objectClass (outside a I hI).toChart =
      RVChartRing.objectClass a.toChart := by
  have h := RVDisjointInvariants.partition_value (RVDisjointPresentation.toChartInvariant B).toAdditiveInvariant a I hI
  change RVChartRing.objectClass a.toChart = RVChartRing.objectClass (outside a I hI).toChart +
    RVChartRing.objectClass (inside a I hI).toChart at h
  rw [RVChartRing.objectClass_iso (insideIso a I hI hs)] at h
  exact (add_comm _ _).trans h.symm

theorem ordinary_cut {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hs : I ⊆ a.domain) :
    RVOrdinaryRing.objectClass (restrict a I hI hs).toChart + RVOrdinaryRing.objectClass (outside a I hI).toChart =
      RVOrdinaryRing.objectClass a.toChart := by
  let f : RVOrdinaryDisjointInvariants.AdditiveInvariant (RVAdmissibleFamilies.all B) (RVOrdinaryRing.Ring B) :=
    { value := fun _ a _ => RVOrdinaryRing.objectClass a
      iso := fun _ _ _ _ _ F => RVOrdinaryRing.objectClass_iso F
      coproduct := fun _ a b _ _ => RVTaggedCoproductProperties.ordinary_class_coproduct a b }
  have h := RVOrdinaryDisjointInvariants.partition_value (RVAdmissibleFamilies.all B) f a trivial I hI
  change RVOrdinaryRing.objectClass a.toChart = RVOrdinaryRing.objectClass (outside a I hI).toChart +
    RVOrdinaryRing.objectClass (inside a I hI).toChart at h
  rw [RVOrdinaryRing.objectClass_iso (RVForgetScissors.ofMeasured (insideIso a I hI hs))] at h
  exact (add_comm _ _).trans h.symm

def complementIso {k : ℕ} (U : GammaGroundRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) :
    RVForgetScissors.UnderlyingIso
      (Section3RVChartBridge.chart (U.restrict (U.domain.sdiff X) (fun _ h => h.1)))
      (outside (ofChart (Section3RVChartBridge.chart U)) (rawDomain X) (rawDomain_definable X)).toChart :=
  RVForgetScissors.ofMap _ _ id (RVSharpCharts.identity_graph_definable B _ (rawDomain_definable _)) (by
    change Set.BijOn id (rawDomain (U.domain.sdiff X)) (rawDomain U.domain \ rawDomain X)
    rw [rawDomain_sdiff]
    exact Set.bijOn_id _)

def measuredComplementIso {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity)) :
    Iso (Section3MeasuredRVChartBridge.chart (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1)))
      (outside (ofChart (Section3MeasuredRVChartBridge.chart U)) (rawDomain X) (rawDomain_definable X)).toChart where
  equiv := (complementIso U.underlying X).equiv
  graph_definable := (complementIso U.underlying X).graph_definable
  weight_eq u := by
    let a := (rawEquiv (U.underlying.domain.sdiff X)).symm u
    have ha := rawEquiv_symm_value (U.underlying.domain.sdiff X) u
    change (Section3MeasuredRVChartBridge.chart (U.restrict (U.underlying.domain.sdiff X) _)).correctedWeight u.val =
      (Section3MeasuredRVChartBridge.chart U).correctedWeight u.val
    rw [← ha]
    exact (Section3MeasuredRVChartBridge.chart_weight (U.restrict (U.underlying.domain.sdiff X) _) a).trans
      (Section3MeasuredRVChartBridge.chart_weight U
        (GammaGroundMap.inclusion (show (U.underlying.domain.sdiff X).carrier ⊆ U.underlying.domain.carrier from
          fun _ h => h.1) a)).symm

theorem ordinary_native_cut {k : ℕ} (U : GammaGroundRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier) :
    RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (U.restrict X hX)) +
      RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (U.restrict (U.domain.sdiff X) (fun _ h => h.1))) =
        RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U) := by
  rw [RVOrdinaryRing.objectClass_iso (restrictionIso U X hX), RVOrdinaryRing.objectClass_iso (complementIso U X)]
  exact ordinary_cut _ _ _ (rawDomain_mono hX)

theorem measured_native_cut {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart (U.restrict X hX)) +
      RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1))) =
        RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart U) := by
  rw [RVChartRing.objectClass_iso (measuredRestrictionIso U X hX), RVChartRing.objectClass_iso (measuredComplementIso U X)]
  exact measured_cut _ _ _ (rawDomain_mono hX)

end DiamondIntegral.Section4.Section3RVChartCuts
