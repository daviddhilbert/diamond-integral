import «section 4».Section3RVChartCuts
import «section 4».RESDisjointPresentation
import «section 4».RESOrdinaryDisjointPresentation
import «section 3».GammaGroundMeasuredRESScissors

/-! Native RES scissors descend to actual RES chart classes. Every cut
keeps finite value support; the ordinary case forgets only the form. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RESChartCuts
open RVMeasuredCharts RVChartDisjointUnion Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def restrict {k : ℕ} (a : RESChart B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) (hs : I ⊆ a.domain) : RESChart B k :=
  ⟨(RVChartRestrictions.restrict (ofChart a.toChart) I hI hs).toChart,
    (RVAdmissibleFamilies.res B).restrict _ _ _ I hI hs a.finite_values⟩
def outside {k : ℕ} (a : RESChart B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) : RESChart B k :=
  ⟨(RVChartRestrictions.outside (ofChart a.toChart) I hI).toChart,
    (RVAdmissibleFamilies.res B).outside_good _ I hI a.finite_values⟩
def inside {k : ℕ} (a : RESChart B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) : RESChart B k :=
  ⟨(RVChartRestrictions.inside (ofChart a.toChart) I hI).toChart,
    (RVAdmissibleFamilies.res B).inside_good _ I hI a.finite_values⟩

theorem ordinary_cut {k : ℕ} (a : RESChart B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) (hs : I ⊆ a.domain) :
    RESOrdinaryRing.objectClass (restrict a I hI hs) + RESOrdinaryRing.objectClass (outside a I hI) = RESOrdinaryRing.objectClass a := by
  have h := RVOrdinaryDisjointInvariants.partition_value (RVAdmissibleFamilies.res B)
    (RESOrdinaryDisjointPresentation.toChartInvariant B).toAdditiveInvariant (ofChart a.toChart) a.finite_values I hI
  change RESOrdinaryRing.objectClass a = RESOrdinaryRing.objectClass (outside a I hI) + RESOrdinaryRing.objectClass (inside a I hI) at h
  rw [RESOrdinaryRing.objectClass_iso (a := inside a I hI) (b := restrict a I hI hs)
    (RVForgetScissors.ofMeasured (Section3RVChartCuts.insideIso (ofChart a.toChart) I hI hs))] at h
  exact (add_comm _ _).trans h.symm

theorem measured_cut {k : ℕ} (a : RESChart B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) (hs : I ⊆ a.domain) :
    RESChartRing.objectClass (restrict a I hI hs) + RESChartRing.objectClass (outside a I hI) = RESChartRing.objectClass a := by
  have h := RVAdmissibleDisjointInvariants.partition_value (RVAdmissibleFamilies.res B)
    (RESDisjointPresentation.toChartInvariant B).toAdditiveInvariant (ofChart a.toChart) a.finite_values I hI
  change RESChartRing.objectClass a = RESChartRing.objectClass (outside a I hI) + RESChartRing.objectClass (inside a I hI) at h
  rw [RESChartRing.objectClass_iso (a := inside a I hI) (b := restrict a I hI hs)
    (Section3RVChartCuts.insideIso (ofChart a.toChart) I hI hs)] at h
  exact (add_comm _ _).trans h.symm

theorem ordinary_native_cut {k : ℕ} (U : GammaGroundRESObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity)) (hX : X.carrier ⊆ U.obj.domain.carrier) :
    RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES (U.restrict X hX)) +
      RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1))) =
        RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES U) := by
  let a := Section3RVChartBridge.chartRES U
  have hs := Section3RVRestrictionBridge.rawDomain_mono hX
  have hi := RESOrdinaryRing.objectClass_iso (a := Section3RVChartBridge.chartRES (U.restrict X hX))
    (b := restrict a (rawDomain X) (rawDomain_definable X) hs) (Section3RVRestrictionBridge.restrictionIso U.obj X hX)
  have ho := RESOrdinaryRing.objectClass_iso
    (a := Section3RVChartBridge.chartRES (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)))
    (b := outside a (rawDomain X) (rawDomain_definable X)) (Section3RVChartCuts.complementIso U.obj X)
  rw [hi, ho]
  exact ordinary_cut a _ _ hs

theorem measured_native_cut {k : ℕ} (U : GammaGroundMeasuredRESObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.underlying.arity))
    (hX : X.carrier ⊆ U.obj.underlying.domain.carrier) :
    RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES (U.restrict X hX)) +
      RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES (U.restrict (U.obj.underlying.domain.sdiff X) (fun _ h => h.1))) =
        RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES U) := by
  let a := Section3MeasuredRVChartBridge.chartRES U
  have hs := Section3RVRestrictionBridge.rawDomain_mono hX
  have hi := RESChartRing.objectClass_iso (a := Section3MeasuredRVChartBridge.chartRES (U.restrict X hX))
    (b := restrict a (rawDomain X) (rawDomain_definable X) hs) (Section3RVRestrictionBridge.measuredRestrictionIso U.obj X hX)
  have ho := RESChartRing.objectClass_iso
    (a := Section3MeasuredRVChartBridge.chartRES (U.restrict (U.obj.underlying.domain.sdiff X) (fun _ h => h.1)))
    (b := outside a (rawDomain X) (rawDomain_definable X)) (Section3RVChartCuts.measuredComplementIso U.obj X)
  rw [hi, ho]
  exact measured_cut a _ _ hs

theorem ordinary_obj_eq {k : ℕ} {U V : GammaGroundRESObject hc B k} (h : U.obj = V.obj) :
    RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES U) = RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES V) := by
  have f : GammaGroundBijection U.obj.domain V.obj.domain := by rw [h]; exact GammaGroundBijection.id _
  exact RESOrdinaryRing.objectClass_iso (Section3RVChartBridge.chartIso f)

theorem measured_obj_eq {k : ℕ} {U V : GammaGroundMeasuredRESObject hc B k} (h : U.obj = V.obj) :
    RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES U) = RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES V) := by
  have f : GammaGroundMeasuredRVHom U.obj V.obj := by rw [h]; exact GammaGroundMeasuredRVHom.id _
  exact RESChartRing.objectClass_iso (Section3MeasuredRVChartBridge.chartIso f)

@[simp] theorem ordinary_empty (k : ℕ) : RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES (GammaGroundRESObject.empty hc B k)) = 0 := by
  apply RESOrdinaryRing.objectClass_empty
  change rvValues '' (∅ : Set (Fin 0 → CanonicalRV.RVSort M)) = ∅
  exact Set.image_empty _
@[simp] theorem measured_empty (k : ℕ) : RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES (GammaGroundMeasuredRESObject.empty hc B k)) = 0 := by
  apply RESChartRing.objectClass_empty
  change rvValues '' (∅ : Set (Fin 0 → CanonicalRV.RVSort M)) = ∅
  exact Set.image_empty _

theorem ordinary_scissor {k : ℕ} {a b d e : GammaGroundRESObject hc B k}
    (h : gammaGroundRVScissor a.obj b.obj d.obj e.obj) :
    RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES a) + RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES b) =
      RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES d) + RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES e) := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst U
  rw [ordinary_obj_eq (V := d.restrict X hX) hA,
    ordinary_obj_eq (V := d.restrict (d.obj.domain.sdiff X) (fun _ h => h.1)) hB,
    ordinary_obj_eq (V := GammaGroundRESObject.empty hc B k) hE, ordinary_empty, add_zero]
  exact ordinary_native_cut d X hX

theorem measured_scissor {k : ℕ} {a b d e : GammaGroundMeasuredRESObject hc B k}
    (h : gammaGroundMeasuredRVScissor a.obj b.obj d.obj e.obj) :
    RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES a) + RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES b) =
      RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES d) + RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES e) := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst U
  rw [measured_obj_eq (V := d.restrict X hX) hA,
    measured_obj_eq (V := d.restrict (d.obj.underlying.domain.sdiff X) (fun _ h => h.1)) hB,
    measured_obj_eq (V := GammaGroundMeasuredRESObject.empty hc B k) hE, measured_empty, add_zero]
  exact measured_native_cut d X hX

end DiamondIntegral.Section4.Section3RESChartCuts
