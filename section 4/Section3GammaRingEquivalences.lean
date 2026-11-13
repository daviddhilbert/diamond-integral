import «section 4».Section3GammaNativeRingMaps
import «section 4».Section3GammaChartAddMaps
import «section 4».ObjectClassAdditiveGeneration
import «section 3».GammaPieceSums
import «section 3».MeasuredGammaPieceSums
import «section 3».CompletionDirectSum

/-! Actual Gamma ring equivalences, including arbitrary finite tags and
all partial measured forms, from inverse object-class formulas. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3GammaRingEquivalences
open Section3GammaChartBridge Section3GammaNativeClassCuts Section3GammaFamilyClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

theorem ordinary_add_class {n : ℕ} (U : GammaGroundGammaObject hc B n) :
    Section3GammaChartAddMaps.ordinary hc B (ordinaryClass U) = ordinaryValue U :=
  Section3GammaChartAddMaps.ordinary_class hc B U
theorem measured_add_class {n : ℕ} (U : GammaGroundMeasuredGammaObject hc B n) :
    Section3GammaChartAddMaps.measured hc B (measuredClass U) = measuredValue U :=
  Section3GammaChartAddMaps.measured_class hc B U

def ordinaryPresentation : ObjectClassAdditiveGeneration.Presentation (GammaOrdinaryRing.Generator B) (GammaOrdinaryRing.Ring B) where
  objectClass a := GammaOrdinaryRing.objectClass a.2
  unit := ⟨0, GammaOrdinaryCharts.unit B⟩
  class_unit := GammaOrdinaryRing.class_unit B
  product a b := ⟨b.1 + a.1, GammaOrdinaryCharts.product a.2 b.2⟩
  class_product a b := GammaOrdinaryRing.class_product a.2 b.2
  free := Ideal.Quotient.mk (GammaOrdinaryRing.relationIdeal B)
  free_of _ := rfl
  surjective := Ideal.Quotient.mk_surjective

def measuredPresentation : ObjectClassAdditiveGeneration.Presentation (GammaChartPresentation.Generator B) (GammaRVChartPresentation.ChartRing B) where
  objectClass a := GammaRVChartPresentation.objectClass a.2
  unit := ⟨0, GammaChartOperations.unit B⟩
  class_unit := GammaRVChartPresentation.class_unit B
  product a b := ⟨b.1 + a.1, GammaChartOperations.product a.2 b.2⟩
  class_product a b := GammaRVChartPresentation.class_product a.2 b.2
  free := Ideal.Quotient.mk (GammaRVChartPresentation.relationIdeal B)
  free_of _ := rfl
  surjective := Ideal.Quotient.mk_surjective

theorem ordinary_toDirectSum_class {n : ℕ} (U : GammaGroundGammaObject hc B n) :
    ringCompletionCongr (gammaGroundGammaSemiringEquivDirectSum (hc := hc) (ground := B)) (ordinaryClass U) =
      of (gammaGroundGammaDirectSumClass hc U) := by
  rw [ordinaryClass, ringCompletionCongr_of]
  exact congrArg of (gammaGroundGammaPresentationToDirectSum_class U)

theorem measured_toDirectSum_class {n : ℕ} (U : GammaGroundMeasuredGammaObject hc B n) :
    ringCompletionCongr (gammaGroundMeasuredGammaSemiringEquivDirectSum (hc := hc) (ground := B)) (measuredClass U) =
      of (gammaGroundMeasuredGammaDirectSumClass hc U) := by
  rw [measuredClass, ringCompletionCongr_of]
  exact congrArg of (gammaGroundMeasuredGammaPresentationToDirectSum_class U)

theorem ordinary_addHom_ext {G : Type*} [AddCommGroup G]
    (f g : GammaGroundGammaGrothendieckRing hc B →+ G)
    (h : ∀ n (U : GammaGroundGammaObject hc B n), f (ordinaryClass U) = g (ordinaryClass U)) : f = g := by
  let E := ringCompletionCongr (gammaGroundGammaSemiringEquivDirectSum (hc := hc) (ground := B))
  have hh : f.comp E.symm.toAddEquiv.toAddMonoidHom = g.comp E.symm.toAddEquiv.toAddMonoidHom := by
    apply completionAddHom_ext
    have hd : ((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) =
        ((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) := by
      apply DirectSum.addHom_ext
      intro n
      have hp : (((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundGammaKPlus hc B) n)) =
          (((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundGammaKPlus hc B) n)) := by
        apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundGammaPresentation hc B n)
        intro U
        change f (E.symm (of (gammaGroundGammaDirectSumClass hc U))) = g (E.symm (of (gammaGroundGammaDirectSumClass hc U)))
        rw [← ordinary_toDirectSum_class hc B U, RingEquiv.symm_apply_apply]
        exact h n U
      exact DFunLike.congr_fun hp
    exact DFunLike.congr_fun hd
  exact AddMonoidHom.ext (fun x => by
    have hx := DFunLike.congr_fun hh (E x)
    change f (E.symm (E x)) = g (E.symm (E x)) at hx
    simpa only [RingEquiv.symm_apply_apply] using hx)

theorem measured_addHom_ext {G : Type*} [AddCommGroup G]
    (f g : GammaGroundMeasuredGammaGrothendieckRing hc B →+ G)
    (h : ∀ n (U : GammaGroundMeasuredGammaObject hc B n), f (measuredClass U) = g (measuredClass U)) : f = g := by
  let E := ringCompletionCongr (gammaGroundMeasuredGammaSemiringEquivDirectSum (hc := hc) (ground := B))
  have hh : f.comp E.symm.toAddEquiv.toAddMonoidHom = g.comp E.symm.toAddEquiv.toAddMonoidHom := by
    apply completionAddHom_ext
    have hd : ((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) =
        ((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) := by
      apply DirectSum.addHom_ext
      intro n
      have hp : (((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundMeasuredGammaKPlus hc B) n)) =
          (((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundMeasuredGammaKPlus hc B) n)) := by
        apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundMeasuredGammaPresentation hc B n)
        intro U
        change f (E.symm (of (gammaGroundMeasuredGammaDirectSumClass hc U))) = g (E.symm (of (gammaGroundMeasuredGammaDirectSumClass hc U)))
        rw [← measured_toDirectSum_class hc B U, RingEquiv.symm_apply_apply]
        exact h n U
      exact DFunLike.congr_fun hp
    exact DFunLike.congr_fun hd
  exact AddMonoidHom.ext (fun x => by
    have hx := DFunLike.congr_fun hh (E x)
    change f (E.symm (E x)) = g (E.symm (E x)) at hx
    simpa only [RingEquiv.symm_apply_apply] using hx)

theorem ordinary_chart_native :
    (Section3GammaChartAddMaps.ordinary hc B).comp (Section3GammaNativeRingMaps.ordinary hc B).toAddMonoidHom = AddMonoidHom.id _ := by
  apply ObjectClassAdditiveGeneration.hom_ext (ordinaryPresentation B)
  rintro ⟨n, a⟩
  change Section3GammaChartAddMaps.ordinary hc B (Section3GammaNativeRingMaps.ordinary hc B (GammaOrdinaryRing.objectClass a)) = GammaOrdinaryRing.objectClass a
  rw [Section3GammaNativeRingMaps.ordinary_class, ordinary_add_class]
  change (∑ i : Fin 1, GammaOrdinaryRing.objectClass (chart (Section3GammaCodeBridge.native hc a.support a.support_definable))) = _
  rw [Fin.sum_univ_one, Section3GammaRoundtripBridge.ordinary_chart_native]

theorem measured_chart_native :
    (Section3GammaChartAddMaps.measured hc B).comp (Section3GammaNativeRingMaps.measured hc B).toAddMonoidHom = AddMonoidHom.id _ := by
  apply ObjectClassAdditiveGeneration.hom_ext (measuredPresentation B)
  rintro ⟨n, a⟩
  change Section3GammaChartAddMaps.measured hc B (Section3GammaNativeRingMaps.measured hc B (GammaRVChartPresentation.objectClass a)) = GammaRVChartPresentation.objectClass a
  rw [Section3GammaNativeRingMaps.measured_class, measured_add_class]
  change (∑ i : Fin 1, GammaRVChartPresentation.objectClass (measuredChart
    (Section3GammaCodeBridge.native hc a.support a.support_definable)
    (Section3GammaCodeBridge.form hc a.support a.support_definable a.normalizedVolume a.normalizedVolume_definable))) = _
  rw [Fin.sum_univ_one]
  exact GammaRVChartPresentation.class_iso (Section3GammaRoundtripBridge.measured_chart_native a)

theorem ordinary_native_chart :
    (Section3GammaNativeRingMaps.ordinary hc B).toAddMonoidHom.comp (Section3GammaChartAddMaps.ordinary hc B) = AddMonoidHom.id _ := by
  apply ordinary_addHom_ext hc B
  intro n U
  change Section3GammaNativeRingMaps.ordinary hc B (Section3GammaChartAddMaps.ordinary hc B (ordinaryClass U)) = ordinaryClass U
  rw [ordinary_add_class]
  change Section3GammaNativeRingMaps.ordinary hc B (∑ i, GammaOrdinaryRing.objectClass (chart (U.piece i))) = _
  simp only [map_sum, Section3GammaNativeRingMaps.ordinary_class, Section3GammaRoundtripBridge.ordinary_native_chart]
  have h := congrArg (of : GammaGroundGammaPositiveSemiring hc B → GammaGroundGammaGrothendieckRing hc B)
    (gammaGroundGammaSemiringClass_tag_sum U)
  simpa only [map_sum, ordinaryClass] using h.symm

theorem measured_native_chart :
    (Section3GammaNativeRingMaps.measured hc B).toAddMonoidHom.comp (Section3GammaChartAddMaps.measured hc B) = AddMonoidHom.id _ := by
  apply measured_addHom_ext hc B
  intro n U
  change Section3GammaNativeRingMaps.measured hc B (Section3GammaChartAddMaps.measured hc B (measuredClass U)) = measuredClass U
  rw [measured_add_class]
  change Section3GammaNativeRingMaps.measured hc B (∑ i, GammaRVChartPresentation.objectClass (measuredChart (U.underlying.piece i) (U.form i))) = _
  simp only [map_sum, Section3GammaNativeRingMaps.measured_class]
  have hs : ∀ i, measuredClass (nativeMeasured hc (measuredChart (U.underlying.piece i) (U.form i))) =
      measuredClass (gammaGroundMeasuredGammaSingleForm (U.underlying.piece i) (U.form i)) :=
    fun i => measured_iso (Section3GammaRoundtripBridge.measured_native_chart _ _)
  simp only [hs]
  have h := congrArg (of : GammaGroundMeasuredGammaPositiveSemiring hc B → GammaGroundMeasuredGammaGrothendieckRing hc B)
    (gammaGroundMeasuredGammaSemiringClass_finite_pieces U.underlying.tags U.underlying.piece U.form)
  simpa only [map_sum, measuredClass, gammaGroundMeasuredGammaSingleForm] using h.symm

def ordinary : GammaOrdinaryRing.Ring B ≃+* GammaGroundGammaGrothendieckRing hc B :=
  RingEquiv.ofBijective (Section3GammaNativeRingMaps.ordinary hc B) ⟨(by
    intro x y h
    have hh := congrArg (Section3GammaChartAddMaps.ordinary hc B) h
    exact (DFunLike.congr_fun (ordinary_chart_native hc B) x).symm.trans
      (hh.trans (DFunLike.congr_fun (ordinary_chart_native hc B) y))), (by
    intro y
    exact ⟨Section3GammaChartAddMaps.ordinary hc B y, DFunLike.congr_fun (ordinary_native_chart hc B) y⟩)⟩

def measured : GammaRVChartPresentation.ChartRing B ≃+* GammaGroundMeasuredGammaGrothendieckRing hc B :=
  RingEquiv.ofBijective (Section3GammaNativeRingMaps.measured hc B) ⟨(by
    intro x y h
    have hh := congrArg (Section3GammaChartAddMaps.measured hc B) h
    exact (DFunLike.congr_fun (measured_chart_native hc B) x).symm.trans
      (hh.trans (DFunLike.congr_fun (measured_chart_native hc B) y))), (by
    intro y
    exact ⟨Section3GammaChartAddMaps.measured hc B y, DFunLike.congr_fun (measured_native_chart hc B) y⟩)⟩

theorem ordinary_class {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) : ordinary hc B (GammaOrdinaryRing.objectClass a) = ordinaryClass (nativeOrdinary hc a) :=
  Section3GammaNativeRingMaps.ordinary_class hc B a
theorem measured_class {n : ℕ} (a : GammaWeightedCharts.Chart B n) : measured hc B (GammaRVChartPresentation.objectClass a) = measuredClass (nativeMeasured hc a) :=
  Section3GammaNativeRingMaps.measured_class hc B a

theorem ordinary_symm_class {n : ℕ} (U : GammaGroundGammaObject hc B n) :
    (ordinary hc B).symm (ordinaryClass U) = ordinaryValue U := by
  have h := DFunLike.congr_fun (ordinary_native_chart hc B) (ordinaryClass U)
  rw [AddMonoidHom.comp_apply, ordinary_add_class] at h
  exact (ordinary hc B).injective (by rw [RingEquiv.apply_symm_apply]; exact h.symm)
theorem measured_symm_class {n : ℕ} (U : GammaGroundMeasuredGammaObject hc B n) :
    (measured hc B).symm (measuredClass U) = measuredValue U := by
  have h := DFunLike.congr_fun (measured_native_chart hc B) (measuredClass U)
  rw [AddMonoidHom.comp_apply, measured_add_class] at h
  exact (measured hc B).injective (by rw [RingEquiv.apply_symm_apply]; exact h.symm)

end DiamondIntegral.Section4.Section3GammaRingEquivalences
