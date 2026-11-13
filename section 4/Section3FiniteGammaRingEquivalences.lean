import «section 4».Section3FiniteGammaNativeRingMaps
import «section 4».Section3FiniteGammaChartAddMaps
import «section 4».ObjectClassAdditiveGeneration
import «section 3».CompletionDirectSum
import «section 3».GammaPieceSums
import «section 3».MeasuredGammaPieceSums

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

namespace DiamondIntegral.Section4.Section3FiniteGammaRingEquivalences
open Section3FiniteGammaChartBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

theorem ordinary_add_class {n : ℕ} (U : GammaGroundFiniteGammaObject hc B n) :
    Section3FiniteGammaChartAddMaps.ordinary hc B (ordinaryClass U) = ordinaryValue U :=
  Section3FiniteGammaChartAddMaps.ordinary_class hc B U
theorem measured_add_class {n : ℕ} (U : GammaGroundMeasuredFiniteGammaObject hc B n) :
    Section3FiniteGammaChartAddMaps.measured hc B (measuredClass U) = measuredValue U :=
  Section3FiniteGammaChartAddMaps.measured_class hc B U

def ordinaryPresentation : ObjectClassAdditiveGeneration.Presentation (GammaOrdinaryFiniteRing.Generator B) (GammaOrdinaryFiniteRing.Ring B) where
  objectClass a := GammaOrdinaryFiniteRing.objectClass a.2
  unit := ⟨0, GammaOrdinaryFiniteCharts.unit B⟩
  class_unit := GammaOrdinaryFiniteRing.class_unit B
  product a b := ⟨b.1 + a.1, GammaOrdinaryFiniteCharts.product a.2 b.2⟩
  class_product a b := GammaOrdinaryFiniteRing.class_product a.2 b.2
  free := Ideal.Quotient.mk (GammaOrdinaryFiniteRing.relationIdeal B)
  free_of _ := rfl
  surjective := Ideal.Quotient.mk_surjective

def measuredPresentation : ObjectClassAdditiveGeneration.Presentation (GammaFiniteRVPresentation.Generator B) (GammaFiniteRVPresentation.ChartRing B) where
  objectClass a := GammaFiniteRVPresentation.objectClass a.2
  unit := ⟨0, GammaFiniteRVCharts.unit B⟩
  class_unit := GammaFiniteRVPresentation.class_unit B
  product a b := ⟨b.1 + a.1, GammaFiniteRVCharts.product a.2 b.2⟩
  class_product a b := GammaFiniteRVPresentation.class_product a.2 b.2
  free := Ideal.Quotient.mk (GammaFiniteRVPresentation.relationIdeal B)
  free_of _ := rfl
  surjective := Ideal.Quotient.mk_surjective

theorem ordinary_toDirectSum_class {n : ℕ} (U : GammaGroundFiniteGammaObject hc B n) :
    ringCompletionCongr (gammaGroundFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := B)) (ordinaryClass U) =
      of (gammaGroundFiniteGammaDirectSumClass U) := by
  rw [ordinaryClass, ringCompletionCongr_of]
  exact congrArg of (gammaGroundFiniteGammaPresentationToDirectSum_class U)

theorem measured_toDirectSum_class {n : ℕ} (U : GammaGroundMeasuredFiniteGammaObject hc B n) :
    ringCompletionCongr (gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := B)) (measuredClass U) =
      of (gammaGroundMeasuredFiniteGammaDirectSumClass U) := by
  rw [measuredClass, ringCompletionCongr_of]
  exact congrArg of (gammaGroundMeasuredFiniteGammaPresentationToDirectSum_class U)

theorem ordinary_addHom_ext {G : Type*} [AddCommGroup G]
    (f g : GammaGroundFiniteGammaGrothendieckRing hc B →+ G)
    (h : ∀ n (U : GammaGroundFiniteGammaObject hc B n), f (ordinaryClass U) = g (ordinaryClass U)) : f = g := by
  let E := ringCompletionCongr (gammaGroundFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := B))
  have hh : f.comp E.symm.toAddEquiv.toAddMonoidHom = g.comp E.symm.toAddEquiv.toAddMonoidHom := by
    apply completionAddHom_ext
    have hd : ((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) =
        ((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) := by
      apply DirectSum.addHom_ext
      intro n
      have hp : (((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundFiniteGammaKPlus hc B) n)) =
          (((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundFiniteGammaKPlus hc B) n)) := by
        apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundFiniteGammaPresentation hc B n)
        intro U
        change f (E.symm (of (gammaGroundFiniteGammaDirectSumClass U))) = g (E.symm (of (gammaGroundFiniteGammaDirectSumClass U)))
        rw [← ordinary_toDirectSum_class hc B U, RingEquiv.symm_apply_apply]
        exact h n U
      exact DFunLike.congr_fun hp
    exact DFunLike.congr_fun hd
  exact AddMonoidHom.ext (fun x => by
    have hx := DFunLike.congr_fun hh (E x)
    change f (E.symm (E x)) = g (E.symm (E x)) at hx
    simpa only [RingEquiv.symm_apply_apply] using hx)

theorem measured_addHom_ext {G : Type*} [AddCommGroup G]
    (f g : GammaGroundMeasuredFiniteGammaGrothendieckRing hc B →+ G)
    (h : ∀ n (U : GammaGroundMeasuredFiniteGammaObject hc B n), f (measuredClass U) = g (measuredClass U)) : f = g := by
  let E := ringCompletionCongr (gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := B))
  have hh : f.comp E.symm.toAddEquiv.toAddMonoidHom = g.comp E.symm.toAddEquiv.toAddMonoidHom := by
    apply completionAddHom_ext
    have hd : ((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) =
        ((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of) := by
      apply DirectSum.addHom_ext
      intro n
      have hp : (((f.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc B) n)) =
          (((g.comp E.symm.toAddEquiv.toAddMonoidHom).comp of).comp (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc B) n)) := by
        apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundMeasuredFiniteGammaPresentation hc B n)
        intro U
        change f (E.symm (of (gammaGroundMeasuredFiniteGammaDirectSumClass U))) = g (E.symm (of (gammaGroundMeasuredFiniteGammaDirectSumClass U)))
        rw [← measured_toDirectSum_class hc B U, RingEquiv.symm_apply_apply]
        exact h n U
      exact DFunLike.congr_fun hp
    exact DFunLike.congr_fun hd
  exact AddMonoidHom.ext (fun x => by
    have hx := DFunLike.congr_fun hh (E x)
    change f (E.symm (E x)) = g (E.symm (E x)) at hx
    simpa only [RingEquiv.symm_apply_apply] using hx)

theorem ordinary_chart_native :
    (Section3FiniteGammaChartAddMaps.ordinary hc B).comp (Section3FiniteGammaNativeRingMaps.ordinary hc B).toAddMonoidHom = AddMonoidHom.id _ := by
  apply ObjectClassAdditiveGeneration.hom_ext (ordinaryPresentation B)
  rintro ⟨n, a⟩
  change Section3FiniteGammaChartAddMaps.ordinary hc B (Section3FiniteGammaNativeRingMaps.ordinary hc B (GammaOrdinaryFiniteRing.objectClass a)) = GammaOrdinaryFiniteRing.objectClass a
  rw [Section3FiniteGammaNativeRingMaps.ordinary_class, ordinary_add_class]
  change (∑ i : Fin 1, GammaOrdinaryFiniteRing.objectClass (ordinaryFamily (nativeOrdinary hc a) i)) = _
  rw [Fin.sum_univ_one]
  have he : ordinaryFamily (nativeOrdinary hc a) (0 : Fin 1) = a := by cases a; rfl
  rw [he]

theorem measured_chart_native :
    (Section3FiniteGammaChartAddMaps.measured hc B).comp (Section3FiniteGammaNativeRingMaps.measured hc B).toAddMonoidHom = AddMonoidHom.id _ := by
  apply ObjectClassAdditiveGeneration.hom_ext (measuredPresentation B)
  rintro ⟨n, a⟩
  change Section3FiniteGammaChartAddMaps.measured hc B (Section3FiniteGammaNativeRingMaps.measured hc B (GammaFiniteRVPresentation.objectClass a)) = GammaFiniteRVPresentation.objectClass a
  rw [Section3FiniteGammaNativeRingMaps.measured_class, measured_add_class]
  change (∑ i : Fin 1, GammaFiniteRVPresentation.objectClass (measuredFamily (nativeMeasured hc a) i)) = _
  rw [Fin.sum_univ_one]
  exact GammaFiniteRVPresentation.class_iso (Section3GammaRoundtripBridge.measured_chart_native a.toChart)

theorem ordinary_native_chart :
    (Section3FiniteGammaNativeRingMaps.ordinary hc B).toAddMonoidHom.comp (Section3FiniteGammaChartAddMaps.ordinary hc B) = AddMonoidHom.id _ := by
  apply ordinary_addHom_ext hc B
  intro n U
  change Section3FiniteGammaNativeRingMaps.ordinary hc B (Section3FiniteGammaChartAddMaps.ordinary hc B (ordinaryClass U)) = ordinaryClass U
  rw [ordinary_add_class]
  change Section3FiniteGammaNativeRingMaps.ordinary hc B (∑ i, GammaOrdinaryFiniteRing.objectClass (ordinaryFamily U i)) = _
  simp only [map_sum, Section3FiniteGammaNativeRingMaps.ordinary_class]
  have h : gammaGroundFiniteGammaSemiringClass U = ∑ i, gammaGroundFiniteGammaSemiringClass (nativeOrdinary hc (ordinaryFamily U i)) := by
    apply gammaGroundFiniteGammaToGammaSemiring_injective (hc := hc) (ground := B)
    have hmap : gammaGroundFiniteGammaToGammaSemiring (∑ i, gammaGroundFiniteGammaSemiringClass (nativeOrdinary hc (ordinaryFamily U i))) =
        ∑ i, gammaGroundFiniteGammaToGammaSemiring (gammaGroundFiniteGammaSemiringClass (nativeOrdinary hc (ordinaryFamily U i))) :=
      _root_.map_sum (gammaGroundFiniteGammaToGammaSemiring (hc := hc) (ground := B)).toAddMonoidHom _ _
    rw [hmap, gammaGroundFiniteGammaToGammaSemiring_class]
    simp only [gammaGroundFiniteGammaToGammaSemiring_class]
    exact gammaGroundGammaSemiringClass_tag_sum U.obj
  simpa only [map_sum, ordinaryClass] using (congrArg (of : GammaGroundFiniteGammaPositiveSemiring hc B → GammaGroundFiniteGammaGrothendieckRing hc B) h).symm

theorem measured_native_chart :
    (Section3FiniteGammaNativeRingMaps.measured hc B).toAddMonoidHom.comp (Section3FiniteGammaChartAddMaps.measured hc B) = AddMonoidHom.id _ := by
  apply measured_addHom_ext hc B
  intro n U
  change Section3FiniteGammaNativeRingMaps.measured hc B (Section3FiniteGammaChartAddMaps.measured hc B (measuredClass U)) = measuredClass U
  rw [measured_add_class]
  change Section3FiniteGammaNativeRingMaps.measured hc B (∑ i, GammaFiniteRVPresentation.objectClass (measuredFamily U i)) = _
  simp only [map_sum, Section3FiniteGammaNativeRingMaps.measured_class]
  let S (i : Fin U.obj.underlying.tags) : GammaGroundMeasuredFiniteGammaObject hc B n :=
    ⟨gammaGroundMeasuredGammaSingleForm (U.obj.underlying.piece i) (U.obj.form i), fun _ => U.property i⟩
  have hs : ∀ i, measuredClass (nativeMeasured hc (measuredFamily U i)) = measuredClass (S i) :=
    fun i => measured_iso (Section3GammaRoundtripBridge.measured_native_chart _ _)
  simp only [hs]
  have h : gammaGroundMeasuredFiniteGammaSemiringClass U = ∑ i, gammaGroundMeasuredFiniteGammaSemiringClass (S i) := by
    apply gammaGroundMeasuredFiniteGammaToGammaSemiring_injective (hc := hc) (ground := B)
    have hmap : gammaGroundMeasuredFiniteGammaToGammaSemiring (∑ i, gammaGroundMeasuredFiniteGammaSemiringClass (S i)) =
        ∑ i, gammaGroundMeasuredFiniteGammaToGammaSemiring (gammaGroundMeasuredFiniteGammaSemiringClass (S i)) :=
      _root_.map_sum (gammaGroundMeasuredFiniteGammaToGammaSemiring (hc := hc) (ground := B)).toAddMonoidHom _ _
    rw [hmap, gammaGroundMeasuredFiniteGammaToGammaSemiring_class]
    simp only [gammaGroundMeasuredFiniteGammaToGammaSemiring_class]
    exact gammaGroundMeasuredGammaSemiringClass_finite_pieces U.obj.underlying.tags U.obj.underlying.piece U.obj.form
  simpa only [map_sum, measuredClass] using (congrArg (of : GammaGroundMeasuredFiniteGammaPositiveSemiring hc B → GammaGroundMeasuredFiniteGammaGrothendieckRing hc B) h).symm

def ordinary : GammaOrdinaryFiniteRing.Ring B ≃+* GammaGroundFiniteGammaGrothendieckRing hc B :=
  RingEquiv.ofBijective (Section3FiniteGammaNativeRingMaps.ordinary hc B) ⟨(by
    intro x y h
    have hh := congrArg (Section3FiniteGammaChartAddMaps.ordinary hc B) h
    exact (DFunLike.congr_fun (ordinary_chart_native hc B) x).symm.trans
      (hh.trans (DFunLike.congr_fun (ordinary_chart_native hc B) y))), (by
    intro y
    exact ⟨Section3FiniteGammaChartAddMaps.ordinary hc B y, DFunLike.congr_fun (ordinary_native_chart hc B) y⟩)⟩

def measured : GammaFiniteRVPresentation.ChartRing B ≃+* GammaGroundMeasuredFiniteGammaGrothendieckRing hc B :=
  RingEquiv.ofBijective (Section3FiniteGammaNativeRingMaps.measured hc B) ⟨(by
    intro x y h
    have hh := congrArg (Section3FiniteGammaChartAddMaps.measured hc B) h
    exact (DFunLike.congr_fun (measured_chart_native hc B) x).symm.trans
      (hh.trans (DFunLike.congr_fun (measured_chart_native hc B) y))), (by
    intro y
    exact ⟨Section3FiniteGammaChartAddMaps.measured hc B y, DFunLike.congr_fun (measured_native_chart hc B) y⟩)⟩

theorem ordinary_class {n : ℕ} (a : GammaOrdinaryCharts.FiniteChart B n) : ordinary hc B (GammaOrdinaryFiniteRing.objectClass a) = ordinaryClass (nativeOrdinary hc a) :=
  Section3FiniteGammaNativeRingMaps.ordinary_class hc B a
theorem measured_class {n : ℕ} (a : GammaFiniteRVCharts.FiniteChart B n) : measured hc B (GammaFiniteRVPresentation.objectClass a) = measuredClass (nativeMeasured hc a) :=
  Section3FiniteGammaNativeRingMaps.measured_class hc B a

theorem ordinary_symm_class {n : ℕ} (U : GammaGroundFiniteGammaObject hc B n) :
    (ordinary hc B).symm (ordinaryClass U) = ordinaryValue U := by
  have h := DFunLike.congr_fun (ordinary_native_chart hc B) (ordinaryClass U)
  rw [AddMonoidHom.comp_apply, ordinary_add_class] at h
  exact (ordinary hc B).injective (by rw [RingEquiv.apply_symm_apply]; exact h.symm)
theorem measured_symm_class {n : ℕ} (U : GammaGroundMeasuredFiniteGammaObject hc B n) :
    (measured hc B).symm (measuredClass U) = measuredValue U := by
  have h := DFunLike.congr_fun (measured_native_chart hc B) (measuredClass U)
  rw [AddMonoidHom.comp_apply, measured_add_class] at h
  exact (measured hc B).injective (by rw [RingEquiv.apply_symm_apply]; exact h.symm)

end DiamondIntegral.Section4.Section3FiniteGammaRingEquivalences
