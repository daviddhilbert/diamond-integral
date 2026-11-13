import «section 4».FinitePieceValuations

/-! Finite Gamma chart relations hold in the actual finite completions.
Only the proved positive inclusions are used to transport elementary
partitions; no injectivity after group completion is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3FiniteGammaNativeClasses
open Section3FiniteGammaChartBridge Section3GammaCodeBridge FinitePieceValuations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def single {n : ℕ} (G : Piece hc B n) : GammaGroundFiniteGammaObject hc B n :=
  ⟨GammaGroundGammaObject.single G.val, fun _ => G.property⟩
def singleWeight {n : ℕ} (G : Piece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) : GammaGroundMeasuredFiniteGammaObject hc B n :=
  ⟨gammaGroundMeasuredGammaSingleWeight G.val f hf, fun _ => G.property⟩

theorem ordinary_partition {n : ℕ} (G A D : Piece hc B n)
    (hA : A.val.carrier ⊆ G.val.carrier) (hD : D.val.carrier ⊆ G.val.carrier)
    (hd : Disjoint A.val.carrier D.val.carrier) (hu : (A.val.union D.val).carrier = G.val.carrier) :
    ordinaryClass (single G) = ordinaryClass (single A) + ordinaryClass (single D) := by
  have h : gammaGroundFiniteGammaSemiringClass (single G) =
      gammaGroundFiniteGammaSemiringClass (single A) + gammaGroundFiniteGammaSemiringClass (single D) := by
    apply gammaGroundFiniteGammaToGammaSemiring_injective (hc := hc) (ground := B)
    rw [(gammaGroundFiniteGammaToGammaSemiring (hc := hc) (ground := B)).map_add,
      gammaGroundFiniteGammaToGammaSemiring_class, gammaGroundFiniteGammaToGammaSemiring_class,
      gammaGroundFiniteGammaToGammaSemiring_class]
    exact gammaGroundGammaSemiringClass_native_partition G.val A.val D.val hA hD hd hu
  simpa only [ordinaryClass, map_add] using congrArg of h

theorem measured_partition {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) (G A D : Piece hc B n)
    (hA : A.val.carrier ⊆ G.val.carrier) (hD : D.val.carrier ⊆ G.val.carrier)
    (hd : Disjoint A.val.carrier D.val.carrier) (hu : (A.val.union D.val).carrier = G.val.carrier) :
    measuredClass (singleWeight G f hf) = measuredClass (singleWeight A f hf) + measuredClass (singleWeight D f hf) := by
  have h : gammaGroundMeasuredFiniteGammaSemiringClass (singleWeight G f hf) =
      gammaGroundMeasuredFiniteGammaSemiringClass (singleWeight A f hf) + gammaGroundMeasuredFiniteGammaSemiringClass (singleWeight D f hf) := by
    apply gammaGroundMeasuredFiniteGammaToGammaSemiring_injective (hc := hc) (ground := B)
    rw [(gammaGroundMeasuredFiniteGammaToGammaSemiring (hc := hc) (ground := B)).map_add,
      gammaGroundMeasuredFiniteGammaToGammaSemiring_class, gammaGroundMeasuredFiniteGammaToGammaSemiring_class,
      gammaGroundMeasuredFiniteGammaToGammaSemiring_class]
    exact gammaGroundMeasuredGammaSemiringClass_native_partition G.val A.val D.val hA hD hd hu f hf
  simpa only [measuredClass, map_add] using congrArg of h

theorem ordinary_scissor {n : ℕ} (a b c d : GammaOrdinaryCharts.FiniteChart B n)
    (h : GammaOrdinaryFiniteRing.Scissor a b c d) :
    ordinaryClass (nativeOrdinary hc c) + ordinaryClass (nativeOrdinary hc d) =
      ordinaryClass (nativeOrdinary hc a) + ordinaryClass (nativeOrdinary hc b) :=
  FinitePieceValuations.scissor (fun G => ordinaryClass (single G)) ordinary_partition
    ⟨native hc a.support a.support_definable, a.finite_support⟩ ⟨native hc b.support b.support_definable, b.finite_support⟩
    ⟨native hc c.support c.support_definable, c.finite_support⟩ ⟨native hc d.support d.support_definable, d.finite_support⟩ h.1 h.2

theorem measured_ofTotal {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaOrderLogic.GammaDefinable B I) (hi : I.Finite)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : GammaDefinableMaps.MapDefinable B μ) :
    measuredClass (nativeMeasured hc (GammaFiniteRVCharts.ofTotal B n I hI hi μ hμ)) =
      measuredClass (singleWeight ⟨native hc I hI, hi⟩ (Section3GammaNativeClassCuts.combinedFunction μ)
        (Section3GammaNativeClassCuts.combinedFunction_definable μ hμ)) := by
  apply measured_iso
  refine ⟨GammaGroundGammaHom.id (GammaGroundGammaObject.single (native hc I hI)), ?_⟩
  intro u
  change (Section3GammaChartBridge.nativeMeasured hc (GammaChartOperations.ofTotal B n I hI μ hμ)).combinedWeight u =
    (gammaGroundMeasuredGammaSingleWeight (native hc I hI) (Section3GammaNativeClassCuts.combinedFunction μ)
      (Section3GammaNativeClassCuts.combinedFunction_definable μ hμ)).combinedWeight u
  rw [Section3GammaChartBridge.nativeMeasured_weight, gammaGroundMeasuredGammaSingleWeight_combined]
  rfl

theorem measured_scissor (n : ℕ) (I J : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaOrderLogic.GammaDefinable B I) (hJ : GammaOrderLogic.GammaDefinable B J) (hi : I.Finite) (hj : J.Finite)
    (hU : GammaOrderLogic.GammaDefinable B (I ∪ J)) (hN : GammaOrderLogic.GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : GammaDefinableMaps.MapDefinable B μ) :
    measuredClass (nativeMeasured hc (GammaFiniteRVCharts.ofTotal B n (I ∪ J) hU (hi.union hj) μ hμ)) +
      measuredClass (nativeMeasured hc (GammaFiniteRVCharts.ofTotal B n (I ∩ J) hN (hi.subset Set.inter_subset_left) μ hμ)) =
        measuredClass (nativeMeasured hc (GammaFiniteRVCharts.ofTotal B n I hI hi μ hμ)) +
          measuredClass (nativeMeasured hc (GammaFiniteRVCharts.ofTotal B n J hJ hj μ hμ)) := by
  rw [measured_ofTotal, measured_ofTotal, measured_ofTotal, measured_ofTotal]
  exact FinitePieceValuations.scissor (fun G => measuredClass (singleWeight G
    (Section3GammaNativeClassCuts.combinedFunction μ) (Section3GammaNativeClassCuts.combinedFunction_definable μ hμ)))
    (measured_partition _ _) ⟨native hc I hI, hi⟩ ⟨native hc J hJ, hj⟩
      ⟨native hc (I ∪ J) hU, hi.union hj⟩ ⟨native hc (I ∩ J) hN, hi.subset Set.inter_subset_left⟩ rfl rfl

theorem ordinary_empty {n : ℕ} (a : GammaOrdinaryCharts.FiniteChart B n) (ha : a.support = ∅) :
    ordinaryClass (nativeOrdinary hc a) = 0 := by
  have h : gammaGroundFiniteGammaSemiringClass (nativeOrdinary hc a) = 0 := by
    apply gammaGroundFiniteGammaToGammaSemiring_injective
    rw [gammaGroundFiniteGammaToGammaSemiring_class, map_zero]
    have he : native hc a.support a.support_definable = GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) :=
      gammaGroundDefSet_eq_of_carrier_eq ha
    change gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (native hc a.support a.support_definable)) = 0
    rw [he, gammaGroundGammaSemiringClass_single_empty]
  simpa only [ordinaryClass, map_zero] using congrArg of h

theorem measured_empty (n : ℕ)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : GammaDefinableMaps.MapDefinable B μ) :
    measuredClass (nativeMeasured hc (GammaFiniteRVCharts.ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) Set.finite_empty μ hμ)) = 0 := by
  rw [measured_ofTotal]
  have he : native hc (∅ : Set (Fin n → Values.Gamma (M := M))) (GammaIntegerFamilies.empty_definable_base B n) =
      GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) := gammaGroundDefSet_eq_of_carrier_eq rfl
  have h : gammaGroundMeasuredFiniteGammaSemiringClass (singleWeight ⟨native hc ∅ (GammaIntegerFamilies.empty_definable_base B n), Set.finite_empty⟩
      (Section3GammaNativeClassCuts.combinedFunction μ) (Section3GammaNativeClassCuts.combinedFunction_definable μ hμ)) = 0 := by
    apply gammaGroundMeasuredFiniteGammaToGammaSemiring_injective
    rw [gammaGroundMeasuredFiniteGammaToGammaSemiring_class, map_zero]
    change gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight
      (native hc ∅ (GammaIntegerFamilies.empty_definable_base B n))
      (Section3GammaNativeClassCuts.combinedFunction μ) (Section3GammaNativeClassCuts.combinedFunction_definable μ hμ)) = 0
    rw [he, gammaGroundMeasuredGammaSemiringClass_single_empty]
  simpa only [measuredClass, map_zero] using congrArg of h

end DiamondIntegral.Section4.Section3FiniteGammaNativeClasses
