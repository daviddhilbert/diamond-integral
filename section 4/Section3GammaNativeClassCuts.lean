import «section 4».Section3GammaNativeIsomorphisms
import «section 4».GammaOrdinaryRing
import «section 3».MeasuredNativeGammaPartitions

/-! Actual native Gamma classes respect chart scissors. Measured
relations keep one common full weight and the original base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3GammaNativeClassCuts
open Section3GammaCodeBridge Section3GammaChartBridge GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def ordinaryClass {n : ℕ} (U : GammaGroundGammaObject hc B n) : GammaGroundGammaGrothendieckRing hc B :=
  of (gammaGroundGammaSemiringClass U)
def measuredClass {n : ℕ} (U : GammaGroundMeasuredGammaObject hc B n) : GammaGroundMeasuredGammaGrothendieckRing hc B :=
  of (gammaGroundMeasuredGammaSemiringClass U)

theorem ordinary_iso {n : ℕ} {U V : GammaGroundGammaObject hc B n} (f : GammaGroundGammaHom U V) : ordinaryClass U = ordinaryClass V :=
  congrArg of (gammaGroundGammaSemiringClass_iso (asIso (show U ⟶ V from f)))
theorem measured_iso {n : ℕ} {U V : GammaGroundMeasuredGammaObject hc B n} (f : GammaGroundMeasuredGammaHom U V) : measuredClass U = measuredClass V :=
  congrArg of (gammaGroundMeasuredGammaSemiringClass_iso (asIso (show U ⟶ V from f)))

theorem valuation_scissor {n : ℕ} {R : Type*} [CommRing R] (v : GammaGroundGammaPiece hc B n → R)
    (hp : ∀ G A D : GammaGroundGammaPiece hc B n, A.carrier ⊆ G.carrier → D.carrier ⊆ G.carrier →
      Disjoint A.carrier D.carrier → (A.union D).carrier = G.carrier → v G = v A + v D)
    (A D U E : GammaGroundGammaPiece hc B n)
    (hU : U.carrier = A.carrier ∪ D.carrier) (hE : E.carrier = A.carrier ∩ D.carrier) :
    v U + v E = v A + v D := by
  let X := D.sdiff A
  have hA : A.carrier ⊆ U.carrier := by rw [hU]; exact Set.subset_union_left
  have hX : X.carrier ⊆ U.carrier := by intro x hx; rw [hU]; exact Or.inr hx.1
  have hd1 : Disjoint A.carrier X.carrier := Set.disjoint_left.mpr (fun _ ha hx => hx.2 ha)
  have hu1 : (A.union X).carrier = U.carrier := by
    ext x
    rw [hU]
    change (x ∈ A.carrier ∨ x ∈ D.carrier ∧ x ∉ A.carrier) ↔ x ∈ A.carrier ∨ x ∈ D.carrier
    tauto
  have hED : E.carrier ⊆ D.carrier := by rw [hE]; exact Set.inter_subset_right
  have hXD : X.carrier ⊆ D.carrier := fun _ hx => hx.1
  have hd2 : Disjoint E.carrier X.carrier := Set.disjoint_left.mpr (fun x he hx => hx.2 ((Set.ext_iff.mp hE x).mp he).1)
  have hu2 : (E.union X).carrier = D.carrier := by
    ext x
    change (x ∈ E.carrier ∨ x ∈ D.carrier ∧ x ∉ A.carrier) ↔ x ∈ D.carrier
    rw [hE]
    change (x ∈ A.carrier ∧ x ∈ D.carrier ∨ x ∈ D.carrier ∧ x ∉ A.carrier) ↔ x ∈ D.carrier
    tauto
  rw [hp U A X hA hX hd1 hu1, hp D E X hED hXD hd2 hu2]
  abel

theorem ordinary_partition {n : ℕ} (G A D : GammaGroundGammaPiece hc B n)
    (hA : A.carrier ⊆ G.carrier) (hD : D.carrier ⊆ G.carrier) (hd : Disjoint A.carrier D.carrier)
    (hu : (A.union D).carrier = G.carrier) : ordinaryClass (GammaGroundGammaObject.single G) =
      ordinaryClass (GammaGroundGammaObject.single A) + ordinaryClass (GammaGroundGammaObject.single D) := by
  have h := congrArg (of : GammaGroundGammaPositiveSemiring hc B → GammaGroundGammaGrothendieckRing hc B)
    (gammaGroundGammaSemiringClass_native_partition G A D hA hD hd hu)
  simpa only [ordinaryClass, map_add] using h

theorem ordinary_scissor {n : ℕ} (a b c d : GammaOrdinaryCharts.Chart B n) (h : GammaOrdinaryRing.Scissor a b c d) :
    ordinaryClass (nativeOrdinary hc c) + ordinaryClass (nativeOrdinary hc d) =
      ordinaryClass (nativeOrdinary hc a) + ordinaryClass (nativeOrdinary hc b) :=
  valuation_scissor (fun G => ordinaryClass (GammaGroundGammaObject.single G)) ordinary_partition
    (native hc a.support a.support_definable) (native hc b.support b.support_definable)
    (native hc c.support c.support_definable) (native hc d.support d.support_definable) h.1 h.2

def combinedFunction {n : ℕ} (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (γ : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) := μ γ * ∏ i, γ i
theorem combinedFunction_definable {n : ℕ} (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : MapDefinable B μ) : FullGammaFunction (integrationGammaBase B) (combinedFunction μ) :=
  ((function_iff μ).mpr hμ).mul (FullGammaFunction.prod Finset.univ (fun i γ => γ i) (fun i _ => FullGammaFunction.proj _ i))

theorem measured_ofTotal {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    measuredClass (nativeMeasured hc (GammaChartOperations.ofTotal B n I hI μ hμ)) =
      measuredClass (gammaGroundMeasuredGammaSingleWeight (native hc I hI) (combinedFunction μ) (combinedFunction_definable μ hμ)) := by
  apply measured_iso
  refine ⟨GammaGroundGammaHom.id (GammaGroundGammaObject.single (native hc I hI)), ?_⟩
  intro u
  rw [nativeMeasured_weight, gammaGroundMeasuredGammaSingleWeight_combined]
  rfl

theorem measured_partition {n : ℕ} (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) (G A D : GammaGroundGammaPiece hc B n)
    (hA : A.carrier ⊆ G.carrier) (hD : D.carrier ⊆ G.carrier) (hd : Disjoint A.carrier D.carrier)
    (hu : (A.union D).carrier = G.carrier) :
    measuredClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      measuredClass (gammaGroundMeasuredGammaSingleWeight A f hf) + measuredClass (gammaGroundMeasuredGammaSingleWeight D f hf) := by
  have h := congrArg (of : GammaGroundMeasuredGammaPositiveSemiring hc B → GammaGroundMeasuredGammaGrothendieckRing hc B)
    (gammaGroundMeasuredGammaSemiringClass_native_partition G A D hA hD hd hu f hf)
  simpa only [measuredClass, map_add] using h

theorem measured_scissor (n : ℕ) (I J : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaDefinable B I) (hJ : GammaDefinable B J) (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    measuredClass (nativeMeasured hc (GammaChartOperations.ofTotal B n (I ∪ J) hU μ hμ)) +
      measuredClass (nativeMeasured hc (GammaChartOperations.ofTotal B n (I ∩ J) hN μ hμ)) =
        measuredClass (nativeMeasured hc (GammaChartOperations.ofTotal B n I hI μ hμ)) +
          measuredClass (nativeMeasured hc (GammaChartOperations.ofTotal B n J hJ μ hμ)) := by
  rw [measured_ofTotal, measured_ofTotal, measured_ofTotal, measured_ofTotal]
  exact valuation_scissor (fun G => measuredClass (gammaGroundMeasuredGammaSingleWeight G
    (combinedFunction μ) (combinedFunction_definable μ hμ)))
      (measured_partition (combinedFunction μ) (combinedFunction_definable μ hμ))
      (native hc I hI) (native hc J hJ) (native hc (I ∪ J) hU) (native hc (I ∩ J) hN) rfl rfl

theorem ordinary_empty {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) (ha : a.support = ∅) :
    ordinaryClass (nativeOrdinary hc a) = 0 := by
  have he : native hc a.support a.support_definable = GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) :=
    gammaGroundDefSet_eq_of_carrier_eq ha
  change ordinaryClass (GammaGroundGammaObject.single (native hc a.support a.support_definable)) = 0
  rw [he]
  simpa only [ordinaryClass, map_zero] using congrArg
    (of : GammaGroundGammaPositiveSemiring hc B → GammaGroundGammaGrothendieckRing hc B)
      (gammaGroundGammaSemiringClass_single_empty (hc := hc) (B := B) (n := n))

theorem measured_empty (n : ℕ) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : MapDefinable B μ) :
    measuredClass (nativeMeasured hc (GammaChartOperations.ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ)) = 0 := by
  rw [measured_ofTotal]
  have he : native hc (∅ : Set (Fin n → Values.Gamma (M := M))) (GammaIntegerFamilies.empty_definable_base B n) =
      GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) :=
    gammaGroundDefSet_eq_of_carrier_eq rfl
  rw [he]
  have h := congrArg (of : GammaGroundMeasuredGammaPositiveSemiring hc B → GammaGroundMeasuredGammaGrothendieckRing hc B)
    (gammaGroundMeasuredGammaSemiringClass_single_empty (hc := hc) (B := B) (combinedFunction μ) (combinedFunction_definable μ hμ))
  simpa only [measuredClass, map_zero] using h

end DiamondIntegral.Section4.Section3GammaNativeClassCuts
