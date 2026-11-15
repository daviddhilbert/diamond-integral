import «section 5».NativeVFIntegral
import «section 5».NativeZeroStrataValues
import «section 5».NativeVFFinitePartitions

/-! The actual native VF integral of an RV-pullback is computed by its
original-ground RV key. The bounded value sums raw zero strata; the
geometric value normalizes each stratum in its actual nonzero VF degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeVFClass (A : GammaGroundFiniteVFObject hc B) : GammaGroundVFGrothendieckRing hc B :=
  of (gammaGroundVFSemiringClass A)

theorem nativeVFClass_bijection (A D : GammaGroundFiniteVFObject hc B)
    (e : GammaGroundBijection A.domain D.domain) : nativeVFClass A = nativeVFClass D :=
  congrArg of (gammaGroundVFSemiringClass_iso (asIso (show A ⟶ D from e)))

theorem nativeVFClass_finite_partition {ι : Type} [Fintype ι] (A : GammaGroundFiniteVFObject hc B)
    (D : ι → GammaGroundDefSet hc B (rawMixedSpace (M := M) A.vfArity A.rvArity))
    (hd : ∀ i j,i ≠ j → Disjoint (D i).carrier (D j).carrier)
    (hcov : ∀ x,x ∈ A.domain.carrier ↔ ∃ i,x ∈ (D i).carrier) :
    nativeVFClass A = ∑ i,nativeVFClass (A.restrict (D i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  exact (congrArg (of : GammaGroundVFPositiveSemiring hc B → GammaGroundVFGrothendieckRing hc B)
    (nativeVFSemiringClass_finite_partition A D hd hcov)).trans (map_sum _ _ _)

variable {C : GammaGroundContext M} (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput C hc)

theorem nativeVFBoundedValue_of_lift_bijection (A : GammaGroundFiniteVFObject hc C.base)
    {k : ℕ} (U : GammaGroundRVObject hc C.base k) (e : GammaGroundBijection A.domain (gammaGroundObjectLift U)) :
    nativeVFBoundedValue linear H (nativeVFClass A) =
      nativeGroundRVEvaluation C.model00 linear C.uncountable.le C.saturated hc C.base
        C.small_real C.small_gamma C.nontrivial_definable_gamma .bounded (ordinaryClass U) := by
  rw [nativeVFClass_bijection A (gammaGroundObjectLiftFinite U) e]
  exact nativeVFBoundedValue_lift_class linear H U

theorem nativeVFGeometricValue_of_lift_bijection (A : GammaGroundFiniteVFObject hc C.base)
    {k : ℕ} (U : GammaGroundRVObject hc C.base k) (e : GammaGroundBijection A.domain (gammaGroundObjectLift U)) :
    nativeVFGeometricValue linear H (nativeVFClass A) =
      nativeGroundGeometricRetraction C.model00 linear C.uncountable.le C.saturated
        C.small_real C.small_gamma C.nontrivial_definable_gamma (ordinaryClass U) := by
  rw [nativeVFClass_bijection A (gammaGroundObjectLiftFinite U) e]
  exact nativeVFGeometricValue_lift_class linear H U

theorem nativeVFBoundedValue_pullback (A : GammaGroundFiniteVFObject hc C.base)
    (hpull : IsRVPullback A.domain.carrier) :
    nativeVFBoundedValue linear H (nativeVFClass A) =
      nativeRVSetValue C.model00 linear C.uncountable.le C.saturated hc C.base
        C.small_real C.small_gamma C.nontrivial_definable_gamma .bounded (nativeMixedFullKeyMap A.domain).image := by
  rw [nativeVFClass_finite_partition A (nativeVFZeroStratum A.domain)
    (nativeVFZeroStratum_disjoint A.domain) (nativeVFZeroStratum_cover A.domain),map_sum]
  refine (Finset.sum_congr rfl (fun I _ => ?_)).trans
    (nativeVFZeroStrata_raw_value_sum C.model00 linear C.uncountable.le C.saturated
      C.small_real C.small_gamma C.nontrivial_definable_gamma .bounded A.domain hpull A.finite)
  let U := nativeVFZeroStratumRVObject C.uncountable.le C.saturated C.model00 C.small_real
    A.domain hpull A.finite I
  exact (nativeVFBoundedValue_of_lift_bijection linear H _ U
    (nativeVFZeroStratum_lift_bijection C.uncountable.le C.saturated C.model00 C.small_real
      A.domain hpull A.finite I)).trans
    (nativeGroundRVEvaluation_class C.model00 linear C.uncountable.le C.saturated hc C.base
      C.small_real C.small_gamma C.nontrivial_definable_gamma .bounded U)

theorem nativeVFGeometricValue_pullback (A : GammaGroundFiniteVFObject hc C.base)
    (hpull : IsRVPullback A.domain.carrier) :
    nativeVFGeometricValue linear H (nativeVFClass A) =
      ∑ I : Finset (Fin A.vfArity),geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine C.base)
        (nativeRVSetValue C.model00 linear C.uncountable.le C.saturated hc C.base
          C.small_real C.small_gamma C.nontrivial_definable_gamma .geometric
          (nativeRVZeroPatternBase (nativeMixedFullKeyMap A.domain).image (Fin.castAdd A.rvArity) I))
        (Fintype.card I) := by
  rw [nativeVFClass_finite_partition A (nativeVFZeroStratum A.domain)
    (nativeVFZeroStratum_disjoint A.domain) (nativeVFZeroStratum_cover A.domain),map_sum]
  apply Finset.sum_congr rfl
  intro I _
  let U := nativeVFZeroStratumRVObject C.uncountable.le C.saturated C.model00 C.small_real
    A.domain hpull A.finite I
  rw [nativeVFGeometricValue_of_lift_bijection linear H _ U
    (nativeVFZeroStratum_lift_bijection C.uncountable.le C.saturated C.model00 C.small_real
      A.domain hpull A.finite I),nativeGroundGeometricRetraction_class,
    nativeGroundRVEvaluation_class]
  rw [nativeVFZeroStratumRVObject_raw_value]

end DiamondIntegral.Section5
