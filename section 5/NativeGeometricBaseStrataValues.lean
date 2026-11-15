import «section 5».NativeVFBaseStratumSelection
import «section 5».NativeGeometricLiftValues

/-! A prepared RV-pullback with k nonzero fibre VF coordinates has
geometric value equal to the sum over base zero strata of its raw RV key
value normalized in degree card(I)+k. All old RV coordinates are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M} {p k r : ℕ}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)

theorem nativeVFGeometricValue_base_stratum
    (A : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) (p+k) r))
    (hf : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite)
    (hpull : IsRVPullback A.carrier) (hfib : ∀ a : A,∀ i : Fin k,a.val.1 (Fin.natAdd p i) ≠ 0)
    (I : Finset (Fin p)) :
    nativeVFGeometricValue linear H (nativeVFClass
      ((⟨p+k,r,A,hf⟩ : GammaGroundFiniteVFObject hc G.base).restrict
        (nativeVFSelectedZeroStratum A (Fin.castAdd k) I) (nativeVFSelectedZeroStratum_subset A (Fin.castAdd k) I))) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine G.base)
        (nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
          G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric
          (nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r ∘ Fin.castAdd k) I))
        (Fintype.card I+k) := by
  let AJ := nativeVFSelectedZeroStratum A (Fin.castAdd k) I
  let j := nativeVFBaseStratumSelection I k
  let D := (nativeVFCoordinateSelection AJ j).image
  let e := nativeVFBaseStratumDropBijection A I
  let Ai := (⟨p+k,r,A,hf⟩ : GammaGroundFiniteVFObject hc G.base).restrict AJ
    (nativeVFSelectedZeroStratum_subset A (Fin.castAdd k) I)
  have hfinJ : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ AJ.carrier}.Finite :=
    fun x => (hf x).subset (fun _ hx => nativeVFSelectedZeroStratum_subset A (Fin.castAdd k) I hx)
  have hfinD := (gammaGroundFiniteRVFibres_iff e G.uncountable.le G.saturated G.model00 G.small_real).mp hfinJ
  let Ad : GammaGroundFiniteVFObject hc G.base := ⟨Fintype.card I+k,r,D,hfinD⟩
  have hgeo := nativeVFGeometricValue_nonzero_pullback linear H Ad
    (nativeVFBaseStratumDrop_pullback A hpull I) (nativeVFBaseStratumDrop_nonzero A hfib I)
  have hdrop := nativeFullKeyDropBijection AJ j (nativeVFBaseStratum_omitted_zero A I)
  have hrv := (nativeRVSetValue_bijection G.model00 linear G.uncountable.le G.saturated hc G.base
    G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric _ _ hdrop).symm.trans
      (nativeRVSetValue_bijection G.model00 linear G.uncountable.le G.saturated hc G.base
        G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric _ _
        (GammaGroundBijection.ofCarrierEq (nativeFullKeySelectedZeroStratum_image A (Fin.castAdd k) I)))
  exact (congrArg (nativeVFGeometricValue linear H) (nativeVFClass_bijection Ai Ad e)).trans
    (hgeo.trans (congrArg (fun a => geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine G.base) a
      (Fintype.card I+k)) hrv))

theorem nativeVFGeometricValue_base_strata_sum
    (A : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) (p+k) r))
    (hf : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite)
    (hpull : IsRVPullback A.carrier) (hfib : ∀ a : A,∀ i : Fin k,a.val.1 (Fin.natAdd p i) ≠ 0) :
    nativeVFGeometricValue linear H (nativeVFClass (⟨p+k,r,A,hf⟩ : GammaGroundFiniteVFObject hc G.base)) =
      ∑ I : Finset (Fin p),geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine G.base)
        (nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
          G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric
          (nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r ∘ Fin.castAdd k) I))
        (Fintype.card I+k) := by
  have hpart := nativeVFClass_finite_partition (⟨p+k,r,A,hf⟩ : GammaGroundFiniteVFObject hc G.base)
    (nativeVFSelectedZeroStratum A (Fin.castAdd k))
    (nativeVFSelectedZeroStratum_disjoint A (Fin.castAdd k)) (nativeVFSelectedZeroStratum_cover A (Fin.castAdd k))
  refine ((congrArg (nativeVFGeometricValue linear H) hpart).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl (fun I _ => nativeVFGeometricValue_base_stratum linear H A hf hpull hfib I))

end DiamondIntegral.Section5
