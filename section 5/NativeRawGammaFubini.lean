import «section 5».NativeRelativeGammaFubini
import «section 5».RawRVGammaEulerConstructibility
import «section 5».RawRVUnitPartitions
import «section 5».NativeRawWeightedValues

/-! Relative Gamma Fubini for all raw RV bases, including zeros. The
actual original-base nonzero coding retains every output representative;
actual fibre Euler integers are computed over the raw parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem native_raw_relative_gamma_fubini_partition
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    ∃ N : ℕ, ∃ A : Fin N → GammaGroundDefSet hc B (rawRVSpace (M := M) p), ∃ c : Fin N → ℤ,
      (∀ i, (A i).carrier ⊆ X.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) ∧
      (∀ i (x : A i), rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x.val kind = c i) ∧
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rawRVGammaLift h00 X T) =
        nativeTorusClass B ^ n * ∑ i : Fin N, (c i : RESDimensionFreeReduction.Ring B) *
          nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) := by
  let e := gammaGroundRVNonzeroTupleCodeBijection h00 X
  obtain ⟨N,A,c,hsub,hd,hcov,hcst,he⟩ := native_relative_gamma_fubini_partition h00 linear hκ hs hr hγ hΓ kind
    (rawRVGammaBaseCode X) (rawRVGammaFamilyCode h00 X T) (rawRVGammaFamilyCode_projection h00 X T)
  have hp := groundBijection_pullback_partition e A hd hcov
  refine ⟨N,(fun i => e.inverseImage (A i)),c,(fun i => e.inverseImage_subset (A i)),hp.1,hp.2,?_,?_⟩
  · intro i x
    let a : X := ⟨x.val,e.inverseImage_subset (A i) x.property⟩
    have hq : (e.map a).val ∈ (A i).carrier := (groundBijection_inverseImage_at e (A i) a).mp x.property
    have hconst := hcst i ⟨(e.map a).val,hq⟩
    exact (rawRVGammaFibreEulerValue_forward_code h00 hκ hs hr hγ X T a kind).symm.trans hconst
  · exact he.trans (congrArg (fun z => nativeTorusClass B ^ n * z) (by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => (c i : RESDimensionFreeReduction.Ring B) * z)
        (nativeRVSetValue_raw_unit_bijection h00 linear hκ hs hr hγ hΓ kind _ _
          (e.restrictTarget (A i) (hsub i))).symm))

theorem native_raw_relative_gamma_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rawRVGammaLift h00 X T) =
      nativeTorusClass B ^ n * nativeRawWeightedValue h00 linear hκ hs hr hγ hΓ kind X
        (fun x => rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x kind)
        (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X T kind).1
        (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X T kind).2 := by
  obtain ⟨N,A,c,hsub,hd,hcov,hcst,he⟩ := native_raw_relative_gamma_fubini_partition
    h00 linear hκ hs hr hγ hΓ kind X T
  have hw := nativeRawWeightedValue_partition h00 linear hκ hs hr hγ hΓ kind X _
    (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X T kind).1
    (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X T kind).2 A c hsub hd hcov hcst
  exact he.trans (congrArg (fun w => nativeTorusClass B ^ n * w) hw.symm)

end DiamondIntegral.Section5
