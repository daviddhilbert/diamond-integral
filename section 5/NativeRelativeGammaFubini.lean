import «section 5».NativeEulerCertificateFubini
import «section 5».RVGammaEulerCatalogPartitions

/-! General relative Gamma Fubini in the actual native RES reduction.
The finite weighted partition uses the actual fibre Euler integers over
the exact original RV parameter base. -/
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

theorem native_relative_gamma_fubini_partition
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (hproj : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ X.carrier) :
    ∃ N : ℕ, ∃ A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p), ∃ c : Fin N → ℤ,
      (∀ i, (A i).carrier ⊆ X.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) ∧
      (∀ i (x : A i), rvGammaFibreEulerValue hc h00 hκ hs hr hγ T x.val kind = c i) ∧
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rvGammaFamilyLift T) =
        nativeTorusClass B ^ n * ∑ i : Fin N, (c i : RESDimensionFreeReduction.Ring B) *
          nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) := by
  obtain ⟨N,A,C,hsub,hd,hcov,hvalid⟩ := rv_gamma_euler_certificate_partition h00 hκ hs hr hγ X T
  let c : Fin N → ℤ := fun i => ((C i).syntax hc).eulerValue kind
  refine ⟨N,A,c,hsub,hd,hcov,?_,?_⟩
  · intro i x
    exact (C i).originalGammaRowEulerValue hc h00 hκ hs hr hγ (rvGammaFamilySchema T)
      (rvUnitValues x.val) (hvalid i x) kind
  · have hl := rvGammaFamilyLift_restrict_partition X T hproj A hd hcov
    rw [nativeUnitRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
      (rvGammaFamilyLift T) (fun i => rvGammaFamilyLift (rvGammaFamilyRestrict T (A i))) hl.1 hl.2]
    have he (i : Fin N) :
        nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rvGammaFamilyLift (rvGammaFamilyRestrict T (A i))) =
          (c i : RESDimensionFreeReduction.Ring B) * nativeTorusClass B ^ n *
            nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) := by
      apply native_euler_certificate_fubini h00 linear hκ hs hr hγ hΓ kind (A i)
        (rvGammaFamilyRestrict T (A i)) (fun _ _ h => h.2) (C i)
      intro x
      exact ((C i).validFor_source_congr (rvGammaFamilySchema T)
        (rvGammaFamilySchema (rvGammaFamilyRestrict T (A i))) (rvUnitValues x.val)
        (rvGammaFamilySchema_restrict_row T (A i) x)).mp (hvalid i x)
    simp_rw [he]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

end DiamondIntegral.Section5
