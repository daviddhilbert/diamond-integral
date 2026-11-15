import «section 5».OriginalEulerFamilyPartitions
import «section 5».RVGammaReverseBijections

/-! A complete original-base Euler certificate computes the actual
native value of the whole mixed RV/Gamma family. -/
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

theorem native_euler_certificate_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (hproj : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ X.carrier)
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n)
    (hv : ∀ x : X, C.ValidFor hc (rvGammaFamilySchema T) (rvUnitValues x.val)) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rvGammaFamilyLift T) =
      ((C.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring B) * nativeTorusClass B ^ n *
        nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  have hp := C.family_partition X T hproj hv
  have hl := rvGammaReverseLift_finite_partition T (fun i => (C.cells i).family X) hp.1 hp.2
  have hcvalid (i : Fin C.size) (x : X) :
      (((C.cells i).syntax hc).validity (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
        (nativeGammaRelationSyntax hc).less).Realize (predicateParameterValues B (rvUnitValues x.val)) := by
    have h := hv x
    simp only [OriginalEulerCertificate.ValidFor,EulerFormulaCertificate.validity,
      FirstOrder.Language.Formula.realize_inf,finiteWitnessValidityFormula_realize] at h
    exact h.1 i
  rw [nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _ (rvGammaReverseBijection T).symm,
    nativeUnitRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
      (rvGammaReverseLift T) (fun i => rvGammaReverseLift ((C.cells i).family X)) hl.1 hl.2]
  calc
    (∑ i : Fin C.size, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
      (rvGammaReverseLift ((C.cells i).family X))) =
      ∑ i : Fin C.size, (((C.cells i).syntax hc).shape.eulerValue kind : RESDimensionFreeReduction.Ring B) *
        nativeTorusClass B ^ n * nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
      apply Finset.sum_congr rfl
      intro i _
      exact ((C.cells i).family_is_cell X (hcvalid i)).native_value h00 linear hκ hs hr hγ hΓ kind
    _ = _ := by
      simp only [← Finset.sum_mul,← Int.cast_sum,EulerFormulaCertificate.eulerValue,OriginalEulerCertificate.syntax]

end DiamondIntegral.Section5
