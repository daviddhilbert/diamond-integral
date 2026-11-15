import «section 5».MonomialFunctionTorsors
import «section 5».GammaFunctionMonomialCatalog
import «section 5».GammaFunctionGraphPartitions

/-! A scalar value torsor varying over an arbitrary nonzero RV base has
one residue-torus factor in the actual native ungraded evaluation. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem native_scalar_torsor_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (groundGammaFunctionGraphLift f) =
      nativeTorusClass B * nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  obtain ⟨N, C, hd, hcov⟩ := gamma_function_monomial_catalog hκ hs h00 hr hγ hΓ f
  let A := fun i => (C i).monomial.source
  have hgraphs := groundGammaFunctionGraphLift_finite_partition f A hd hcov
  rw [nativeUnitRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
    (groundGammaFunctionGraphLift f)
    (fun i => groundGammaFunctionGraphLift (f.restrict (fun x hx => (hcov x).mpr ⟨i,hx⟩)))
    hgraphs.1 hgraphs.2]
  calc
    (∑ i : Fin N, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (groundGammaFunctionGraphLift (f.restrict (fun x hx => (hcov x).mpr ⟨i,hx⟩)))) =
      ∑ i : Fin N, nativeTorusClass B * nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (C i).monomial.function_torsor_value h00 linear hκ hs hr hγ hΓ kind
        (f.restrict (C i).source_subset) (C i).graph (C i).graph_functional (C i).row
    _ = nativeTorusClass B * ∑ i : Fin N, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (fun z => nativeTorusClass B * z)
      (nativeUnitRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind X A hd hcov).symm

end DiamondIntegral.Section5
