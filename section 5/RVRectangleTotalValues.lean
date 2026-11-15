import «section 5».OriginalProductTotalValues
import «section 5».OriginalRVTotalGraphs
import «section 5».RVRectangleTotalPartitions

/-! Whole prepared rectangle packages evaluate actual total RV families.
Their original-base maps and Euler witnesses suffice for the formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}

theorem RVRectanglePieceSchema.total_native_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : RVRectanglePieceSchema B p a (fun _ => .rv))
    (hv : ∀ x : X, F.Valid hc (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X F.source) =
      nativeTorusClass B ^ F.freeArity * ((F.euler.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring B) *
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X F.residue.domain) :=
  (nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (originalRVTotalBijection X F.source F.target F.graph (fun x => (hv x).2.2))).trans
      (original_product_total_value h00 linear hκ hs hr hγ hΓ kind X F.residue.domain F.gamma F.euler
        (fun x => (hv x).2.1))

theorem RVRectangleDecompositionSchema.total_native_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    {D : GammaDomainFormula B p a (fun _ => .rv)} (W : RVRectangleDecompositionSchema D)
    (hv : ∀ x : X, W.Valid hc (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) =
      ∑ i : Fin W.size, nativeTorusClass B ^ (W.cells i).freeArity *
        (((W.cells i).euler.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring B) *
          nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
            (originalRVTotalFamily X (W.cells i).residue.domain) := by
  have hp := W.total_partition X hv
  have he := nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
    (originalRVTotalFamily X D) (fun i => originalRVTotalFamily X (W.cells i).source) hp.1 hp.2
  exact he.trans (Finset.sum_congr rfl (fun i _ =>
    (W.cells i).total_native_value h00 linear hκ hs hr hγ hΓ kind X (fun x => (hv x).2.1 i)))

end DiamondIntegral.Section5
