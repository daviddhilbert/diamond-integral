import «section 5».RVRectanglePieceExistence
import «section 5».RVRectangleDecompositionSchemata
import «section 5».RVRawDomainPartitions

/-! Complete finite original RV rectangle packages exist at every mixed
parameter, including empty rows and raw zero-coordinate domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}

theorem rv_rectangle_decomposition_schema_at_parameter
    (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (D : GammaDomainFormula B p a sp) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    ∃ W : RVRectangleDecompositionSchema D, W.Valid hc z := by
  let X := originalRVRowDomain hc D z
  obtain ⟨N,C,hd,hcov⟩ := raw_rv_rectangle_decomposition (hc := hc) (B := ⟨B.real ∪ Set.range z,B.gamma⟩) h00 hκ hs
    (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) X
  choose F hF hrow using (fun i => rv_rectangle_piece_schema_at_parameter hc h00 hκ hs B hr hγ sp z hz (C i))
  let W : RVRectangleDecompositionSchema D := ⟨N,F⟩
  have hp := rawDomain_finite_partition X (fun i => (C i).source) hd hcov
  refine ⟨W,hz,hF,?_,?_⟩
  · intro v
    exact (Set.ext_iff.mp (originalRVRowDomain_raw D z) v).symm.trans
      ((hp.2 v).trans (exists_congr (fun i => (Set.ext_iff.mp (hrow i) v).symm)))
  · intro i j hij v hv
    exact Set.disjoint_left.mp (hp.1 i j hij)
      ((Set.ext_iff.mp (hrow i) v).mp hv.1) ((Set.ext_iff.mp (hrow j) v).mp hv.2)

end DiamondIntegral.Section5
