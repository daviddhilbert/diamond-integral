import «section 5».RESLayoutExistence
import IntegrationSection6.GammaWitnessUniformity

/-! Literal ideal terms retain their coefficient occurrences, orientation,
old native domains and original-base formal relation certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 RESFiniteWitness
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}




theorem res_native_equality_iff_valid_layout
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (hF : F.Valid hc z) (hG : G.Valid hc z) :
    nativeRESChartClass (F.chart hc z hF) = nativeRESChartClass (G.chart hc z hG) ↔
      ∃ W : RESLayoutStabilizationSchema F G, W.Valid hc z := by
  constructor
  · exact res_layout_schema_exists_of_native_equality B sp z hz F G hF hG
  · rintro ⟨W, hW⟩
    exact W.native_equality hc z hW

theorem res_equality_finite_layout_catalog
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (hF : ∀ z ∈ A, F.Valid hc z) (hG : ∀ z ∈ A, G.Valid hc z)
    (he : ∀ z, ∀ hz : z ∈ A,
      nativeRESChartClass (F.chart hc z (hF z hz)) = nativeRESChartClass (G.chart hc z (hG z hz))) :
    ∃ J : Finset (RESLayoutStabilizationSchema F G),
      ∀ z ∈ A, ∃ W ∈ J, W.Valid hc z := by
  exact gamma_finite_witnesses hκ hs hr hγ sp A hA
    (fun W : RESLayoutStabilizationSchema F G => {z | W.Valid hc z})
    (fun W => W.valid_definable hc) (by
      intro z hz
      exact res_layout_schema_exists_of_native_equality B sp z (hA.proper z hz) F G (hF z hz) (hG z hz) (he z hz))

end DiamondIntegral.Section5
