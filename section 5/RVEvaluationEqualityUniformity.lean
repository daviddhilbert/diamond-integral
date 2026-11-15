import «section 5».RVEvaluationEqualityExistence
import IntegrationSection6.GammaWitnessUniformity

/-! Native row equality has a finite catalog of whole original-base
witnesses, with both rectangle packages and the complete stabilization
graph selected before preparing any VF parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b : ℕ} {sp : Fin p → SortTag}

theorem rv_native_equality_iff_valid_package
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind E z ↔
      ∃ W : RVEvaluationEqualitySchema hc kind D E, W.Valid hc z := by
  constructor
  · exact rv_evaluation_equality_schema_at_parameter h00 linear hκ hs hr hγ hΓ kind D E z hz
  · rintro ⟨W,hW⟩
    exact W.native_equality hc h00 linear hκ hs hr hγ hΓ z hW

theorem rv_equality_finite_package_catalog
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp)
    (he : ∀ z ∈ A, nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind E z) :
    ∃ J : Finset (RVEvaluationEqualitySchema hc kind D E), ∀ z ∈ A, ∃ W ∈ J, W.Valid hc z := by
  exact gamma_finite_witnesses hκ hs hr hγ sp A hA
    (fun W : RVEvaluationEqualitySchema hc kind D E => {z | W.Valid hc z})
    (fun W => W.valid_definable hc) (fun z hz =>
      rv_evaluation_equality_schema_at_parameter h00 linear hκ hs hr hγ hΓ kind D E z (hA.proper z hz) (he z hz))

end DiamondIntegral.Section5
