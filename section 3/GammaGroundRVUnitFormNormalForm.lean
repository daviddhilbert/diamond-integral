import «section 3».GammaGroundRVValueWeightNormalForm
import «section 3».RVGammaFormValuePartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- The local measured geometric normal form for every actual definable
Gamma-valued weight on a nonzero RV tuple domain. -/
theorem gammaGroundRVUnit_form_normal_form {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (ω : GammaGroundMap A (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (w : (rawRVUnitSpace (M := M) n).Carrier → Values.Gamma (M := M))
    (hω : ∀ a : A, w a.val = (ω a).val) :
    ∃ N : ℕ, ∃ C : Fin N → GammaGroundRVFormProductChart hc B (rawRVUnitSpace (M := M) n) w,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      (∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (C i).source.carrier) := by
  obtain ⟨J,Q,f,hQ,hdis,hcov,hf⟩ :=
    gammaGroundRVUnitGammaForm_value_partition hκ hs h00 hsmall hγsmall A ω
  apply gammaGroundRVFormProductCharts_assemble A Q hdis hcov
  intro j
  obtain ⟨N,C,hCd,hCc⟩ := gammaGroundRVUnit_value_weight_normal_form hκ hs h00 hsmall hγsmall hΓ
    (Q j) (f j).val (f j).property
  have he : ∀ i x, x ∈ (C i).source.carrier → w x = (f j).val (rvUnitTupleValues x) := by
    intro i x hx
    have hq : x ∈ (Q j).carrier := (hCc x).mpr ⟨i,hx⟩
    let a : A := ⟨x,hQ j hq⟩
    exact (hω a).trans (hf j a hq).symm
  exact ⟨N,fun i => (C i).changeWeight w (he i),hCd,hCc⟩
end DiamondIntegral.Section3
