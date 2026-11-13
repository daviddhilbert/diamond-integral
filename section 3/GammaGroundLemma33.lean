import «section 3».GammaGroundRVFibreComparison
import «section 3».GammaGroundRVFibreInvariance
import Section4.EarlierRVInputs
import «section 3».GammaGroundRVDimensionConsequences
import «section 3».GammaGroundRVFibreDimension
import «section 3».RVFibreDimension
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r : ℕ}

variable {m s : ℕ}
theorem gammaGroundLemma_3_3
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hS : Cardinal.mk ground.real < κ)
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)}
    (f : GammaGroundBijection A B) :
    gammaGroundRVFibreDimension A = gammaGroundRVFibreDimension B := by
  have hne : A.carrier.Nonempty ↔ B.carrier.Nonempty := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨(f.map ⟨a, ha⟩).val, (f.map ⟨a, ha⟩).property⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, _⟩ := f.bijective.surjective ⟨b, hb⟩
      exact ⟨a.val, a.property⟩
  have hd := gammaGroundRVFibreDim_eq_of_bijective
    (rvExchangeInput_of_earlier hκ hs h00) hκ hs
    (gammaRVAlgebraicityInput_of_earlier hκ hs h00) hS f.map f.bijective
  unfold gammaGroundRVFibreDimension
  rw [hne, hd]

theorem gammaGroundRVDimension_ofReal
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hS : Cardinal.mk ground.real < κ)
    {d : ℕ} (A : DefSet (rawRVSpace (M := M) d) ground.real) :
    gammaGroundRVDimension (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A) =
      Section2.rvDimension ground.real A.carrier := by
  by_cases hA : A.carrier.Nonempty
  · have hA' : (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A).carrier.Nonempty := hA
    rw [gammaGroundRVDimension, if_pos hA', gammaGroundRVDim_ofReal
      (rvExchangeInput_of_earlier hκ hs h00) hκ hs
      (gammaRVAlgebraicityInput_of_earlier hκ hs h00) hS]
    exact (rvDimension_eq_companion hc A hA).symm
  · have hA' : ¬ (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A).carrier.Nonempty := hA
    rw [gammaGroundRVDimension, if_neg hA', Set.not_nonempty_iff_eq_empty.mp hA,
      Section2.rvDimension_empty]

end DiamondIntegral.Section3
