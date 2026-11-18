import «section 3».GammaMeasuredObjectRowElementary
import «section 3».GammaMeasuredSchemaOperationValidity
import IntegrationSection6.GammaAdmissibilityPromotion

/-! Actual admissible measured elementary steps yield valid finite proof
schemata. Slice bounds, elementary presentations, and structural bounds
are supplied by the existing native theorems. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaMeasuredObjectRow.admissibility_bound
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    {z : Fin p → M} {U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ (k+1)}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity (k+1) sp}
    (hF : GammaMeasuredObjectRow z U F) (hValid : F.valid z)
    (i : Fin (k+1)) (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i) :
    ∃ A : ℕ, (GammaFiniteAdmissibilitySchema.mk F.object i A).valid z := by
  obtain ⟨A,hA⟩ := GammaAdmissible.uniform_label_slices (B := ⟨B.real ∪ Set.range z,B.gamma⟩)
    (U := (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject) (i := i)
    hκ hs h00 (small_union_range hκ B.real hr z) hg hAd
  have hImage (r : Fin (k+1) → M) : Fin.append z r ∈ tupleVolumeImage F.object.volume ↔
      r ∈ gammaVolumeImage (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject :=
    (tupleVolumeImage_append_iff F.object.volume z r).trans
      ((exists_congr (fun x => hF.native.2 x r)).trans (gammaRawObjectVolume_image_iff _ r))
  refine ⟨A,hValid.1,?_,?_⟩
  · intro r hr'
    exact hAd.image_nonzero ((hImage r).mp hr')
  · intro t ht
    have he : {r | Fin.append z r ∈ tupleVolumeImage F.object.volume ∧ ∀ j, j ≠ i → r j = t j} =
        {r | r ∈ gammaVolumeImage (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject ∧ ∀ j, j ≠ i → r j = t j} :=
      Set.ext (fun r => and_congr (hImage r) Iff.rfl)
    change _ ∧ _
    rw [he]
    exact hA t ht

theorem gammaMeasured_elementary_formula_witness {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    {z : Fin p → M} {U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ (k+1)}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity (k+1) sp}
    (hF : GammaMeasuredObjectRow z U F) (hValid : F.valid z)
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject (Fin.last k)) :
    ∃ L A : ℕ, (GammaMeasuredRelationSchema.elementary F L A).valid z ∧
      GammaMeasuredObjectRow z
        (gammaMeasuredElementaryObject hκ hs h00 (small_union_range hκ B.real hr z) U (Fin.last k) hAd)
        (F.elementaryFormula.essential.withBound L) := by
  obtain ⟨A,hA⟩ := hF.admissibility_bound hκ hs h00 hr hg hValid (Fin.last k) hAd
  obtain ⟨P⟩ := F.object.realize z hValid.1
  let Ad : GammaFiniteAdmissibilitySchema B p U.underlying.arity (k+1) sp := ⟨F.object,Fin.last k,A⟩
  obtain ⟨L,hL⟩ := F.object.exists_valid_elementary_bound hκ hs h00 hr hg z hValid.1.1 P
    (Fin.last k) (Ad.admissible z hA P)
  have hElementary := F.elementary_valid_of_bound z hValid L hL
  have hEssential : (F.elementaryFormula.essential.withBound L).valid z :=
    (F.elementaryFormula.withBound L).essential_valid z hElementary
  exact ⟨L,A,⟨hValid,hEssential,hA⟩,hF.elementary hκ hs h00 hr hValid.1.1 hAd L⟩

end DiamondIntegral.Section3
