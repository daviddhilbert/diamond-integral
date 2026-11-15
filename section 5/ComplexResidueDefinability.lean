import «section 5».FramedResidueConstructibility
import «section 5».ConstructibleFieldDefinability
import Section4.ResidueFieldInterpretation

/-! Complex constructible coordinates translate into the original RV
language over the full Laurent base, without naming any Kummer root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
local instance inverseResidueStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem residueRaw_complex (c : ℂ) :
    residueRaw (complexResidueEquiv c) = Sum.inr (residueLift c) := by
  change (residueRV (complexResidue c)).val = _
  rw [residueRV_complexResidue]
  rfl

theorem residueName_base (x : ModelResidue Carrier) : baseCarrier (residueRaw x) := by
  obtain ⟨c, rfl⟩ := complexResidueEquiv.surjective x
  rw [residueRaw_complex]
  by_cases hc : c = 0
  · simp [residueLift, hc, baseCarrier]
  · change baseCarrier (Sum.inr (residueLift c))
    simp only [residueLift, hc, ↓reduceDIte, baseCarrier]
    exact ⟨0, rfl⟩

def complexResidueImage {n : ℕ} (X : Set (Fin n → ℂ)) : Set (Fin n → Carrier) :=
  {z | ∃ x ∈ X, (fun i => Sum.inr (residueLift (x i))) = z}

theorem complex_residue_image_definable {n : ℕ} (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    {c | baseCarrier c}.Definable LRV (complexResidueImage X) := by
  let D : Set (Fin n → ModelResidue Carrier) :=
    {y | (complexResidueEquiv.symm ∘ y) ∈ X}
  have hD : Relative.Def (⊤ : Subfield (ModelResidue Carrier)) D :=
    ring_definable_preimage_equiv complexResidueEquiv.symm X hX
  have h := residueFieldImage_raw_definable (⊤ : Subfield (ModelResidue Carrier))
    {c | baseCarrier c} (fun c => residueName_base c.val) D hD
  have hvals (y : Fin n → ModelResidue Carrier) : residueFieldValues y =
      fun i => Sum.inr (residueLift (complexResidueEquiv.symm (y i))) := by
    funext i
    change residueRaw (y i) = _
    have he := residueRaw_complex (complexResidueEquiv.symm (y i))
    rw [complexResidueEquiv.apply_symm_apply] at he
    exact he
  convert h using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨complexResidueEquiv ∘ x, ?_, ?_⟩
    · change (complexResidueEquiv.symm ∘ (complexResidueEquiv ∘ x)) ∈ X
      have heq : complexResidueEquiv.symm ∘ (complexResidueEquiv ∘ x) = x :=
        funext (fun i => complexResidueEquiv.symm_apply_apply (x i))
      rwa [heq]
    · rw [hvals]
      simp only [Function.comp_apply, RingEquiv.symm_apply_apply]
  · rintro ⟨y, hy, he⟩
    exact ⟨complexResidueEquiv.symm ∘ y, hy, (hvals y).symm.trans he⟩

theorem constructible_residue_image_definable {n : ℕ}
    (C : Set (PrimeSpectrum (MvPolynomial (Fin n) (⊤ : Subfield ℂ)))) (hC : IsConstructible C) :
    {c | baseCarrier c}.Definable LRV
      (complexResidueImage {x | fieldTuplePrime (⊤ : Subfield ℂ) x ∈ C}) :=
  complex_residue_image_definable _ (constructible_field_definable _ C hC)

end DiamondIntegral.Section5.PuiseuxOriginal
