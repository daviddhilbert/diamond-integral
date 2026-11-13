import «section 3».IntegrationGammaTail
import «section 2».CitedDiscAtomicity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Full interpreted bases retain exactly the original real/Gamma names
and the finite tuple of actual disc names. The definable code fibres below
name no centre or radius representative. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def integrationDiscBase (B : GammaParameters.Base (M := M)) {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) :
    FullBaseAtomicity.Base (M := M) :=
  ⟨B.real, Sum.inr '' B.gamma ∪ Sum.inl '' Set.range (Section2.finitePolydiscNames closed a δ)⟩

theorem integrationDiscBase_mono (B : GammaParameters.Base (M := M)) {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) :
    (integrationGammaBase B).imaginary ⊆ (integrationDiscBase B closed a δ).imaginary :=
  Set.subset_union_left

theorem integrationDiscBase_name (B : GammaParameters.Base (M := M)) {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) (j : Fin k) :
    Sum.inl (Section2.finitePolydiscNames closed a δ j) ∈ (integrationDiscBase B closed a δ).imaginary :=
  Or.inr ⟨_,Set.mem_range_self j,rfl⟩

theorem integrationDiscBase_adjoinGamma (B : GammaParameters.Base (M := M)) {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (γ : Values.Gamma (M := M)) :
    integrationDiscBase (Section2.adjoinGamma B γ) closed a δ =
      (integrationDiscBase B closed a δ).adjoin (Sum.inr γ) := by
  change (⟨B.real,Sum.inr '' (insert γ B.gamma) ∪ _⟩ : FullBaseAtomicity.Base (M := M)) = _
  simp only [ImaginaryParameters.Base.adjoin,integrationDiscBase,Set.image_insert_eq,Set.insert_union]

theorem integrationNamedDiscCodes (B : FullBaseAtomicity.Base (M := M))
    (D : BallImaginaries.Ball M) (hD : Sum.inl D ∈ B.imaginary) (closed : Bool) :
    FullBaseAtomicity.OverBase B {z : Fin 2 → M |
      integrationDiscCode closed z ∈ (@ParameterPresentation.presentation M sM hM).pullback {Sum.inl D}} := by
  have hp := ParameterPresentation.presentation_definable (M := M) B.real
  have hm := integrationDiscCode_definable (M := M) B.real closed
  have hn : FullBaseAtomicity.OverBase B ((@ParameterPresentation.presentation M sM hM).pullback {Sum.inl D}) := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.named_singleton hp hD
  exact FullBaseAtomicity.OverBase.preimage_map hn hm

theorem integrationNamedDiscCodes_row (D : BallImaginaries.Ball M) (closed : Bool)
    (a r : Section2.VF M) (hr : r ≠ 0) :
    integrationDiscCode closed ![a.val,r.val] ∈
      (@ParameterPresentation.presentation M sM hM).pullback {Sum.inl D} ↔
    (if closed then Section2.closedDiscCode a (Section2.vfValue r)
      else Section2.openDiscCode a (Section2.finiteValue r hr)) = D := by
  obtain ⟨hp,hd⟩ := integrationDiscCode_compatible closed a r hr
  change (∃ h, ParameterPresentation.decode ⟨_,h⟩ = Sum.inl D) ↔ _
  constructor
  · rintro ⟨h,he⟩
    exact Sum.inl.inj (hd.symm.trans he)
  · intro he
    exact ⟨hp,hd.trans (congrArg Sum.inl he)⟩
end DiamondIntegral.Section3
