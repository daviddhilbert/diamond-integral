import «section 5».OriginalEulerRowValues

/-! The actual Gamma fibre Euler integers have finite range and genuine
original-ground definable level sets, selected by whole certificates. -/
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
variable {B : Base (M := M)} {p n : ℕ} {sp : Fin p → SortTag}

theorem original_euler_row_values_constructible (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (D : GammaDomainFormula B p n sp) (hD : ∀ z ∈ A, originalGammaSourceValid hc D z) (kind : EulerKind) :
    (Set.range (fun z : A => originalGammaRowEulerValue hc h00 hκ hs hr hγ D z.val kind)).Finite ∧
      ∀ m : ℤ, DefinableOverBase B sp
        {z | z ∈ A ∧ originalGammaRowEulerValue hc h00 hκ hs hr hγ D z kind = m} := by
  obtain ⟨J, hJ⟩ := original_euler_finite_catalog hc h00 hκ hs hr hγ A hA D hD
  let c := fun z => originalGammaRowEulerValue hc h00 hκ hs hr hγ D z kind
  let e := fun C : OriginalEulerCertificate B sp n => (C.syntax hc).eulerValue kind
  have hsound (C : OriginalEulerCertificate B sp n) (z : Fin p → M) (hv : C.ValidFor hc D z) :
      c z = e C := C.originalGammaRowEulerValue hc h00 hκ hs hr hγ D z hv kind
  constructor
  · apply (J.image e).finite_toSet.subset
    rintro m ⟨z, rfl⟩
    obtain ⟨C, hC, hv⟩ := hJ z.val z.property
    exact Finset.mem_image.mpr ⟨C, hC, (hsound C z.val hv).symm⟩
  · intro m
    let K := J.filter (fun C => e C = m)
    let V := fun C : OriginalEulerCertificate B sp n =>
      {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧ C.ValidFor hc D z}
    have hU := DefinableOverBase.finite_iUnion K V (fun C _ => C.validFor_definable hc D)
    have h := hA.inter hU
    convert h using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    change (z ∈ A ∧ c z = m) ↔ (z ∈ A ∧ ∃ C ∈ K, z ∈ V C)
    constructor
    · rintro ⟨hz, hm⟩
      obtain ⟨C, hC, hv⟩ := hJ z hz
      refine ⟨hz, C, Finset.mem_filter.mpr ⟨hC, (hsound C z hv).symm.trans hm⟩, hA.proper z hz, hv⟩
    · rintro ⟨hz, C, hC, _, hv⟩
      exact ⟨hz, (hsound C z hv).trans (Finset.mem_filter.mp hC).2⟩

end DiamondIntegral.Section5
