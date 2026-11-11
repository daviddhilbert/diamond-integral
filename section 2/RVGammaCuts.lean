import «section 2».UniformGammaSuprema
import Section8.GammaRadiusBase

/-! The unary RV-to-Gamma reduction in 2.41. The complete graph supplies
all definable order cuts, so the checked finite-image theorem applies on
each fixed finite input value fibre. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rawGammaLessGraph (D : Set (Fin n → M)) (f : (Fin n → M) → Gamma M) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | z ∘ Sum.inl ∈ D ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
    f (z ∘ Sum.inl) < GammaParameters.codeValue (z (.inr 0))}

theorem rawGammaLessGraph_eq (D : Set (Fin n → M)) (f : (Fin n → M) → Gamma M) :
    rawGammaLessGraph D f = rawGammaUpperGraph D (fun x => {f x}) \
      rawGammaFamilyGraph D (fun x => {f x}) := by
  ext z
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _ ∧ _) ∧ ¬ (_ ∧ _ ∧ _))
  constructor
  · rintro ⟨hzD,hzNZ,hlt⟩
    refine ⟨⟨hzD,hzNZ,?_⟩,?_⟩
    · intro a ha
      have he : a = f (z ∘ Sum.inl) := ha
      exact he.symm ▸ hlt.le
    · rintro ⟨_,_,he⟩
      exact hlt.ne he.symm
  · rintro ⟨⟨hzD,hzNZ,hupper⟩,hnot⟩
    refine ⟨hzD,hzNZ,lt_of_le_of_ne (hupper (Set.mem_singleton _)) ?_⟩
    intro he
    exact hnot ⟨hzD,hzNZ,he.symm⟩

theorem rawGammaLessGraph_definable (S : Set M) (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (f : (Fin n → M) → Gamma M) (hf : S.Definable LRV (rawGammaFamilyGraph D (fun x => {f x}))) :
    S.Definable LRV (rawGammaLessGraph D f) := by
  rw [rawGammaLessGraph_eq]
  exact (rawGammaUpperGraph_definable S D hD _ hf).sdiff hf

theorem rv_gamma_image_finite_on_value_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (S D : Set M) (hsmall : Cardinal.mk S < κ) (hD : DefinableAt S .rv D)
    (γ : Gamma M) (hDγ : ∀ t : RVInfinity M, t.val ∈ D → Values.vrv t = γ.val)
    (f : M → Gamma M)
    (hf : S.Definable LRV (rawGammaFamilyGraph {x : Fin 1 → M | x 0 ∈ D} (fun x => {f (x 0)}))) :
    (f '' D).Finite := by
  have hLess := rawGammaLessGraph_definable S {x : Fin 1 → M | x 0 ∈ D}
    hD.raw_definable (fun x => f (x 0)) hf
  have hcuts : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S
      (GammaParameters.cutFamily D f) := by
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]
    change S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M |
      (z ∘ Sum.inl,z (.inr 0)) ∈ GammaParameters.cutFamily D f}
    let idx : Fin 1 ⊕ Fin 1 → Fin 1 ⊕ Fin 1 := Sum.swap
    convert hLess.preimage_comp idx using 1
    ext z
    change (GammaParameters.NonzeroRV (z (.inl 0)) ∧ z (.inr 0) ∈ D ∧
      f (z (.inr 0)) < GammaParameters.codeValue (z (.inl 0))) ↔
      (z (.inr 0) ∈ D ∧ GammaParameters.NonzeroRV (z (.inl 0)) ∧
        f (z (.inr 0)) < GammaParameters.codeValue (z (.inl 0)))
    tauto
  exact GammaParameters.finite_image_of_definable_cuts hs S D hsmall hD γ hDγ f hcuts

end DiamondIntegral.Section2
