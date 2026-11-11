import «section 2».GammaSuprema
import «section 2».RawFibreComparisons

/-! The least-upper-bound formula uniformly defines a Gamma-valued
fibre bound over the original base. All real codes of every Gamma value
are retained; no representative is selected as a parameter. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rawGammaFamilyGraph (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M)) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | z ∘ Sum.inl ∈ D ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
    GammaParameters.codeValue (z (.inr 0)) ∈ P (z ∘ Sum.inl)}

def rawGammaUpperGraph (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M)) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | z ∘ Sum.inl ∈ D ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
    GammaParameters.codeValue (z (.inr 0)) ∈ upperBounds (P (z ∘ Sum.inl))}

def rawGammaLUBGraph (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M)) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | z ∘ Sum.inl ∈ D ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
    IsLUB (P (z ∘ Sum.inl)) (GammaParameters.codeValue (z (.inr 0)))}

theorem rawGammaUpperGraph_eq (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M)) :
    rawGammaUpperGraph D P =
      {z | z ∘ Sum.inl ∈ D ∧ GammaParameters.NonzeroRV (z (.inr 0))} ∩
        rawFibreForallCompare (rawGammaFamilyGraph D P) iLe := by
  ext z
  constructor
  · rintro ⟨hzD,hzNZ,hupper⟩
    refine ⟨⟨hzD,hzNZ⟩,fun v hv => ?_⟩
    have hvNZ : GammaParameters.NonzeroRV v := hv.2.1
    have hvP : GammaParameters.codeValue v ∈ P (z ∘ Sum.inl) := hv.2.2
    exact (GammaParameters.original_le_codeValue_iff v (z (.inr 0)) hvNZ hzNZ).mpr (hupper hvP)
  · rintro ⟨⟨hzD,hzNZ⟩,hcompare⟩
    refine ⟨hzD,hzNZ,fun a ha => ?_⟩
    obtain ⟨v,hvNZ,hva⟩ := GammaParameters.EndpointLogic.codeValue_surjective a
    have hrow : Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => v) ∈ rawGammaFamilyGraph D P := by
      exact ⟨hzD,hvNZ,hva.symm ▸ ha⟩
    have hle := (GammaParameters.original_le_codeValue_iff v (z (.inr 0)) hvNZ hzNZ).mp (hcompare v hrow)
    rwa [hva] at hle

theorem rawGammaUpperGraph_definable (S : Set M) (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P)) :
    S.Definable LRV (rawGammaUpperGraph D P) := by
  rw [rawGammaUpperGraph_eq]
  have hNZ := (GammaParameters.nonzero_rv_definable S).preimage_comp
    (fun _ : Fin 1 => (Sum.inr 0 : Fin n ⊕ Fin 1))
  exact ((hD.preimage_comp Sum.inl).inter hNZ).inter
    (rawFibreForallCompare_definable S _ hP iLe (GammaParameters.raw_le_definable S))

theorem rawGammaLUBGraph_eq (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M)) :
    rawGammaLUBGraph D P = rawGammaUpperGraph D P ∩
      rawFibreForallCompare (rawGammaUpperGraph D P) (fun v u => iLe u v) := by
  ext z
  constructor
  · rintro ⟨hzD,hzNZ,hLUB⟩
    refine ⟨⟨hzD,hzNZ,hLUB.1⟩,fun v hv => ?_⟩
    have hvNZ : GammaParameters.NonzeroRV v := hv.2.1
    have hvU : GammaParameters.codeValue v ∈ upperBounds (P (z ∘ Sum.inl)) := hv.2.2
    exact (GammaParameters.original_le_codeValue_iff (z (.inr 0)) v hzNZ hvNZ).mpr (hLUB.2 hvU)
  · rintro ⟨⟨hzD,hzNZ,hupper⟩,hcompare⟩
    refine ⟨hzD,hzNZ,hupper,fun a ha => ?_⟩
    obtain ⟨v,hvNZ,hva⟩ := GammaParameters.EndpointLogic.codeValue_surjective a
    have hrow : Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => v) ∈ rawGammaUpperGraph D P :=
      ⟨hzD,hvNZ,hva.symm ▸ ha⟩
    have hle := (GammaParameters.original_le_codeValue_iff (z (.inr 0)) v hzNZ hvNZ).mp (hcompare v hrow)
    rwa [hva] at hle

theorem rawGammaLUBGraph_definable (S : Set M) (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P)) :
    S.Definable LRV (rawGammaLUBGraph D P) := by
  rw [rawGammaLUBGraph_eq]
  have hU := rawGammaUpperGraph_definable S D hD P hP
  have hrev : S.Definable₂ LRV {p : M × M | iLe p.2 p.1} := by
    change S.Definable LRV {z : Fin 2 → M | iLe (z 1) (z 0)}
    convert (GammaParameters.raw_le_definable S).preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
    ext z
    rfl
  exact hU.inter (rawFibreForallCompare_definable S _ hU _ hrev)

theorem rawGammaLUBGraph_selector_eq (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M))
    (g : (Fin n → M) → Gamma M) (hg : ∀ x ∈ D, IsLUB (P x) (g x)) :
    rawGammaLUBGraph D P = rawGammaFamilyGraph D (fun x => {g x}) := by
  ext z
  constructor
  · rintro ⟨hzD,hzNZ,hLUB⟩
    exact ⟨hzD,hzNZ,hLUB.unique (hg _ hzD)⟩
  · rintro ⟨hzD,hzNZ,hgval⟩
    have he : GammaParameters.codeValue (z (.inr 0)) = g (z ∘ Sum.inl) := hgval
    exact ⟨hzD,hzNZ,he.symm ▸ hg _ hzD⟩

theorem uniform_gamma_supremum (S : Set M) (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hexists : ∀ x ∈ D, ∃ c : Gamma M, IsLUB (P x) c) :
    ∃ g : (Fin n → M) → Gamma M,
      S.Definable LRV (rawGammaFamilyGraph D (fun x => {g x})) ∧ ∀ x ∈ D, IsLUB (P x) (g x) := by
  classical
  let g (x : Fin n → M) : Gamma M := if hx : x ∈ D then (hexists x hx).choose else 1
  have hg : ∀ x ∈ D, IsLUB (P x) (g x) := by
    intro x hx
    simpa only [g,dite_eq_left hx] using (hexists x hx).choose_spec
  refine ⟨g,?_,hg⟩
  rw [← rawGammaLUBGraph_selector_eq D P g hg]
  exact rawGammaLUBGraph_definable S D hD P hP

end DiamondIntegral.Section2
