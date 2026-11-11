import «section 2».UniformGammaSuprema
import «section 2».RawFibreRelationalImages
import Section4.GammaMultiplicationSyntax
import Section8.GammaRadiusBase

/-! Absolute Gamma values and their full code graphs, for the author's
uniform fibre-bound construction. In multiplicative notation the absolute
value is max(gamma, gamma inverse). -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def gammaAbs (γ : Gamma M) : Gamma M := max γ γ⁻¹

theorem gammaAbs_le_iff (x γ : Gamma M) : gammaAbs x ≤ γ ↔ γ⁻¹ ≤ x ∧ x ≤ γ := by
  constructor
  · intro h
    have hx := (max_le_iff.mp h).1
    have hi := inv_le_inv' (max_le_iff.mp h).2
    exact ⟨by simpa only [inv_inv] using hi,hx⟩
  · rintro ⟨hl,hu⟩
    apply max_le_iff.mpr
    exact ⟨hu,by simpa only [inv_inv] using inv_le_inv' hl⟩

theorem gamma_inverse_definable (S : Set M) {ι : Type} [Finite ι] (i j : ι) :
    GammaSyntax.Definable S (fun z : ι → Gamma M => z j = (z i)⁻¹) := by
  have hm := GammaSyntax.mul_definable (M := M) S
    (Sum.inl i : ι ⊕ Fin 1) (.inl j) (.inr 0)
  have ho := GammaSyntax.unary_at (GammaSyntax.one_definable (M := M) S) (Sum.inr (0 : Fin 1) : ι ⊕ Fin 1)
  apply ((hm.and ho).exists_block).congr
  intro z
  change (∃ u : Fin 1 → Gamma M, z i*z j = u 0 ∧ u 0 ∈ ({1} : Set (Gamma M))) ↔ z j = (z i)⁻¹
  constructor
  · rintro ⟨u,hm,ho⟩
    have hu : u 0 = 1 := ho
    exact eq_inv_of_mul_eq_one_right (hm.trans hu)
  · intro he
    exact ⟨fun _ => 1,by rw [he,mul_inv_cancel],Set.mem_singleton _⟩

theorem gamma_max_definable (S : Set M) {ι : Type} [Finite ι] (i j k : ι) :
    GammaSyntax.Definable S (fun z : ι → Gamma M => z k = max (z i) (z j)) := by
  have h := ((GammaSyntax.lt_definable (M := M) S j i).not.and (GammaSyntax.eq_definable S k j)).or
    ((GammaSyntax.lt_definable S i j).not.and (GammaSyntax.eq_definable S k i))
  apply h.congr
  intro z
  change ((¬ z j < z i ∧ z k = z j) ∨ (¬ z i < z j ∧ z k = z i)) ↔ z k = max (z i) (z j)
  constructor
  · rintro (⟨hle,he⟩ | ⟨hle,he⟩)
    · rwa [max_eq_right (le_of_not_gt hle)]
    · rwa [max_eq_left (le_of_not_gt hle)]
  · intro he
    by_cases hij : z i ≤ z j
    · exact Or.inl ⟨not_lt_of_ge hij,by simpa only [max_eq_right hij] using he⟩
    · exact Or.inr ⟨not_lt_of_ge (le_of_not_ge hij),by simpa only [max_eq_left (le_of_not_ge hij)] using he⟩

theorem gammaAbs_definable (S : Set M) :
    GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 1 = gammaAbs (z 0)) := by
  have hi := gamma_inverse_definable (M := M) S
    (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1) (.inr 0)
  have hm := gamma_max_definable (M := M) S
    (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1) (.inr 0) (.inl 1)
  apply ((hi.and hm).exists_block).congr
  intro z
  change (∃ u : Fin 1 → Gamma M, u 0 = (z 0)⁻¹ ∧ z 1 = max (z 0) (u 0)) ↔ z 1 = gammaAbs (z 0)
  constructor
  · rintro ⟨u,hi,hm⟩
    rwa [hi] at hm
  · intro he
    exact ⟨fun _ => (z 0)⁻¹,rfl,he⟩

def gammaAbsCodeRelation (a b : M) : Prop :=
  GammaParameters.NonzeroRV a ∧ GammaParameters.NonzeroRV b ∧
    GammaParameters.codeValue b = gammaAbs (GammaParameters.codeValue a)

theorem gammaAbsCodeRelation_definable (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    S.Definable₂ LRV {p : M × M | gammaAbsCodeRelation p.1 p.2} := by
  have h := gammaAbs_definable (M := M) S
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
    {z | GammaSyntax.Proper z ∧ GammaParameters.codeValue (z 1) = gammaAbs (GammaParameters.codeValue (z 0))} at h
  rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at h
  change S.Definable LRV {z : Fin 2 → M | gammaAbsCodeRelation (z 0) (z 1)}
  convert h using 1
  ext z
  constructor
  · rintro ⟨h0,h1,he⟩
    exact ⟨by intro j; fin_cases j; exact h0; exact h1,he⟩
  · rintro ⟨hz,he⟩
    exact ⟨hz 0,hz 1,he⟩

theorem rawGammaFamilyGraph_abs_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n : ℕ} (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M))
    (hP : S.Definable LRV (rawGammaFamilyGraph D P)) :
    S.Definable LRV (rawGammaFamilyGraph D (fun x => gammaAbs '' P x)) := by
  have h := rawFibreRelationalImage_definable S _ hP gammaAbsCodeRelation (gammaAbsCodeRelation_definable hc S)
  convert h using 1
  ext z
  constructor
  · rintro ⟨hzD,hzNZ,a,ha,haz⟩
    obtain ⟨v,hvNZ,hva⟩ := GammaParameters.EndpointLogic.codeValue_surjective a
    refine ⟨v,⟨hzD,hvNZ,hva.symm ▸ ha⟩,hvNZ,hzNZ,?_⟩
    exact haz.symm.trans (congrArg gammaAbs hva.symm)
  · rintro ⟨v,⟨hzD,hvNZ,hvP⟩,_,hzNZ,he⟩
    exact ⟨hzD,hzNZ,GammaParameters.codeValue v,hvP,he.symm⟩

end DiamondIntegral.Section2
