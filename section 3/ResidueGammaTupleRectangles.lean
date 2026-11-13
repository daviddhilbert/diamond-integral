import «section 3».ResidueGammaTupleColumns
import «section 3».FiniteDefinableColumns
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]



def gammaTupleFamilyValues {n m : ℕ}
    (R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop) (W : Set (Fin n → M)) :
    Set (Fin m → Values.Gamma (M := M)) := {γ | ∃ a ∈ W, R a γ}

theorem gammaTupleFamilyValues_definable {B : Base (M := M)} {n m : ℕ}
    {R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop}
    (hR : mixedGammaTupleDefinable B R) (W : Set (Fin n → M))
    (hW : FullRawDefinable (integrationGammaBase B) (fun a => a ∈ W)) :
    FullGammaSyntax.Definable (integrationGammaBase B) (fun γ => γ ∈ gammaTupleFamilyValues R W) := by
  have hp := FullRawDefinable.reindex hR (Sum.swap : Fin n ⊕ Fin m → Fin m ⊕ Fin n)
  have hh := (hp.and (hW.reindex (Sum.inr : Fin n → Fin m ⊕ Fin n))).exists_block
  apply FullBaseAtomicity.OverBase.congr hh
  intro c
  change (∃ a : Fin n → M, (GammaSyntax.Proper c ∧ R a (GammaSyntax.decode c)) ∧ a ∈ W) ↔
    (GammaSyntax.Proper c ∧ ∃ a ∈ W, R a (GammaSyntax.decode c))
  exact ⟨fun ⟨a,⟨hc,hr⟩,ha⟩ => ⟨hc,a,ha,hr⟩,fun ⟨hc,a,ha,hr⟩ => ⟨a,⟨hc,hr⟩,ha⟩⟩

/-- Finite disjoint original-ground rectangles for any finite residue
and Gamma tuple arities. No HK theorem is an input to this proof. -/
theorem residue_gamma_tuple_finite_rectangles {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {n m : ℕ} (R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop)
    (hR : mixedGammaTupleDefinable B R) (hsort : ∀ a γ, R a γ → ∀ i, iRV (a i))
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (hsub : ∀ a ∈ A, ∀ i, a i ∈ D i) :
    ∃ P : Finset (Set (Fin n → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ DefinableOverBase B (fun _ => .rv) W ∧
        FullGammaSyntax.Definable (integrationGammaBase B) (fun γ => γ ∈ gammaTupleFamilyValues R W)) ∧
      (P : Set (Set (Fin n → M))).Pairwise Disjoint ∧
      ∀ a ∈ A, ∀ γ, R a γ ↔ ∃ W ∈ P, a ∈ W ∧ γ ∈ gammaTupleFamilyValues R W := by
  let U := fun γ a => R a γ
  let Def (W : Set (Fin n → M)) := FullRawDefinable (integrationGammaBase B) (fun a => a ∈ W) ∧ W ⊆ A
  have hf := residue_gamma_tuple_finite_columns hκ hs h00 B hsmall hγsmall hΓ R hR hsort A hA D hD hvalues hsub
  have hchoose : ∀ W, Def W → (∃ a ∈ W, ∃ b ∈ W, relationColumn U a ≠ relationColumn U b) →
      ∃ γ, Def (W ∩ {a | U γ a}) ∧ Def (W \ {a | U γ a}) ∧
        (∃ a ∈ W, U γ a) ∧ (∃ b ∈ W, ¬ U γ b) := by
    intro W hW ⟨a,ha,b,hb,hne⟩
    have hd : ∃ γ, ¬ (R a γ ↔ R b γ) := by
      by_contra hh
      push_neg at hh
      exact hne (Set.ext hh)
    obtain ⟨γ,hγ,hsep⟩ := residue_columns_named_gamma_tuple_separation hκ hs h00 B hsmall hΓ R hR
      D hD hvalues a b (hsub a (hW.2 ha)) (hsub b (hW.2 hb)) hd
    have hr := hR.fibre γ (fun i => integrationGammaDefinable (hγ i))
    refine ⟨γ,⟨hW.1.and hr,fun a h => hW.2 h.1⟩,
      ⟨hW.1.and hr.not,fun a h => hW.2 h.1⟩,?_⟩
    by_cases hra : R a γ
    · exact ⟨⟨a,ha,hra⟩,⟨b,hb,fun hrb => hsep (iff_of_true hra hrb)⟩⟩
    · have hrb : R b γ := by
        by_contra hrb
        exact hsep (iff_of_false hra hrb)
      exact ⟨⟨b,hb,hrb⟩,⟨a,ha,hra⟩⟩
  obtain ⟨P,hP,hDis,hCov⟩ := finite_definable_column_partition U Def hchoose A
    ⟨integrationGammaDefinable hA,Set.Subset.rfl⟩ hf
  have hW : ∀ W ∈ P, DefinableOverBase B (fun _ => .rv) W := by
    intro W hw
    apply (integrationGammaDefinable_iff (fun a ha i => hA.proper a ((hP W hw).2.1 ha) i)).mpr
    exact (hP W hw).2.2.1.1
  refine ⟨P,fun W hw => ⟨(hP W hw).1,(hP W hw).2.1,hW W hw,
    gammaTupleFamilyValues_definable hR W (hP W hw).2.2.1.1⟩,hDis,?_⟩
  intro a ha γ
  constructor
  · intro hr
    obtain ⟨W,hw,haW⟩ := (Set.ext_iff.mp hCov a).mp ha
    exact ⟨W,hw,haW,a,haW,hr⟩
  · rintro ⟨W,hw,haW,b,hb,hr⟩
    exact (Set.ext_iff.mp ((hP W hw).2.2.2 a haW b hb) γ).mpr hr
end DiamondIntegral.Section3
