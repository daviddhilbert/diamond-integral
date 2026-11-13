import «section 3».ResidueGammaColumns
import «section 3».FullGammaColumnPartition
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



def gammaTupleColumnValues {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop) (W : Set (Fin n → M)) :
    Set (Values.Gamma (M := M)) := {γ | ∃ a ∈ W, R a γ}

theorem gammaTuplePullback_definable (B : Base (M := M)) {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop)
    (hR : DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | NonzeroRV (z (Fin.last n)) ∧ R (Fin.init z) (codeValue (z (Fin.last n)))}) :
    FullRawDefinable (integrationGammaBase B)
      (fun z : Fin 1 ⊕ Fin n → M => NonzeroRV (z (.inl 0)) ∧ R (z ∘ Sum.inr) (codeValue (z (.inl 0)))) := by
  let π : Fin (n+1) → Fin 1 ⊕ Fin n := Fin.lastCases (.inl 0) Sum.inr
  have hh := FullRawDefinable.reindex (integrationGammaDefinable hR) π
  convert hh using 1
  ext z
  have he : Fin.init (z ∘ π) = z ∘ Sum.inr := by
    funext i
    simp only [Fin.init,Function.comp_apply,π,Fin.lastCases_castSucc]
  change (NonzeroRV (z (.inl 0)) ∧ R (z ∘ Sum.inr) (codeValue (z (.inl 0)))) ↔ _
  simp only [Function.comp_apply,π,Fin.lastCases_last] at he ⊢
  rw [← he]

theorem gammaTupleColumnValues_definable (B : Base (M := M)) {n : ℕ}
    (R : (Fin n → M) → Values.Gamma (M := M) → Prop)
    (hR : DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | NonzeroRV (z (Fin.last n)) ∧ R (Fin.init z) (codeValue (z (Fin.last n)))})
    (W : Set (Fin n → M)) (hW : DefinableOverBase B (fun _ => .rv) W) :
    FullGammaSyntax.Scalar (integrationGammaBase B) (gammaTupleColumnValues R W) := by
  have hh := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (gammaTuplePullback_definable B R hR)
    (FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable hW) (Sum.inr : Fin n → Fin 1 ⊕ Fin n)))
  change FullBaseAtomicity.OverBase (integrationGammaBase B)
    {a : Fin 1 → M | a 0 ∈ Values.gammaPullback (gammaTupleColumnValues R W)}
  convert hh using 1
  ext a
  change (a 0 ∈ Values.gammaPullback (gammaTupleColumnValues R W)) ↔ _
  rw [GammaSyntax.mem_gammaPullback_iff]
  change (NonzeroRV (a 0) ∧ ∃ z ∈ W, R z (codeValue (a 0))) ↔
    ∃ z : Fin n → M, (NonzeroRV (a 0) ∧ R z (codeValue (a 0))) ∧ z ∈ W
  exact ⟨fun ⟨hn,z,hz,hr⟩ => ⟨z,⟨hn,hr⟩,hz⟩,fun ⟨z,⟨hn,hr⟩,hz⟩ => ⟨hn,z,hz,hr⟩⟩

/-- ACVF orthogonality for finite-value RV tuples and one Gamma variable.
Every factor remains definable over the original real/Gamma ground. -/
theorem residue_tuple_gamma_finite_rectangles {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {n : ℕ} (R : (Fin n → M) → Values.Gamma (M := M) → Prop)
    (hR : DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | NonzeroRV (z (Fin.last n)) ∧ R (Fin.init z) (codeValue (z (Fin.last n)))})
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (hsub : ∀ a ∈ A, ∀ i, a i ∈ D i) :
    ∃ P : Finset (Set (Fin n → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ DefinableOverBase B (fun _ => .rv) W ∧
        FullGammaSyntax.Scalar (integrationGammaBase B) (gammaTupleColumnValues R W)) ∧
      (P : Set (Set (Fin n → M))).Pairwise Disjoint ∧
      ∀ a ∈ A, ∀ γ, R a γ ↔ ∃ W ∈ P, a ∈ W ∧ γ ∈ gammaTupleColumnValues R W := by
  have hf := residue_tuple_gamma_finite_columns hκ hs h00 B hsmall hγsmall R hR A hA D hD hvalues hsub
  obtain ⟨δ,hδ,hδ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  let F : Values.Gamma (M := M) → Set (Fin n → M) := fun γ => {a | R a γ}
  have hF : FullBaseAtomicity.OverBase (integrationGammaBase B) (AdjoinGamma.vectorPullback F) :=
    gammaTuplePullback_definable B R hR
  obtain ⟨P,hP,hDis,hCov⟩ := fullGammaFiniteColumnPartition h00 (integrationGammaBase B)
    δ hδ hδ1 F hF A (integrationGammaDefinable hA) hf
  have hW : ∀ W ∈ P, DefinableOverBase B (fun _ => .rv) W := by
    intro W hw
    apply (integrationGammaDefinable_iff (fun a ha i => hA.proper a ((hP W hw).2.1 ha) i)).mpr
    exact (hP W hw).2.2.1
  refine ⟨P,fun W hw => ⟨(hP W hw).1,(hP W hw).2.1,hW W hw,
    gammaTupleColumnValues_definable B R hR W (hW W hw)⟩,hDis,?_⟩
  intro a ha γ
  constructor
  · intro hr
    obtain ⟨W,hw,haW⟩ := (Set.ext_iff.mp hCov a).mp ha
    exact ⟨W,hw,haW,a,haW,hr⟩
  · rintro ⟨W,hw,haW,b,hb,hr⟩
    exact ((hP W hw).2.2.2 a haW b hb γ).mpr hr
end DiamondIntegral.Section3
