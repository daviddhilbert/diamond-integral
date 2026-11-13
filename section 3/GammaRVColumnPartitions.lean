import «section 3».FullGammaColumnPartition
import «section 3».IntegrationGammaParameters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Finite Gamma columns are separated by tests definable over the same
base; no representative of a column is adjoined as a real parameter. -/
theorem gammaRVBase_finite_column_partition (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B)
    (R : Values.Gamma (M := M) → M → Prop)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (hfinite : (relationColumn R '' D).Finite) :
    ∃ P : Finset (Set (Fin 1 → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ {z | z 0 ∈ D} ∧
        GammaParameters.DefinableOverBase B (fun _ => .rv) W ∧
        ∀ x ∈ W, ∀ u ∈ W, ∀ γ, R γ (x 0) ↔ R γ (u 0)) ∧
      (P : Set (Set (Fin 1 → M))).Pairwise Disjoint ∧
      {z : Fin 1 → M | z 0 ∈ D} = {z | ∃ W ∈ P, z ∈ W} := by
  have hfraw : (relationColumn (fun γ (z : Fin 1 → M) => R γ (z 0)) '' {z | z 0 ∈ D}).Finite := by
    apply hfinite.subset
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨z 0,hz,rfl⟩
  let F : Values.Gamma (M := M) → Set (Fin 1 → M) := fun γ => {z | R γ (z 0)}
  have hRF : FullBaseAtomicity.OverBase (integrationGammaBase B) (AdjoinGamma.vectorPullback F) := by
    have hh := FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable hR)
      (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
    convert hh using 1
    ext z
    simp only [AdjoinGamma.vectorPullback,Set.mem_ofPred_eq,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    rfl
  obtain ⟨ρ,hρ,hρ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  obtain ⟨P,hP,hDis,hCov⟩ := fullGammaFiniteColumnPartition h00 (integrationGammaBase B)
    ρ hρ hρ1 F hRF {z | z 0 ∈ D} (integrationGammaDefinable hD) hfraw
  refine ⟨P,fun W hW => ⟨(hP W hW).1,(hP W hW).2.1,?_,(hP W hW).2.2.2⟩,hDis,hCov⟩
  apply (integrationGammaDefinable_iff ?_).mpr (hP W hW).2.2.1
  intro z hz i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact hD.proper (z 0) ((hP W hW).2.1 hz)
end DiamondIntegral.Section3
