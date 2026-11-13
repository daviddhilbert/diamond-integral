import «section 3».FiniteDefinableColumns
import IntegrationSection3ACVF.FullGammaAtomicity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Finitely many Gamma columns have a finite partition over exactly the
original full base. The separating Gamma tests are definable over that base. -/
theorem fullGammaFiniteColumnPartition (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M)) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ) {n : ℕ}
    (R : Values.Gamma (M := M) → Set (Fin n → M))
    (hR : FullBaseAtomicity.OverBase B (AdjoinGamma.vectorPullback R))
    (D : Set (Fin n → M)) (hD : FullBaseAtomicity.OverBase B D)
    (hfinite : (relationColumn (fun γ x => x ∈ R γ) '' D).Finite) :
    ∃ P : Finset (Set (Fin n → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ D ∧ FullBaseAtomicity.OverBase B W ∧
        ∀ x ∈ W, ∀ u ∈ W, ∀ γ, x ∈ R γ ↔ u ∈ R γ) ∧
      (P : Set (Set (Fin n → M))).Pairwise Disjoint ∧ D = {x | ∃ W ∈ P, x ∈ W} := by
  have hchoose (A : Set (Fin n → M)) (hA : FullBaseAtomicity.OverBase B A)
      (hc : ∃ x ∈ A, ∃ u ∈ A, relationColumn (fun γ x => x ∈ R γ) x ≠
        relationColumn (fun γ x => x ∈ R γ) u) :
      ∃ γ, FullBaseAtomicity.OverBase B (A ∩ {x | x ∈ R γ}) ∧
        FullBaseAtomicity.OverBase B (A \ {x | x ∈ R γ}) ∧
        (∃ x ∈ A, x ∈ R γ) ∧ (∃ u ∈ A, u ∉ R γ) := by
    have hbad := FullGammaAtomicity.cutParameters_definable hA hR
    have hne : (FullGammaAtomicity.cutParameters A R).Nonempty := by
      obtain ⟨x,hx,u,hu,hne⟩ := hc
      have hdiff : ∃ γ, ¬ (x ∈ R γ ↔ u ∈ R γ) := by
        by_contra hn
        push_neg at hn
        exact hne (Set.ext hn)
      obtain ⟨γ,hγ⟩ := hdiff
      refine ⟨γ,?_⟩
      by_cases hxγ : x ∈ R γ
      · exact ⟨x,hx,hxγ,u,hu,fun huγ => hγ (iff_of_true hxγ huγ)⟩
      · have huγ : u ∈ R γ := by
          by_contra huγ
          exact hγ (iff_of_false hxγ huγ)
        exact ⟨u,hu,huγ,x,hx,hxγ⟩
    obtain ⟨γ,hγ,hγdef⟩ := FullGammaPoint.gamma_definable_point h00 δ hδ hδ1 _ hbad hne
    have hr := AdjoinGamma.fibre_definable hR γ hγdef
    obtain ⟨x,hx,hxr,u,hu,hun⟩ := hγ
    exact ⟨γ,FullBaseAtomicity.OverBase.inter hA hr,
      FullBaseAtomicity.OverBase.inter hA (FullBaseAtomicity.OverBase.compl hr),⟨x,hx,hxr⟩,⟨u,hu,hun⟩⟩
  obtain ⟨P,hP,hDis,hCov⟩ := finite_definable_column_partition (fun γ x => x ∈ R γ)
    (FullBaseAtomicity.OverBase B) hchoose D hD hfinite
  refine ⟨P,fun W hW => ⟨(hP W hW).1,(hP W hW).2.1,(hP W hW).2.2.1,?_⟩,hDis,hCov⟩
  intro x hx u hu γ
  exact Set.ext_iff.mp ((hP W hW).2.2.2 x hx u hu) γ
end DiamondIntegral.Section3
