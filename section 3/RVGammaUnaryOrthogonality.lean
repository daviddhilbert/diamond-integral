import «section 3».GammaRVColumnPartitions
import «section 3».GammaRVFiniteValueColumns
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

def gammaRVColumnValues (R : Values.Gamma (M := M) → M → Prop) (W : Set (Fin 1 → M)) :
    Set (Values.Gamma (M := M)) := {γ | ∃ z ∈ W, R γ (z 0)}

theorem gammaRVColumnValues_definable (B : GammaParameters.Base (M := M))
    (R : Values.Gamma (M := M) → M → Prop)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (W : Set (Fin 1 → M)) (hW : GammaParameters.DefinableOverBase B (fun _ => .rv) W) :
    FullGammaSyntax.Scalar (integrationGammaBase B) (gammaRVColumnValues R W) := by
  let F : Values.Gamma (M := M) → Set (Fin 1 → M) := fun γ => {z | R γ (z 0)}
  have hRF : FullBaseAtomicity.OverBase (integrationGammaBase B) (AdjoinGamma.vectorPullback F) := by
    have hh := FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable hR)
      (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
    convert hh using 1
    ext z
    simp only [AdjoinGamma.vectorPullback,Set.mem_ofPred_eq,Function.comp_apply,Matrix.cons_val_zero]
    rfl
  have hh := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hRF
    (FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable hW) (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)))
  change FullBaseAtomicity.OverBase (integrationGammaBase B)
    {a : Fin 1 → M | a 0 ∈ Values.gammaPullback (gammaRVColumnValues R W)}
  convert hh using 1
  ext a
  change (a 0 ∈ Values.gammaPullback (gammaRVColumnValues R W)) ↔ _
  rw [GammaSyntax.mem_gammaPullback_iff]
  change (NonzeroRV (a 0) ∧ ∃ z ∈ W, R (codeValue (a 0)) (z 0)) ↔
    ∃ z : Fin 1 → M, (NonzeroRV (a 0) ∧ R (codeValue (a 0)) (z 0)) ∧ z ∈ W
  exact ⟨fun ⟨hn,z,hz,hr⟩ => ⟨z,⟨hn,hr⟩,hz⟩,fun ⟨z,⟨hn,hr⟩,hz⟩ => ⟨hn,z,hz,hr⟩⟩

/-- Unary ACVF counterpart of the finite-value-support rectangle step.
Both factors are definable over the original ground, including at RV zero. -/
theorem rv_gamma_unary_finite_rectangles {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : Values.Gamma (M := M) → M → Prop) (hsort : ∀ γ t, R γ t → iRV t)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite) :
    ∃ P : Finset (Set (Fin 1 → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ {z | z 0 ∈ D} ∧
        GammaParameters.DefinableOverBase B (fun _ => .rv) W ∧
        FullGammaSyntax.Scalar (integrationGammaBase B) (gammaRVColumnValues R W)) ∧
      (P : Set (Set (Fin 1 → M))).Pairwise Disjoint ∧
      ∀ γ x, x ∈ D → (R γ x ↔ ∃ W ∈ P, ![x] ∈ W ∧ γ ∈ gammaRVColumnValues R W) := by
  have hfinite := gammaRVBase_finite_value_columns hκ hs h00 B hsmall R hsort hR D hD hvalues
  obtain ⟨P,hP,hDis,hCov⟩ := gammaRVBase_finite_column_partition h00 B hΓ R hR D hD hfinite
  refine ⟨P,fun W hW => ⟨(hP W hW).1,(hP W hW).2.1,(hP W hW).2.2.1,
    gammaRVColumnValues_definable B R hR W (hP W hW).2.2.1⟩,hDis,?_⟩
  intro γ x hx
  constructor
  · intro hr
    obtain ⟨W,hW,hxW⟩ := (Set.ext_iff.mp hCov ![x]).mp hx
    exact ⟨W,hW,hxW,![x],hxW,hr⟩
  · rintro ⟨W,hW,hxW,u,hu,hr⟩
    exact ((hP W hW).2.2.2 ![x] hxW u hu γ).mpr hr
end DiamondIntegral.Section3
