import «section 3».IntegrationDiscBases
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Finite support in the original Gamma/disc base, retaining all old actual disc names. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def integrationDiscNamesTuple {s k : ℕ} (closed : Fin k → Bool)
    (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M) (γ : Fin s → Values.Gamma (M := M)) :
    Fin (s+k) → ParameterPresentation.Name (M := M) :=
  Fin.append (fun i => Sum.inr (γ i)) (fun j => Sum.inl (Section2.finitePolydiscNames closed a δ j))

theorem integrationDiscWith (B : GammaParameters.Base (M := M)) {k n : ℕ}
    (closed : Fin k → Bool) (a : Fin k → Section2.VF M) (δ : Fin k → Section2.Gamma M)
    (A : Set (Fin n → M)) (hA : FullBaseAtomicity.OverBase (integrationDiscBase B closed a δ) A) :
    ∃ s, ∃ γ : Fin s → Values.Gamma (M := M), (∀ i, γ i ∈ B.gamma) ∧
      @ImaginaryParameters.WithTuple LRV M (CanonicalStructure.normalize (M := M))
        (ParameterPresentation.Name (M := M)) (Fin 5) (@ParameterPresentation.presentation M sM hM)
        B.real (Fin (s+k)) (Fin n) (integrationDiscNamesTuple closed a δ γ) A := by
  obtain ⟨F,hF,hw⟩ := hA
  let G := F.filter (fun i => ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
  have hG (j : G) : ∃ γ : Values.Gamma (M := M), j.val = Sum.inr γ := (Finset.mem_filter.mp j.property).2
  choose γ hname using hG
  have hg (j : G) : γ j ∈ B.gamma := by
    have h := hF j.val (Finset.mem_filter.mp j.property).1
    rw [hname j] at h
    rcases h with ⟨η,hη,he⟩ | ⟨D,hD,he⟩
    · exact (Sum.inr.inj he) ▸ hη
    · cases he
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let η : Fin (Fintype.card G) → Values.Gamma (M := M) := γ ∘ e.symm
  have hBall (j : F) (hj : ¬ ∃ γ : Values.Gamma (M := M), j.val = Sum.inr γ) :
      ∃ i : Fin k, j.val = Sum.inl (Section2.finitePolydiscNames closed a δ i) := by
    rcases hF j.val j.property with ⟨γ,hγ,he⟩ | ⟨D,⟨i,hi⟩,he⟩
    · exact (hj ⟨γ,he.symm⟩).elim
    · exact ⟨i,he.symm.trans (congrArg Sum.inl hi.symm)⟩
  let f (j : F) : Fin (Fintype.card G+k) :=
    if hj : ∃ γ : Values.Gamma (M := M), j.val = Sum.inr γ then
      Fin.castAdd k (e ⟨j.val,Finset.mem_filter.mpr ⟨j.property,hj⟩⟩)
    else Fin.natAdd (Fintype.card G) (hBall j hj).choose
  have hf : integrationDiscNamesTuple closed a δ η ∘ f = (Subtype.val : F → ParameterPresentation.Name (M := M)) := by
    funext j
    by_cases hj : ∃ γ : Values.Gamma (M := M), j.val = Sum.inr γ
    · simp only [Function.comp_apply,f,dite_eq_left hj,integrationDiscNamesTuple,Fin.append_left,
        η,Equiv.symm_apply_apply]
      exact (hname ⟨j.val,Finset.mem_filter.mpr ⟨j.property,hj⟩⟩).symm
    · simp only [Function.comp_apply,f,dite_eq_right hj,integrationDiscNamesTuple,Fin.append_right]
      exact (hBall j hj).choose_spec.symm
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  refine ⟨Fintype.card G,η,(fun i => hg (e.symm i)),?_⟩
  letI := CanonicalStructure.normalize (M := M)
  exact hw.reindex hp f hf
end DiamondIntegral.Section3
