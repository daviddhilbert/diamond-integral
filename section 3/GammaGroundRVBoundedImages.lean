import «section 3».GammaGroundRealization
import «section 2».RVBoundedImages

/-! Lemma 2.41 (`db:to:db`) over a Γ-ground base. The checked statement is
for a real parameter set. A set definable over the real part together with
finitely many Γ names is definable over a small real set containing the real
part (`GammaGroundDefinable.realize`), and the conclusion of 2.41 (existence
of a double bound) does not mention parameters; so the Γ-ground statement
follows from the real one over that set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

omit [M ⊨ Axioms.ACVF] in
theorem rawRVSpace_preimage_eq (U : Set (Fin n → Section2.RVInfinity M)) :
    (rawRVSpace (M := M) n).preimage U = Section2.rvInputValues '' U := by
  ext z
  constructor
  · rintro ⟨hz,hU⟩
    exact ⟨(rawRVSpace (M := M) n).decode ⟨z,hz⟩,hU,rvValues_decode ⟨z,hz⟩⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨⟨a,rfl⟩,?_⟩
    change (rawRVSpace (M := M) n).decode ⟨rvValues a,⟨a,rfl⟩⟩ ∈ U
    rw [decode_rvValues]
    exact ha

/-- The graph of an RV-valued function as a relation on RV-tuple spaces. -/
def rvScalarGraphRelation (U : Set (Fin n → Section2.RVInfinity M))
    (f : (Fin n → Section2.RVInfinity M) → Section2.RV M)
    (u : (rawRVSpace (M := M) n).Carrier) (w : (rawRVSpace (M := M) 1).Carrier) : Prop :=
  u ∈ U ∧ w = fun _ => (f u).val

theorem rvScalarGraph_relation_eq (U : Set (Fin n → Section2.RVInfinity M))
    (f : (Fin n → Section2.RVInfinity M) → Section2.RV M) :
    (rawRVSpace (M := M) n).relation (rawRVSpace 1) (rvScalarGraphRelation U f) =
      Section2.rvScalarFunctionGraph U f := by
  ext z
  constructor
  · rintro ⟨hx,hy,hU,hw⟩
    refine ⟨(rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl,hx⟩,hU,rvValues_decode ⟨z ∘ Sum.inl,hx⟩,?_⟩
    have h := congrFun (rvValues_decode ⟨z ∘ Sum.inr,hy⟩) 0
    rw [hw] at h
    exact h
  · rintro ⟨u,hu,hl,hr⟩
    have hx : z ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain := ⟨u,hl⟩
    have hw : z ∘ Sum.inr = rvValues (fun _ : Fin 1 => (f u).val) := by
      funext i
      change z (Sum.inr i) = (f u).val.val
      have hi : (i : Fin 1) = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      rw [hi]
      exact hr.symm
    have hy : z ∘ Sum.inr ∈ (rawRVSpace (M := M) 1).domain := ⟨_,hw.symm⟩
    have hdu : (rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl,hx⟩ = u := by
      apply rvValues_injective
      exact (rvValues_decode _).trans hl.symm
    refine ⟨hx,hy,?_,?_⟩
    · rw [hdu]
      exact hu
    · rw [hdu]
      apply rvValues_injective
      exact (rvValues_decode _).trans hw

/-- Lemma 2.41 over a Γ-ground base. -/
theorem lemma_2_41_gammaGround
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (ground : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk ground.real < κ)
    (hΓ : Section2.NontrivialDefinableGamma (⟨ground.real,∅⟩ : Section2.ParameterBase M))
    (U : Set (Fin n → Section2.RVInfinity M)) (hU : GammaGroundDefinable hc ground (rawRVSpace n) U)
    (f : (Fin n → Section2.RVInfinity M) → Section2.RV M)
    (hf : GammaGroundDefinable hc ground ((rawRVSpace n).prod (rawRVSpace 1))
      {p | rvScalarGraphRelation U f p.1 p.2})
    (hbounded : Section2.RVValueDoublyBounded U) :
    ∃ γ : Section2.Gamma M, ∀ u ∈ U,
      (γ⁻¹).val ≤ Values.vrv (f u).val ∧ Values.vrv (f u).val ≤ γ.val := by
  obtain ⟨T₁,hT₁,hs₁,_,hU₁⟩ := hU.realize hκ hsmall
  obtain ⟨T₂,hT₂,hs₂,_,hf₂⟩ := hf.realize hκ hsmall
  let T := T₁ ∪ T₂
  have hsT : Cardinal.mk T < κ :=
    (Cardinal.mk_union_le T₁ T₂).trans_lt (Cardinal.add_lt_of_lt hκ hs₁ hs₂)
  have hUT : T.Definable LRV (Section2.rvInputValues '' U) := by
    have h : T₁.Definable LRV ((rawRVSpace (M := M) n).preimage U) := hU₁
    rw [rawRVSpace_preimage_eq] at h
    exact h.mono Set.subset_union_left
  have hfT : T.Definable LRV (Section2.rvScalarFunctionGraph U f) := by
    have h := (Space.definable_prod_iff (rawRVSpace (M := M) n) (rawRVSpace 1) T₂ (rvScalarGraphRelation U f)).mp hf₂
    change T₂.Definable LRV ((rawRVSpace (M := M) n).relation (rawRVSpace 1) (rvScalarGraphRelation U f)) at h
    rw [rvScalarGraph_relation_eq] at h
    exact h.mono Set.subset_union_right
  have hΓT : Section2.NontrivialDefinableGamma (⟨T,∅⟩ : Section2.ParameterBase M) :=
    hΓ.mono (hT₁.trans Set.subset_union_left) (Set.Subset.refl _)
  exact Section2.lemma_2_41 hc h00 linear hκ hs T hsT hΓT U hUT f hfT hbounded

end DiamondIntegral.Section3
