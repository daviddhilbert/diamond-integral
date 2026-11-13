import «section 3».RVValueFibreIndependence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rv_rank_extension_in_gamma_fibres (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {n m : ℕ}
    (a : Fin n → CanonicalRV.RVSort M) (γ : Fin m → Values.Gamma (M := M)) :
    ∃ b : Fin m → CanonicalRV.RVSort M, (∀ i, Values.vrv (b i) = (γ i).val) ∧
      rvTupleRank hc hex S a + m ≤ rvTupleRank hc hex S (Fin.append a b) := by
  obtain ⟨b,hb,hval⟩ := exists_independent_gamma_fibre_tuple hκ hs h00 (S ∪ Set.range (rvValues a))
    (small_union_range hκ S hsmall (rvValues a)) γ
  obtain ⟨v,_,hvinj,hvind,_⟩ := exists_rv_coordinate_basis_independent hc hex S a
  let d := rvTupleRank hc hex S a
  have haind : RVSequenceIndependent S (a ∘ v) := (rvSequenceIndependent_iff hc hex S _).mpr ⟨hvinj,hvind⟩
  have hb' : RVSequenceIndependent (S ∪ Set.range (rvValues (a ∘ v))) b := hb.mono_base (by
    rintro x (hx | ⟨i,rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨v i,rfl⟩)
  have hind := rvSequenceIndependent_append S (a ∘ v) b haind hb'
  let w : Fin (d+m) → Fin (n+m) :=
    Fin.addCases (fun i : Fin d => Fin.castAdd m (v i)) (Fin.natAdd n)
  have he : (Fin.append a b) ∘ w = Fin.append (a ∘ v) b := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,w,Fin.addCases_left,Fin.append_left]
    · simp only [Function.comp_apply,w,Fin.addCases_right,Fin.append_right]
      change b j = Fin.append (a ∘ v) b (Fin.natAdd (rvTupleRank hc hex S a) j)
      exact (Fin.append_right _ _ j).symm
  have hle := rvTupleRank_subsequence_le hc hex S (Fin.append a b) w
  rw [he,rvTupleRank_eq_arity_of_sequence hc hex S _ hind] at hle
  exact ⟨b,hval,hle⟩
end DiamondIntegral.Section3
