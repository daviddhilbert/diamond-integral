import «section 3».UnaryResidueGammaClosure
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Finite tuples of residue parameters add no Gamma-algebraic values.
Each coordinate is allowed any ground-definable finite set of values. -/
theorem residue_tuple_gamma_algebraic_elimination {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (a : Fin n → M) (ha : ∀ i, a i ∈ D i) (δ : Values.Gamma (M := M))
    (hδ : GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ) :
    GammaDefinableClosureAtBase B δ := by
  induction n with
  | zero =>
    have he : (⟨B.real ∪ Set.range a,B.gamma⟩ : Base (M := M)) = B := by
      have hr : Set.range a = ∅ := by
        ext x
        exact ⟨fun ⟨i,_⟩ => i.elim0,False.elim⟩
      simp only [hr,Set.union_empty]
    rw [he] at hδ
    exact (gamma_algebraic_iff_definable_base B δ).mp hδ
  | succ n ih =>
    let C : Base (M := M) := ⟨B.real ∪ Set.range (Fin.init a),B.gamma⟩
    have hCsmall : Cardinal.mk C.real < κ := small_union_range hκ B.real hsmall (Fin.init a)
    have hlastD : DefinableAtBase C .rv (D (Fin.last n)) :=
      (hD (Fin.last n)).mono Set.subset_union_left Set.Subset.rfl
    have he : (⟨C.real ∪ Set.range ![a (Fin.last n)],C.gamma⟩ : Base (M := M)) =
        ⟨B.real ∪ Set.range a,B.gamma⟩ := by
      have hreal : C.real ∪ Set.range ![a (Fin.last n)] = B.real ∪ Set.range a := by
        ext x
        constructor
        · rintro ((hx | ⟨i,hi⟩) | ⟨i,hi⟩)
          · exact Or.inl hx
          · exact Or.inr ⟨i.castSucc,hi⟩
          · have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
            subst i
            exact Or.inr ⟨Fin.last n,hi⟩
        · rintro (hx | ⟨i,hi⟩)
          · exact Or.inl (Or.inl hx)
          · revert hi
            refine Fin.lastCases ?_ (fun j hj => ?_) i
            · intro hi
              exact Or.inr ⟨0,hi⟩
            · exact Or.inl (Or.inr ⟨j,hj⟩)
      exact congrArg (fun U : Set M => (⟨U,B.gamma⟩ : Base (M := M))) hreal
    have hδC : GammaDefinableClosureAtBase C δ :=
      unary_residue_gamma_algebraic_elimination hκ hs h00 C hCsmall (D (Fin.last n)) hlastD
        (hvalues (Fin.last n)) (a (Fin.last n)) (ha (Fin.last n)) δ (he.symm ▸ hδ)
    exact ih (fun i => D i.castSucc) (fun i => hD i.castSucc) (fun i => hvalues i.castSucc)
      (Fin.init a) (fun i => ha i.castSucc) ((gamma_algebraic_iff_definable_base C δ).mpr hδC)
end DiamondIntegral.Section3
