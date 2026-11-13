import Section3.RVExchange
import Section4.RVSequenceBounds
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_nonalgebraic_in_gamma_fibre {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (δ : Values.Gamma (M := M)) :
    ∃ x : CanonicalRV.RVSort M, Values.vrv x = δ.val ∧ ¬ AlgebraicAt S .rv x.val := by
  let c := representative δ
  let T := insert (raw c) S
  have hXd := rawValueFibre_definable S c
  have hXinf := rawValueFibre_infinite h00 c
  have hex : ∃ x ∈ rawValueFibre c, ¬ AlgebraicAt T .rv x := by
    by_contra h
    push Not at h
    exact hXinf (RawClosure.finite_of_definable_subset_algebraic hs T
      (small_insert hκ S hsmall (raw c)) (rawValueFibre c) hXd.raw_definable
      (fun x hx => (h x hx).raw_finite_witness))
  obtain ⟨x,hx,hnot⟩ := hex
  let t : CanonicalRV.RVSort M := ⟨x,hXd.2 hx⟩
  refine ⟨t,?_,fun h => hnot (h.mono (Set.subset_insert (raw c) S))⟩
  exact (rawValueFibre_value c t hx).trans (congrArg Subtype.val (representative_value δ))

/-- Every finite tuple of Gamma values supports a full algebraically
independent RV sequence over any given small real base. -/
theorem exists_independent_gamma_fibre_tuple {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {m : ℕ}
    (γ : Fin m → Values.Gamma (M := M)) :
    ∃ t : Fin m → CanonicalRV.RVSort M, RVSequenceIndependent S t ∧ ∀ i, Values.vrv (t i) = (γ i).val := by
  induction m with
  | zero => exact ⟨Fin.elim0,trivial,fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨t,ht,hval⟩ := ih (Fin.init γ)
    obtain ⟨x,hx,hnot⟩ := exists_nonalgebraic_in_gamma_fibre hκ hs h00 (S ∪ Set.range (rvValues t))
      (small_union_range hκ S hsmall (rvValues t)) (γ (Fin.last m))
    refine ⟨Fin.snoc t x,?_,?_⟩
    · simpa only [RVSequenceIndependent,Fin.init_snoc,Fin.snoc_last] using And.intro ht hnot
    · refine Fin.lastCases ?_ (fun i => ?_)
      · simpa only [Fin.snoc_last] using hx
      · simpa only [Fin.snoc_castSucc,Fin.init_def] using hval i

theorem rvSequenceIndependent_append (S : Set M) {d m : ℕ}
    (a : Fin d → CanonicalRV.RVSort M) (b : Fin m → CanonicalRV.RVSort M)
    (ha : RVSequenceIndependent S a) (hb : RVSequenceIndependent (S ∪ Set.range (rvValues a)) b) :
    RVSequenceIndependent S (Fin.append a b) := by
  induction m with
  | zero =>
    have he : Fin.append a b = a := by
      rw [Fin.append_right_nil a b rfl]
      funext i
      congr 1
    rwa [he]
  | succ m ih =>
    rw [← Fin.snoc_init_self b,Fin.append_snoc]
    constructor
    · simpa only [Fin.init_snoc] using ih (Fin.init b) hb.1
    · have hh := hb.2
      have he : S ∪ Set.range (rvValues (Fin.append a (Fin.init b))) =
          (S ∪ Set.range (rvValues a)) ∪ Set.range (rvValues (Fin.init b)) := by
        have hv : rvValues (Fin.append a (Fin.init b)) = Fin.append (rvValues a) (rvValues (Fin.init b)) := by
          funext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · simp only [rvValues,Fin.append_left]
          · simp only [rvValues,Fin.append_right]
        have hr : Set.range (Fin.append (rvValues a) (rvValues (Fin.init b))) =
            Set.range (rvValues a) ∪ Set.range (rvValues (Fin.init b)) := by
          ext x
          constructor
          · rintro ⟨i,rfl⟩
            refine Fin.addCases (fun j => ?_) (fun j => ?_) i
            · rw [Fin.append_left]
              exact Or.inl ⟨j,rfl⟩
            · rw [Fin.append_right]
              exact Or.inr ⟨j,rfl⟩
          · rintro (⟨i,rfl⟩ | ⟨j,rfl⟩)
            · exact ⟨Fin.castAdd m i,Fin.append_left _ _ i⟩
            · exact ⟨Fin.natAdd d j,Fin.append_right _ _ j⟩
        rw [hv,hr,Set.union_assoc]
      simp only [Fin.init_snoc,Fin.snoc_last]
      change ¬ AlgebraicAt (S ∪ Set.range (rvValues (Fin.append a (Fin.init b)))) .rv (b (Fin.last m)).val
      rwa [he]
end DiamondIntegral.Section3
