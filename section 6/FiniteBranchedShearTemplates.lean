import «section 6».PromotedBranchedShearData

/-! Saturation selects finitely many complete admissible chart templates.
Their output RV arities may vary, and the original source family is
retained in every selected admissibility condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_branched_shear_templates
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (hLocal : ∀ a ∈ U,Nonempty (BranchedShearData (G := G) (A.fibre a))) :
    ∃ k : ℕ,∃ arity : Fin k → ℕ,
      ∃ T : (i : Fin k) → BranchedShearChartTemplate (M := M) S p n r (arity i),
        ∀ a ∈ U,∃ i,a ∈ (T i).good A := by
  let C := Set.range (fun T : Σ s,BranchedShearChartTemplate (M := M) S p n r s => T.2.good A)
  have hC : ∀ c ∈ C,S.Definable LRV c := by
    rintro c ⟨T,rfl⟩
    exact T.2.good_definable A
  have hCover (a) (ha : a ∈ U) : ∃ c ∈ C,a ∈ c := by
    obtain ⟨D⟩ := hLocal a ha
    obtain ⟨T,hT⟩ := exists_promoted_admissible_branched_shear_data hv A a D
    exact ⟨T.good A,⟨⟨D.arity,T⟩,rfl⟩,hT⟩
  obtain ⟨C₀,hFin,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall U hU C hC hCover
  letI : Fintype C₀ := hFin.fintype
  let e := Fintype.equivFin C₀
  let chooseT (c : C₀) := (hSub c.property).choose
  have hT (c : C₀) : (chooseT c).2.good A=c.val := (hSub c.property).choose_spec
  refine ⟨Fintype.card C₀,fun i => (chooseT (e.symm i)).1,fun i => (chooseT (e.symm i)).2,?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hCov a ha
  refine ⟨e ⟨c,hc⟩,?_⟩
  change a ∈ (chooseT (e.symm (e ⟨c,hc⟩))).2.good A
  rw [e.symm_apply_apply,hT]
  exact hac

end DiamondIntegral.Section6
