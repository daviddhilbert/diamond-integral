import «section 6».ContinuousRVTemplateOperations

/-! The combined first-order locus is equivalent to the seven semantic
branch-data conditions on its actual continuous chart functions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
namespace BranchedShearChartTemplate

theorem good_iff_semantics
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : BranchedShearChartTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) (a : Fin p → M) (hF : a ∈ T.goodFunctions) :
    a ∈ T.good A ↔
      (∀ w x,T.indicator.value a hF.1 w x 0=0 ∨ T.indicator.value a hF.1 w x 0=1) ∧
      (∀ x u,(x,u) ∈ (A.fibre a).carrier ↔ ∃ v,T.indicator.value a hF.1 (Fin.append u v) x 0=1) ∧
      (∀ x u v w,T.indicator.value a hF.1 (Fin.append u v) x 0=1 →
        T.indicator.value a hF.1 (Fin.append u w) x 0=1 → v=w) ∧
      (∀ x u v,T.indicator.value a hF.1 (Fin.append u v) x 0=1 → v ∘ T.labels=u) ∧
      (∀ x u v,T.indicator.value a hF.1 (Fin.append u v) x 0=1 → ∀ i,(v i).val ≠ iRVZero) ∧
      (∀ x u v,T.indicator.value a hF.1 (Fin.append u v) x 0=1 →
        rv M (x (Fin.last n)+T.offset.value a hF.2 (Fin.append u v) (Fin.init x) 0)=v T.leading) ∧
      (∀ x u v,T.indicator.value a hF.1 (Fin.append u v) x 0=1 → ∀ d : VF M,rv M d=v T.leading →
        T.indicator.value a hF.1 (Fin.append u v)
          (Function.update x (Fin.last n) (d-T.offset.value a hF.2 (Fin.append u v) (Fin.init x) 0)) 0=1) := by
  constructor
  · intro ha
    let D := T.toData hv A a ha
    exact ⟨D.binary,D.source,D.unique,D.retained,D.nonzero,D.leading_value,D.full_disc⟩
  · rintro ⟨hBinary,hSource,hUnique,hRetained,hNonzero,hLeading,hFull⟩
    refine ⟨hF,(rvScalarBinaryParameterLocus_at T.indicator a hF.1).mpr hBinary,?_,
      (T.uniqueGood_expanded_at a hF.1).mpr hUnique,?_,?_,?_,?_⟩
    · apply (T.sourceGood_at A a).mpr
      apply defSet_eq_of_carrier_eq
      ext q
      rcases q with ⟨x,u⟩
      rw [T.sourceTemplate_fibre_at a hF.1 x u]
      exact (hSource x u).symm
    · apply (T.retainedGood_at a hF.1).mpr
      intro w x hx
      apply hRetained x (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r)
      simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx
    · apply (T.nonzeroGood_at a hF.1).mpr
      intro w x hx
      apply hNonzero x (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r)
      simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx
    · apply (T.leadingGood_at a hF).mpr
      intro w x hx
      have h := hLeading x (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r)
      simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using h
        (by simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx)
    · apply (T.fullDiscGood_at a hF).mpr
      intro w x hx d hd
      have h := hFull x (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r)
      simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using h
        (by simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx) d hd

end BranchedShearChartTemplate
end DiamondIntegral.Section6
