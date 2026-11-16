import «section 6».BranchedShearAdmissibleTemplates

/-! Every actual local branch-data witness promotes into the full
admissibility locus over the original base. Equality of entire family
graphs determines the actual chart functions, on every RV row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s m : ℕ}

theorem ContinuousRVGraphTemplate.value_eq_of_family_section
    (T : ContinuousRVGraphTemplate (M := M) S p r n m) (a : Fin p → M) (ha : a ∈ T.good)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hSection : {z : Fin r ⊕ (Fin n ⊕ Fin m) → M | Sum.elim a z ∈ T.graph}=rvVFGraph f) :
    T.value a ha=f := by
  funext u x i
  have hMem : Sum.elim (rvValues u) (Sum.elim (vfValues x) (vfValues (T.value a ha u x))) ∈ rvVFGraph f :=
    (Set.ext_iff.mp hSection _).mp (T.value_mem a ha u x)
  obtain ⟨v,y,hCode⟩ := hMem
  have hv : v=u := rvValues_injective (by funext j; exact congrFun hCode (.inl j))
  have hy : y=x := vfValues_injective (by funext j; exact congrFun hCode (.inr (.inl j)))
  subst v
  subst y
  exact Subtype.ext (congrFun hCode (.inr (.inr i))).symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_admissible_branched_shear_data
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) (a : Fin p → M)
    (D : BranchedShearData (G := G) (A.fibre a)) :
    ∃ T : BranchedShearChartTemplate (M := M) S p n r D.arity,a ∈ T.good A := by
  obtain ⟨T,hLabels,hLeading,hF,hIGraph,hOGraph⟩ := exists_promoted_branched_shear_charts hv a D
  have hI := T.indicator.value_eq_of_family_section a hF.1 D.indicator hIGraph
  have hO := T.offset.value_eq_of_family_section a hF.2 D.offset hOGraph
  refine ⟨T,hF,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (rvScalarBinaryParameterLocus_at T.indicator a hF.1).mpr
    rw [hI]
    exact D.binary
  · apply (T.sourceGood_at A a).mpr
    apply defSet_eq_of_carrier_eq
    ext q
    rcases q with ⟨x,u⟩
    rw [T.sourceTemplate_fibre_at a hF.1 x u,hI]
    exact (D.source x u).symm
  · apply (T.uniqueGood_expanded_at a hF.1).mpr
    rw [hI]
    exact D.unique
  · apply (T.retainedGood_at a hF.1).mpr
    rw [hI,hLabels]
    intro w x hx
    apply D.retained x (w ∘ Fin.castAdd D.arity) (w ∘ Fin.natAdd r)
    simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx
  · apply (T.nonzeroGood_at a hF.1).mpr
    rw [hI]
    intro w x hx
    apply D.nonzero x (w ∘ Fin.castAdd D.arity) (w ∘ Fin.natAdd r)
    simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx
  · apply (T.leadingGood_at a hF).mpr
    rw [hI,hO,hLeading]
    intro w x hx
    have h := D.leading_value x (w ∘ Fin.castAdd D.arity) (w ∘ Fin.natAdd r)
    simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using h
      (by simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx)
  · apply (T.fullDiscGood_at a hF).mpr
    rw [hI,hO,hLeading]
    intro w x hx d hd
    have h := D.full_disc x (w ∘ Fin.castAdd D.arity) (w ∘ Fin.natAdd r)
    simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using h
      (by simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using hx) d hd

end DiamondIntegral.Section6
