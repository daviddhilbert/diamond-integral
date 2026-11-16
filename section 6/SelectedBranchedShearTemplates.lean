import «section 6».FiniteBranchedShearCovers
import «section 6».FiniteRVTemplateChoices

/-! The finite disjoint choice cover yields one pair of complete chart
formulas over the original base. Both charts are continuous in their VF
inputs for every parameter, and fully admissible on the covered family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r m k : ℕ}

theorem finiteRVTemplateChoice_value_at
    (T : Fin k → ContinuousRVGraphTemplate (M := M) S p r n m)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (C : Fin k → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hSub : ∀ i,C i ⊆ U) (hDisj : ∀ i j a,a ∈ C i → a ∈ C j → i=j)
    (a : Fin p → M) (i : Fin k) (hi : a ∈ C i) (hGood : a ∈ (T i).good)
    (hNew : a ∈ (finiteRVTemplateChoice T U hU C hC).good) :
    (finiteRVTemplateChoice T U hU C hC).value a hNew=(T i).value a hGood := by
  have hGraph := finiteRVTemplateChoice_graph_at T U hU C hC hSub hDisj a i hi
  apply ContinuousRVGraphTemplate.value_eq_of_rows
  intro u
  ext z
  exact (Set.ext_iff.mp hGraph _).trans (Set.ext_iff.mp ((T i).value_graph a hGood u) z)

namespace FiniteBranchedShearCover
variable {A : MixedSetParameterTemplate (M := M) S p (n+1) r} {U : Set (Fin p → M)}

def selectedTemplate (F : FiniteBranchedShearCover A U) (hU : S.Definable LRV U) :
    BranchedShearChartTemplate (M := M) S p n r F.arity where
  indicator := finiteRVTemplateChoice (fun i => (F.templates i).indicator) U hU F.choices F.choices_definable
  offset := finiteRVTemplateChoice (fun i => (F.templates i).offset) U hU F.choices F.choices_definable
  labels := F.labels
  labels_injective := F.labels_injective
  leading := F.leading

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem selectedTemplate_goodFunctions
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FiniteBranchedShearCover A U) (hU : S.Definable LRV U) (a : Fin p → M) :
    a ∈ (F.selectedTemplate hU).goodFunctions :=
  ⟨finiteRVTemplateChoice_good hv _ U hU F.choices F.choices_definable
      (fun i _ ha => ⟨(F.choices_good i ha).1,(F.choices_good i ha).2.1.1⟩) F.cover F.disjoint a,
    finiteRVTemplateChoice_good hv _ U hU F.choices F.choices_definable
      (fun i _ ha => ⟨(F.choices_good i ha).1,(F.choices_good i ha).2.1.2⟩) F.cover F.disjoint a⟩

theorem selectedTemplate_good
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FiniteBranchedShearCover A U) (hU : S.Definable LRV U) (a : Fin p → M) (ha : a ∈ U) :
    a ∈ (F.selectedTemplate hU).good A := by
  obtain ⟨i,hi⟩ := F.cover a ha
  have hGood := (F.choices_good i hi).2
  have hF := F.selectedTemplate_goodFunctions hv hU a
  have hI := finiteRVTemplateChoice_value_at (fun j => (F.templates j).indicator) U hU
    F.choices F.choices_definable (fun j _ hj => (F.choices_good j hj).1) F.disjoint a i hi hGood.1.1 hF.1
  have hO := finiteRVTemplateChoice_value_at (fun j => (F.templates j).offset) U hU
    F.choices F.choices_definable (fun j _ hj => (F.choices_good j hj).1) F.disjoint a i hi hGood.1.2 hF.2
  change (F.selectedTemplate hU).indicator.value a hF.1=(F.templates i).indicator.value a hGood.1.1 at hI
  change (F.selectedTemplate hU).offset.value a hF.2=(F.templates i).offset.value a hGood.1.2 at hO
  let D := (F.templates i).toData hv A a hGood
  apply ((F.selectedTemplate hU).good_iff_semantics hv A a hF).mpr
  rw [hI,hO]
  refine ⟨D.binary,D.source,D.unique,?_,D.nonzero,?_,?_⟩
  · intro x u v hv
    change v ∘ F.labels=u
    rw [← F.labels_eq i]
    exact D.retained x u v hv
  · intro x u v hv
    change rv M (x (Fin.last n)+D.offset (Fin.append u v) (Fin.init x) 0)=v F.leading
    rw [← F.leading_eq i]
    exact D.leading_value x u v hv
  · intro x u v hv d hd
    have hd' : rv M d=v (F.templates i).leading := by
      rw [F.leading_eq i]
      exact hd
    exact D.full_disc x u v hv d hd'

end FiniteBranchedShearCover

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_uniform_branched_shear_template
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (hLocal : ∀ a ∈ U,Nonempty (BranchedShearData (G := G) (A.fibre a))) :
    ∃ s : ℕ,∃ T : BranchedShearChartTemplate (M := M) S p n r s,
      (∀ a,a ∈ T.goodFunctions) ∧ ∀ a ∈ U,a ∈ T.good A := by
  obtain ⟨F⟩ := exists_finite_branched_shear_cover hv hs hsmall A U hU hLocal
  exact ⟨F.arity,F.selectedTemplate hU,F.selectedTemplate_goodFunctions hv hU,F.selectedTemplate_good hv hU⟩

end DiamondIntegral.Section6
