import «section 6».ContinuousVFGraphTemplates
import Section3.TupleCompactness

/-! Compactness for actual parameter-definable continuous focus choices.
Admissibility checks the complete function graph and its prescribed
pointwise relation before extracting a finite original-base family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def graphRowSubsetParameterLocus (R P : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M)) : Set (Fin p → M) :=
  {t | ∀ z,Sum.elim t z ∈ R → Sum.elim t z ∈ P}

theorem graphRowSubsetParameterLocus_definable
    (R P : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M))
    (hR : S.Definable LRV R) (hP : S.Definable LRV P) :
    S.Definable LRV (graphRowSubsetParameterLocus R P) := by
  convert ((hR.inter hP.compl).exists_of_finite).compl using 1
  ext t
  change (∀ z,Sum.elim t z ∈ R → Sum.elim t z ∈ P) ↔
    ¬ ∃ z : Fin n ⊕ Fin m → M,Sum.elim t z ∈ R ∧ Sum.elim t z ∉ P
  simp only [not_exists,not_and,not_not]

namespace ContinuousVFGraphTemplate
def goodWithin (T : ContinuousVFGraphTemplate (M := M) S p n m)
    (P : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M)) : Set (Fin p → M) :=
  T.good ∩ graphRowSubsetParameterLocus T.graph P

theorem goodWithin_definable (T : ContinuousVFGraphTemplate (M := M) S p n m)
    (P : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M)) (hP : S.Definable LRV P) :
    S.Definable LRV (T.goodWithin P) :=
  T.good_definable.inter (graphRowSubsetParameterLocus_definable T.graph P T.definable hP)

theorem value_satisfies (T : ContinuousVFGraphTemplate (M := M) S p n m)
    (P : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M)) (t : Fin p → M) (ht : t ∈ T.goodWithin P)
    (x : Fin n → VF M) :
    Sum.elim t (Sum.elim (vfValues x) (vfValues (T.value t ht.1 x))) ∈ P :=
  ht.2 _ (T.value_mem t ht.1 x)

end ContinuousVFGraphTemplate

theorem exists_promoted_constrained_continuous_vf_template
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (P : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M))
    (a : Fin p → M) (f : (Fin n → VF M) → Fin m → VF M)
    (hf : (S ∪ Set.range a).Definable LRV (vfGraph f)) (hCont : Continuous f)
    (hGood : ∀ x,Sum.elim a (Sum.elim (vfValues x) (vfValues (f x))) ∈ P) :
    ∃ T : ContinuousVFGraphTemplate (M := M) S p n m,a ∈ T.goodWithin P ∧
      {z : Fin n ⊕ Fin m → M | Sum.elim a z ∈ T.graph}=vfGraph f := by
  obtain ⟨T,hT,hSection⟩ := exists_promoted_continuous_vf_graph_template hv a f hf hCont
  refine ⟨T,⟨hT,?_⟩,hSection⟩
  intro z hz
  obtain ⟨x,rfl⟩ := (Set.ext_iff.mp hSection z).mp hz
  exact hGood x

theorem exists_finite_continuous_vf_templates
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin p → M)) (hA : S.Definable LRV A)
    (P : Set (Fin p ⊕ (Fin n ⊕ Fin m) → M)) (hP : S.Definable LRV P)
    (hLocal : ∀ a ∈ A,∃ f : (Fin n → VF M) → Fin m → VF M,
      (S ∪ Set.range a).Definable LRV (vfGraph f) ∧ Continuous f ∧
      ∀ x,Sum.elim a (Sum.elim (vfValues x) (vfValues (f x))) ∈ P) :
    ∃ k : ℕ,∃ T : Fin k → ContinuousVFGraphTemplate (M := M) S p n m,
      ∀ a ∈ A,∃ i,a ∈ (T i).goodWithin P := by
  let C := Set.range (fun T : ContinuousVFGraphTemplate (M := M) S p n m => T.goodWithin P)
  have hC : ∀ c ∈ C,S.Definable LRV c := by
    rintro c ⟨T,rfl⟩
    exact T.goodWithin_definable P hP
  have hCover (a) (ha : a ∈ A) : ∃ c ∈ C,a ∈ c := by
    obtain ⟨f,hf,hCont,hGood⟩ := hLocal a ha
    obtain ⟨T,hT,_⟩ := exists_promoted_constrained_continuous_vf_template hv P a f hf hCont hGood
    exact ⟨T.goodWithin P,⟨T,rfl⟩,hT⟩
  obtain ⟨C₀,hFin,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall A hA C hC hCover
  letI : Fintype C₀ := hFin.fintype
  let e := Fintype.equivFin C₀
  let chooseT (c : C₀) := (hSub c.property).choose
  have hT (c : C₀) : (chooseT c).goodWithin P=c.val := (hSub c.property).choose_spec
  refine ⟨Fintype.card C₀,fun i => chooseT (e.symm i),?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hCov a ha
  refine ⟨e ⟨c,hc⟩,?_⟩
  change a ∈ (chooseT (e.symm (e ⟨c,hc⟩))).goodWithin P
  rw [e.symm_apply_apply,hT]
  exact hac

end DiamondIntegral.Section6
