import «section 4».GammaFiniteDecomposition

/-! Homomorphisms from the intrinsic finite Gamma ring are determined by
degree-zero weighted units and degree-one value fibres. The proof uses
actual RV-lifted singleton product isomorphisms and finite decomposition. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteGenerators
open GammaFiniteRVCharts GammaFiniteRVPresentation GammaFiniteDecomposition
open GammaNameTuples GammaDefinableMaps FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def weightedUnit (B : Base (M := M)) (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) : FiniteChart B 0 :=
  GammaFiniteRVCharts.ofTotal B 0 Set.univ (GammaIntegerFamilies.univ_definable_base B 0) (Set.toFinite _)
    (fun _ => β) (constant_definable B β hβ)

def fibre (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) : FiniteChart B 1 :=
  ⟨RESFibreObjects.gammaFibre B α β hα hβ, RESFibreObjects.gammaFibre_finite B α β hα hβ⟩

def singletonChart {B : Base (M := M)} {n : ℕ} (α : NameTuple B n) (β : Values.Gamma (M := M))
    (hβ : GammaDefinableClosureAtBase B β) : FiniteChart B n :=
  GammaFiniteRVCharts.ofTotal B n {GammaNameTuples.values α} (GammaNameTuples.singleton_definable α) (Set.finite_singleton _)
    (fun _ => β) (constant_definable B β hβ)

theorem singleton_zero_class {B : Base (M := M)} (α : NameTuple B 0) (β : Values.Gamma (M := M))
    (hβ : GammaDefinableClosureAtBase B β) : objectClass (singletonChart α β hβ) = objectClass (weightedUnit B β hβ) := by
  apply class_eq_on_domain (singletonChart α β hβ) (weightedUnit B β hβ)
  · ext z
    change z = GammaNameTuples.values α ↔ True
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim _ _⟩
  · intro z hz
    rfl

theorem singleton_succ_class {B : Base (M := M)} {n : ℕ} (α : NameTuple B (n + 1))
    (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    objectClass (singletonChart α β hβ) =
      objectClass (fibre B (α 0).val 1 (α 0).property (GammaGroupNames.one_definable_base B)) *
        objectClass (singletonChart (Fin.tail α) β hβ) := by
  let a := fibre B (α 0).val 1 (α 0).property (GammaGroupNames.one_definable_base B)
  let b := singletonChart (Fin.tail α) β hβ
  have hs : (singletonChart α β hβ).support = (GammaFiniteRVCharts.product a b).support := by
    ext z
    change (z = GammaNameTuples.values α) ↔
      ((z ∘ headIndex n 1) 0 = (α 0).val ∧ z ∘ tailIndex n 1 = GammaNameTuples.values (Fin.tail α))
    constructor
    · intro h
      subst z
      exact ⟨rfl, by funext i; rfl⟩
    · rintro ⟨h0, ht⟩
      funext i
      exact Fin.cases h0 (fun j => congrFun ht j) i
  have hv : ∀ z ∈ (singletonChart α β hβ).support,
      (singletonChart α β hβ).volume z = (GammaFiniteRVCharts.product a b).volume z := by
    intro z hz
    have he : z = GammaNameTuples.values α := hz
    subst z
    have ha : GammaNameTuples.values α ∘ headIndex n 1 ∈ a.support := by
      change (GammaNameTuples.values α ∘ headIndex n 1) 0 = (α 0).val
      rfl
    have hb : GammaNameTuples.values α ∘ tailIndex n 1 ∈ b.support := by
      change GammaNameTuples.values α ∘ tailIndex n 1 = GammaNameTuples.values (Fin.tail α)
      funext i
      rfl
    change β = GammaSumMap.sumMap a.toChart.normalizedVolume b.toChart.normalizedVolume (GammaNameTuples.values α)
    unfold GammaSumMap.sumMap
    rw [a.toChart.normalizedVolume_on _ ha, b.toChart.normalizedVolume_on _ hb]
    exact (one_mul β).symm
  exact (class_eq_on_domain (singletonChart α β hβ) (GammaFiniteRVCharts.product a b) hs hv).trans (class_product a b)

theorem hom_agree_singletons (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : ChartRing B →+* R)
    (h0 : ∀ β (hβ : GammaDefinableClosureAtBase B β), f (objectClass (weightedUnit B β hβ)) = g (objectClass (weightedUnit B β hβ)))
    (h1 : ∀ α β (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β),
      f (objectClass (fibre B α β hα hβ)) = g (objectClass (fibre B α β hα hβ)))
    {n : ℕ} (α : NameTuple B n) (β : Values.Gamma (M := M)) (hβ : GammaDefinableClosureAtBase B β) :
    f (objectClass (singletonChart α β hβ)) = g (objectClass (singletonChart α β hβ)) := by
  induction n with
  | zero =>
    exact (congrArg f (singleton_zero_class α β hβ)).trans
      ((h0 β hβ).trans (congrArg g (singleton_zero_class α β hβ)).symm)
  | succ n ih =>
    have hf := congrArg f (singleton_succ_class α β hβ)
    have hg := congrArg g (singleton_succ_class α β hβ)
    rw [map_mul] at hf hg
    exact hf.trans ((congrArg₂ (· * ·)
      (h1 (α 0).val 1 (α 0).property (GammaGroupNames.one_definable_base B)) (ih (Fin.tail α))).trans hg.symm)

theorem hom_ext_by_generators (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : ChartRing B →+* R)
    (h0 : ∀ β (hβ : GammaDefinableClosureAtBase B β), f (objectClass (weightedUnit B β hβ)) = g (objectClass (weightedUnit B β hβ)))
    (h1 : ∀ α β (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β),
      f (objectClass (fibre B α β hα hβ)) = g (objectClass (fibre B α β hα hβ))) : f = g := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  obtain ⟨s, hs, hd⟩ := finite_class_decomposition a
  have hf := congrArg f hd
  have hg := congrArg g hd
  rw [map_sum] at hf hg
  refine hf.trans ((Finset.sum_congr rfl ?_).trans hg.symm)
  intro α _
  exact hom_agree_singletons B f g h0 h1 α (a.toChart.normalizedVolume (GammaNameTuples.values α))
    (GammaNameTuples.scalar_value_definable α a.toChart.normalizedVolume a.toChart.normalizedVolume_definable)

end DiamondIntegral.Section4.GammaFiniteGenerators
