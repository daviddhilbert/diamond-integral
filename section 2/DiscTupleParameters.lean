import «section 2».DiscParameters
import Section3.GammaProjection

/-! Actual finite-radius disc names with arbitrary finite real output
contexts. The complete relation ranges over every centre/radius presentation
and is invariant under equality of the DC names. Fixing a presentation
only occurs in the explicit auxiliary-base theorem below. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure FiniteDiscTupleRelation (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (sn : Fin m → SortTag) where
  supportArity : ℕ
  support : Fin supportArity → Gamma M
  support_mem : ∀ j, support j ∈ B.gamma
  relation : GammaParameters.Relation B.real (supportArity+n) (n+m)
    (Fin.append (fun _ : Fin n => .vf) sn)
  invariant : ∀ (a a' : Fin n → VF M) (δ δ' : Fin n → Gamma M),
    finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ' →
    ∀ x : Fin m → M,
      Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
          relation.fibre (Fin.append support δ) ↔
        Fin.append (SpecialTransformations.Section4.vfValues a') x ∈
          relation.fibre (Fin.append support δ')

def FiniteDiscTupleRelation.fibre {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    Set (Fin m → M) :=
  {x | Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
    R.relation.fibre (Fin.append R.support δ)}

/-- The output context is properly sorted even with no output coordinates. -/
theorem FiniteDiscTupleRelation.fibre_proper {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    R.fibre a δ ⊆ GammaParameters.sortedUniverse sn := by
  intro x hx j
  have h := R.relation.fibre_proper (Fin.append R.support δ) _ hx (Fin.natAdd n j)
  simpa only [Fin.append_right] using h

/-- No chosen centre or radius representative affects the named fibre. -/
theorem FiniteDiscTupleRelation.fibre_eq_of_names {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn)
    (a a' : Fin n → VF M) (δ δ' : Fin n → Gamma M)
    (he : finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ') :
    R.fibre a δ = R.fibre a' δ' := Set.ext (R.invariant a a' δ δ' he)

/-- Definability over the disc tuple uses an invariant global relation,
rather than selecting or naming a centre of any disc. -/
def DefinableOverFiniteDiscNames (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  ∃ R : FiniteDiscTupleRelation B closed sn, R.fibre a δ = A

theorem DefinableOverFiniteDiscNames.proper {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {a : Fin n → VF M} {δ : Fin n → Gamma M}
    {sn : Fin m → SortTag} {A : Set (Fin m → M)}
    (hA : DefinableOverFiniteDiscNames B closed a δ sn A) :
    A ⊆ GammaParameters.sortedUniverse sn := by
  obtain ⟨R, rfl⟩ := hA
  exact R.fibre_proper a δ

/-- Equal DC names give exactly the same definable sets in every output
arity; the real presentations need not themselves be ground-definable. -/
theorem definableOverFiniteDiscNames_iff_of_names (B : ParameterBase M) {n m : ℕ}
    (closed : Fin n → Bool) (a a' : Fin n → VF M) (δ δ' : Fin n → Gamma M)
    (he : finitePolydiscNames closed a δ = finitePolydiscNames closed a' δ')
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) :
    DefinableOverFiniteDiscNames B closed a δ sn A ↔
      DefinableOverFiniteDiscNames B closed a' δ' sn A := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R, (R.fibre_eq_of_names a a' δ δ' he).symm.trans hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R, (R.fibre_eq_of_names a a' δ δ' he).trans hR⟩

/-- The auxiliary real/Gamma presentation is explicit: its base contains
the chosen centres and actual finite radii. This is not a descent theorem. -/
theorem FiniteDiscTupleRelation.definable_fibre {B : ParameterBase M} {n m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (a : Fin n → VF M) (δ : Fin n → Gamma M) :
    GammaParameters.DefinableOverBase
      ⟨B.real ∪ Set.range (SpecialTransformations.Section4.vfValues a), B.gamma ∪ Set.range δ⟩
      sn (R.fibre a δ) := by
  let E : ParameterBase M :=
    ⟨B.real ∪ Set.range (SpecialTransformations.Section4.vfValues a), B.gamma ∪ Set.range δ⟩
  let sm := Fin.append (fun _ : Fin n => SortTag.vf) sn
  have hQ : GammaParameters.DefinableOverBase E sm
      (R.relation.fibre (Fin.append R.support δ)) := by
    refine ⟨R.supportArity+n, Fin.append R.support δ, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · change Fin.append R.support δ (Fin.castAdd n k) ∈ B.gamma ∪ Set.range δ
        simpa only [Fin.append_left, Set.mem_union] using Or.inl (R.support_mem k)
      · change Fin.append R.support δ (Fin.natAdd R.supportArity k) ∈ B.gamma ∪ Set.range δ
        simpa only [Fin.append_right, Set.mem_union] using Or.inr (Set.mem_range_self k)
    · exact GammaParameters.DefinableWith.mono_real ⟨R.relation, rfl⟩ Set.subset_union_left
  have hname (j : Fin n) : GammaParameters.DefinableClosureAtBase E .vf (a j).val :=
    GammaParameters.real_definableAtBase E .vf {(a j).val}
      (definableClosureAt_of_mem (Or.inr (Set.mem_range_self j)) (a j).property)
  have hN := (GammaParameters.tuple_singleton_definable_base E (fun _ : Fin n => .vf)
    (SpecialTransformations.Section4.vfValues a) hname).preimage_real sm (Fin.castAdd m)
  have hp := (hQ.inter hN).image_real (Fin.natAdd n)
  have hsn : sm ∘ Fin.natAdd n = sn := by
    funext j
    simp only [sm, Function.comp_apply, Fin.append_right]
  rw [hsn] at hp
  convert hp using 1
  ext x
  constructor
  · intro hx
    let w := Fin.append (SpecialTransformations.Section4.vfValues a) x
    have hw : w ∈ R.relation.fibre (Fin.append R.support δ) := hx
    refine ⟨w, ⟨hw, ?_⟩, ?_⟩
    · refine ⟨?_, hQ.proper w hw⟩
      funext j
      simp only [w, Function.comp_apply, Fin.append_left]
    · funext j
      simp only [w, Function.comp_apply, Fin.append_right]
  · rintro ⟨w, ⟨hw, hleft, _⟩, hright⟩
    have he : Fin.append (SpecialTransformations.Section4.vfValues a) x = w := by
      funext j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [Fin.append_left, Function.comp_apply] using (congrFun hleft k).symm
      · simpa only [Fin.append_right, Function.comp_apply] using (congrFun hright k).symm
    change Fin.append (SpecialTransformations.Section4.vfValues a) x ∈
      R.relation.fibre (Fin.append R.support δ)
    rwa [he]

end DiamondIntegral.Section2
