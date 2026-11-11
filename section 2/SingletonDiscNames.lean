import «section 2».BlockTypeFibres
import «section 2».GammaRelationMaps
import «section 2».DiscGeometry

/-!
# Singleton closed-disc names

A closed disc of radius infinity determines its unique VF point. Its point
chart is injective, so no arbitrary representative is chosen. Definability
in this chart is proved equivalent to naming the corresponding actual VF
tuple. This is the remaining point chart in the closed case of Lemma 2.25.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem closedDiscCode_infinity_underlying (a : VF M) :
    BallImaginaries.underlying (closedDiscCode a (Values.infinity (M := M))) = {a.val} := by
  obtain ⟨G, hG, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  ext x
  constructor
  · intro hx
    let b : VF M := ⟨x, disc_underlying_subset_vf _ hx⟩
    have hb : b ∈ discPoints (closedDiscCode a (Values.infinity (M := M))) := hx
    rw [closedDiscCode_infinity_points v hv] at hb
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp hb)
  · rintro rfl
    have h : a ∈ discPoints (closedDiscCode a (Values.infinity (M := M))) := by
      rw [closedDiscCode_infinity_points v hv]
      exact Set.mem_singleton a
    exact h

noncomputable def singletonDiscTupleNames {n : ℕ} (a : Fin n → VF M) : Fin n → DC (M := M) :=
  fun i => closedDiscCode (a i) (Values.infinity (M := M))

theorem singletonDiscTupleNames_injective {n : ℕ} :
    Function.Injective (singletonDiscTupleNames (M := M) (n := n)) := by
  intro a b he
  funext i
  have h := congrArg BallImaginaries.underlying (congrFun he i)
  simp only [singletonDiscTupleNames, closedDiscCode_infinity_underlying] at h
  exact Subtype.ext (Set.singleton_injective h)

structure SingletonDiscTupleRelation (B : ParameterBase M) (n : ℕ) {m : ℕ} (sn : Fin m → SortTag) where
  supportArity : ℕ
  support : Fin supportArity → Gamma M
  support_mem : ∀ j, support j ∈ B.gamma
  relation : GammaParameters.Relation B.real supportArity (n+m) (Fin.append (fun _ : Fin n => .vf) sn)

def SingletonDiscTupleRelation.fibre {B : ParameterBase M} {n m : ℕ} {sn : Fin m → SortTag}
    (R : SingletonDiscTupleRelation B n sn) (a : Fin n → VF M) : Set (Fin m → M) :=
  {x | Fin.append (SpecialTransformations.Section4.vfValues a) x ∈ R.relation.fibre R.support}

theorem SingletonDiscTupleRelation.fibre_eq_of_names {B : ParameterBase M} {n m : ℕ}
    {sn : Fin m → SortTag} (R : SingletonDiscTupleRelation B n sn)
    (a b : Fin n → VF M) (he : singletonDiscTupleNames a = singletonDiscTupleNames b) :
    R.fibre a = R.fibre b := by
  rw [singletonDiscTupleNames_injective he]

def DefinableOverSingletonDiscNames (B : ParameterBase M) {n m : ℕ} (a : Fin n → VF M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  ∃ R : SingletonDiscTupleRelation B n sn, R.fibre a = A

omit hM in
private theorem append_constants_definable (T : Set M) {n m : ℕ} (a : Fin n → M)
    (ha : ∀ i, a i ∈ T) : T.DefinableMap LRV (fun x : Fin m → M => Fin.append a x) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Fin.append_left] using LRV.definableFun_const (Fin m) (ha i)
  · simpa only [Fin.append_right] using (Set.DefinableFun.proj LRV (i := i))

/-- Naming singleton DC codes and naming their uniquely determined points
give exactly the same definable sets, over the original real/Gamma base. -/
theorem definableOverSingletonDiscNames_iff (B : ParameterBase M) {n m : ℕ}
    (a : Fin n → VF M) (sn : Fin m → SortTag) (A : Set (Fin m → M)) :
    DefinableOverSingletonDiscNames B a sn A ↔
      GammaParameters.DefinableOverBase (tupleBase B (SpecialTransformations.Section4.vfValues a)) sn A := by
  constructor
  · rintro ⟨R, rfl⟩
    let E := tupleBase B (SpecialTransformations.Section4.vfValues a)
    let T : Set M := E.real
    let c : Fin n → M := SpecialTransformations.Section4.vfValues a
    have hc (i : Fin n) : c i ∈ T := Or.inr (Set.mem_range_self i)
    have hf : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _
        T (fun x : Fin m → M => Fin.append c x) := by
      let N := CanonicalStructure.normalize (M := M)
      exact @append_constants_definable M N T n m c hc
    let Q := gammaRelationPreimageMap (R.relation.monoReal Set.subset_union_left) sn
      (fun x : Fin m → M => Fin.append c x) hf
    refine ⟨R.supportArity, R.support, R.support_mem, Q, ?_⟩
    ext x
    change (_ ∈ R.relation.fibre R.support ∧ x ∈ GammaParameters.sortedUniverse sn) ↔ _
    constructor
    · exact And.left
    · intro hx
      refine ⟨hx, fun i => ?_⟩
      simpa only [Fin.append_right] using R.relation.fibre_proper R.support _ hx (Fin.natAdd n i)
  · intro hA
    obtain ⟨P, hP, hrow⟩ := promote_tuple_definable_base B (fun _ : Fin n => .vf)
      (SpecialTransformations.Section4.vfValues a) (fun i => (a i).property) sn A hA
    obtain ⟨k, γ, hγ, Q, hQ⟩ := hP
    let R : SingletonDiscTupleRelation B n sn := ⟨k, γ, hγ, Q⟩
    refine ⟨R, ?_⟩
    ext x
    change Fin.append (SpecialTransformations.Section4.vfValues a) x ∈ Q.fibre γ ↔ x ∈ A
    rw [hQ]
    exact hrow x

def namedSingletonPolydisc {n : ℕ} (a : Fin n → VF M) : Set (Fin n → M) :=
  {x | ∀ i, x i ∈ BallImaginaries.underlying (singletonDiscTupleNames a i)}

theorem namedSingletonPolydisc_eq {n : ℕ} (a : Fin n → VF M) :
    namedSingletonPolydisc a = {SpecialTransformations.Section4.vfValues a} := by
  ext x
  simp only [namedSingletonPolydisc, singletonDiscTupleNames, closedDiscCode_infinity_underlying,
    Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

def IsAtomicOverSingletonDiscNames (B : ParameterBase M) {n m : ℕ} (a : Fin n → VF M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  DefinableOverSingletonDiscNames B a sn A ∧ A.Nonempty ∧
    A ⊆ GammaParameters.sortedUniverse sn ∧
    ∀ C, DefinableOverSingletonDiscNames B a sn C → A ⊆ C ∨ Disjoint A C

/-- The all-singleton closed-polydisc case, over its actual singleton names.
It needs no external atomicity input or nontrivial ground Gamma. -/
theorem singletonPolydisc_atomic (B : ParameterBase M) {n : ℕ} (a : Fin n → VF M) :
    IsAtomicOverSingletonDiscNames B a (fun _ : Fin n => .vf) (namedSingletonPolydisc a) := by
  rw [namedSingletonPolydisc_eq]
  let E := tupleBase B (SpecialTransformations.Section4.vfValues a)
  have hname (i : Fin n) : GammaParameters.DefinableClosureAtBase E .vf (a i).val :=
    GammaParameters.real_definableAtBase E .vf {(a i).val}
      (definableClosureAt_of_mem (Or.inr (Set.mem_range_self i)) (a i).property)
  have hdef := GammaParameters.tuple_singleton_definable_base E (fun _ : Fin n => .vf)
    (SpecialTransformations.Section4.vfValues a) hname
  refine ⟨(definableOverSingletonDiscNames_iff B a _ _).mpr hdef,
    Set.singleton_nonempty _, ?_, ?_⟩
  · rintro x rfl i
    exact (a i).property
  · intro C _
    by_cases h : SpecialTransformations.Section4.vfValues a ∈ C
    · exact Or.inl (Set.singleton_subset_iff.mpr h)
    · exact Or.inr (Set.disjoint_singleton_left.mpr h)

end DiamondIntegral.Section2
