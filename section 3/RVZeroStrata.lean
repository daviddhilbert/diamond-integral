import «section 3».RVCategories
import «section 3».FiniteFamilies
import «section 2».ZeroFaces
import Section4.RVCoordinates
import Section4.MapCorestrict

/-! Notation 3.9: a finite-to-one target in RV-infinity^k splits into
finitely many definable zero patterns. Deleting exactly the zero positions
gives genuine nonzero finite-to-one targets in degrees at most k. The
original domain labels and parameter base are unchanged. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {m k : ℕ}

def rvZeroPattern (S : Set M) (Z : Set (Fin k)) : DefSet (rawRVSpace (M := M) k) S where
  carrier := {t | ∀ i, (t i).val = iRVZero ↔ i ∈ Z}
  definable := by
    classical
    have hz : S.DefinableFun LRV (fun _ : Fin k → M => iRVZero) :=
      (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
          (show S.DefinableMap LRV (fun _ : Fin k → M => Fin.elim0) from fun i => i.elim0)
    have hp (i : Fin k) : S.Definable LRV {z : Fin k → M | z i = iRVZero ↔ i ∈ Z} := by
      have he := (Set.DefinableFun.proj LRV (A := S) (i := i)).ofPred_eq hz
      by_cases hi : i ∈ Z
      · simpa only [hi, iff_true] using he
      · simpa only [hi, iff_false, Set.compl_setOf] using he.compl
    have hall : S.Definable LRV {z : Fin k → M | ∀ i, z i = iRVZero ↔ i ∈ Z} := by
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite hp
    have hd := ((rawRVSpace (M := M) k).definable_domain S).inter hall
    change S.Definable LRV _
    convert hd using 1
    ext z
    constructor
    · rintro ⟨hz, ht⟩
      refine ⟨hz, ?_⟩
      change (∀ i, rvValues ((rawRVSpace k).decode ⟨z, hz⟩) i = iRVZero ↔ i ∈ Z) at ht
      rwa [rvValues_decode] at ht
    · rintro ⟨hz, ht⟩
      refine ⟨hz, ?_⟩
      change ∀ i, rvValues ((rawRVSpace k).decode ⟨z, hz⟩) i = iRVZero ↔ i ∈ Z
      rwa [rvValues_decode]

def rvSelectCoordinates {d : ℕ} (e : Fin d → Fin k)
    (A : DefSet (rawRVSpace (M := M) k) S) : Map A (DefSet.univ (rawRVSpace d) S) := by
  let F (z : Fin k → M) := z ∘ e
  have hd (c : (rawRVSpace (M := M) k).domain) :
      rvValues ((rawRVSpace k).decode c ∘ e) = F c.val := by
    funext i
    exact congrFun (rvValues_decode c) (e i)
  refine Map.ofCodes A (fun t => t ∘ e) F (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨(rawRVSpace k).decode c ∘ e, hd c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hd c).symm

variable {A : DefSet (rawRVSpace (M := M) m) S}

def rvPatternSource (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) (Z : Set (Fin k)) :
    DefSet (rawRVSpace (M := M) m) S :=
  ⟨{x | ∃ a : A, a.val = x ∧ (f a).val ∈ (rvZeroPattern S Z).carrier},
    f.definable_preimage (rvZeroPattern S Z).definable⟩

theorem rvPatternSource_subset (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S))
    (Z : Set (Fin k)) : (rvPatternSource f Z).carrier ⊆ A.carrier := by
  rintro x ⟨a, rfl, _⟩
  exact a.property

def rvPatternMap (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) (Z : Set (Fin k)) :
    Map (rvPatternSource f Z) (rvZeroPattern S Z) :=
  (f.restrict (rvPatternSource_subset f Z)).corestrict (fun x => by
    obtain ⟨a, ha, hf⟩ := x.property
    have he : (Map.inclusion (rvPatternSource_subset f Z) x : A) = a := Subtype.ext ha.symm
    change (f (Map.inclusion (rvPatternSource_subset f Z) x)).val ∈ _
    rw [he]
    exact hf)

theorem rvPatternMap_finite
    (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) (hf : f.FiniteFibres)
    (Z : Set (Fin k)) : (rvPatternMap f Z).FiniteFibres := by
  intro b
  let inc := Map.inclusion (rvPatternSource_subset f Z)
  have hi : Function.Injective inc := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun x : A => x.val) he
  apply ((hf ⟨b.val, Set.mem_univ _⟩).preimage hi.injOn).subset
  intro a ha
  change rvPatternMap f Z a = b at ha
  change f (inc a) = ⟨b.val, Set.mem_univ _⟩
  exact Subtype.ext (congrArg (fun x : rvZeroPattern (M := M) S Z => x.val) ha)

theorem zeroPattern_projection_injective (Z : Set (Fin k)) :
    Function.Injective (rvSelectCoordinates (Section2.zeroFaceChart Z).freeIndex (rvZeroPattern S Z)) := by
  let C := Section2.zeroFaceChart Z
  intro a b he
  have hp : C.project a.val = C.project b.val := congrArg Subtype.val he
  have hzero (x : rvZeroPattern (M := M) S Z) :
      ∀ i, x.val (C.zeroIndex i) = Section2.rvZero M :=
    fun i => Subtype.ext ((x.property _).mpr (C.zero_mem i))
  apply Subtype.ext
  rw [← C.insert_project (Section2.rvZero M) a.val (hzero a),
    ← C.insert_project (Section2.rvZero M) b.val (hzero b), hp]

def rvNonzeroStratum
    (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) (hf : f.FiniteFibres)
    (Z : Set (Fin k)) : RVObject S (Section2.zeroFaceChart Z).freeArity where
  arity := m
  domain := rvPatternSource f Z
  volume := (rvSelectCoordinates (Section2.zeroFaceChart Z).freeIndex (rvZeroPattern S Z)).comp
    (rvPatternMap f Z)
  finite := (Map.finiteFibres_of_injective (zeroPattern_projection_injective Z)).comp
    (rvPatternMap_finite f hf Z)
  nonzero a i h := (Section2.zeroFaceChart Z).free_not_mem i
    (((rvPatternMap f Z a).property _).mp h)

theorem rvNonzeroStratum_degree_le (Z : Set (Fin k)) :
    (Section2.zeroFaceChart Z).freeArity ≤ k := by
  let C := Section2.zeroFaceChart Z
  have hi : Function.Injective C.freeIndex := by
    intro i j he
    apply Fin.ext
    have h := congrArg Fin.val (C.coordinates.injective he)
    change C.zeroArity + i.val = C.zeroArity + j.val at h
    exact Nat.add_left_cancel h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective C.freeIndex hi

theorem rvPatternSource_partition
    (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) (a : A) :
    ∃! Z : Set (Fin k), a.val ∈ (rvPatternSource f Z).carrier := by
  let Z : Set (Fin k) := {i | ((f a).val i).val = iRVZero}
  refine ⟨Z, ⟨a, rfl, fun _ => Iff.rfl⟩, ?_⟩
  rintro W ⟨b, hb, hW⟩
  have he : b = a := Subtype.ext hb
  subst b
  exact Set.ext (fun i => (hW i).symm)

def rvStratifiedObject
    (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) (hf : f.FiniteFibres)
    (Z : Set (Fin k)) : Σ i : Fin (k + 1), RVObject S i.val :=
  ⟨⟨(Section2.zeroFaceChart Z).freeArity, Nat.lt_succ_of_le (rvNonzeroStratum_degree_le Z)⟩,
    rvNonzeroStratum f hf Z⟩

def rvPatternTags (k : ℕ) : Fin (Fintype.card (Set (Fin k))) ≃ Set (Fin k) :=
  (Fintype.equivFin (Set (Fin k))).symm

def rvPatternFamily (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) :
    FiniteFamily (rawRVSpace (M := M) m) S :=
  ⟨Fintype.card (Set (Fin k)), fun i => rvPatternSource f (rvPatternTags k i)⟩

def rvPatternFold (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S))
    (a : (rvPatternFamily f).Carrier) : A :=
  Map.inclusion (rvPatternSource_subset f (rvPatternTags k a.1)) a.2

theorem rvPatternFold_bijective (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) :
    Function.Bijective (rvPatternFold f) := by
  constructor
  · intro x y he
    have hx : (rvPatternFold f x).val ∈ (rvPatternSource f (rvPatternTags k x.1)).carrier := x.2.property
    have hy : (rvPatternFold f x).val ∈ (rvPatternSource f (rvPatternTags k y.1)).carrier := by
      rw [he]
      exact y.2.property
    have htag := (rvPatternTags k).injective ((rvPatternSource_partition f (rvPatternFold f x)).unique hx hy)
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    change i = j at htag
    subst j
    have hab : a = b := Subtype.ext (congrArg (fun a : A => a.val) he)
    cases hab
    rfl
  · intro a
    obtain ⟨Z, hZ⟩ := (rvPatternSource_partition f a).exists
    let i := (rvPatternTags k).symm Z
    have hi : a.val ∈ (rvPatternSource f (rvPatternTags k i)).carrier := by
      change a.val ∈ (rvPatternSource f (rvPatternTags k ((rvPatternTags k).symm Z))).carrier
      rwa [Equiv.apply_symm_apply]
    exact ⟨⟨i, ⟨a.val, hi⟩⟩, Subtype.ext rfl⟩

/-- The original domain is definably the finite disjoint union of the
strata, not merely covered by their images. -/
def rvPatternCarrierEquiv (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) :
    (rvPatternFamily f).Carrier ≃ A := Equiv.ofBijective (rvPatternFold f) (rvPatternFold_bijective f)

theorem rvPatternCarrierEquiv_graph
    (f : Map A (DefSet.univ (rawRVSpace (M := M) k) S)) (i : Fin (rvPatternFamily f).tags) :
    (rawRVSpace (M := M) m).RelationDefinable (rawRVSpace m) S
      (fun x y => ∃ a : (rvPatternFamily f).piece i,
        a.val = x ∧ (rvPatternCarrierEquiv f ⟨i, a⟩).val = y) :=
  (Map.inclusion (rvPatternSource_subset f (rvPatternTags k i))).graph_definable

end DiamondIntegral.Section3
