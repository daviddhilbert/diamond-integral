import «section 3».GammaGroundMapPreimages
import «section 3».GammaGroundRVFamilyObjects
import «section 3».RVZeroStrata
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {m k : ℕ}
def gammaGroundRVZeroPattern (ground : GammaParameters.Base (M := M)) (Z : Set (Fin k)) :
    GammaGroundDefSet hc ground (rawRVSpace (M := M) k) :=
  GammaGroundDefSet.ofReal (rvZeroPattern ground.real Z)

variable {A : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)}

def gammaGroundRVPatternSource (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) (Z : Set (Fin k)) :
    GammaGroundDefSet hc ground (rawRVSpace (M := M) m) :=
  ⟨{x | ∃ a : A, a.val = x ∧ (f a).val ∈ (gammaGroundRVZeroPattern (hc := hc) ground Z).carrier},
    f.definable_preimage (gammaGroundRVZeroPattern (hc := hc) ground Z).definable⟩

theorem gammaGroundRVPatternSource_subset (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)))
    (Z : Set (Fin k)) : (gammaGroundRVPatternSource f Z).carrier ⊆ A.carrier := by
  rintro x ⟨a, rfl, _⟩
  exact a.property

def gammaGroundRVPatternMap (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) (Z : Set (Fin k)) :
    GammaGroundMap (gammaGroundRVPatternSource f Z) (gammaGroundRVZeroPattern (hc := hc) ground Z) :=
  (f.restrict (gammaGroundRVPatternSource_subset f Z)).corestrict (fun x => by
    obtain ⟨a, ha, hf⟩ := x.property
    have he : (GammaGroundMap.inclusion (gammaGroundRVPatternSource_subset f Z) x : A) = a := Subtype.ext ha.symm
    change (f (GammaGroundMap.inclusion (gammaGroundRVPatternSource_subset f Z) x)).val ∈ _
    rw [he]
    exact hf)

theorem gammaGroundRVPatternMap_finite
    (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) (hf : f.FiniteFibres)
    (Z : Set (Fin k)) : (gammaGroundRVPatternMap f Z).FiniteFibres := by
  intro b
  let inc := GammaGroundMap.inclusion (gammaGroundRVPatternSource_subset f Z)
  have hi : Function.Injective inc := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun x : A => x.val) he
  apply ((hf ⟨b.val, Set.mem_univ _⟩).preimage hi.injOn).subset
  intro a ha
  change gammaGroundRVPatternMap f Z a = b at ha
  change f (inc a) = ⟨b.val, Set.mem_univ _⟩
  exact Subtype.ext (congrArg (fun x : gammaGroundRVZeroPattern (hc := hc) ground Z => x.val) ha)

theorem gammaGroundZeroPattern_projection_injective (Z : Set (Fin k)) :
    Function.Injective (gammaGroundRVSelectCoordinates (Section2.zeroFaceChart Z).freeIndex (gammaGroundRVZeroPattern (hc := hc) ground Z)) := by
  let C := Section2.zeroFaceChart Z
  intro a b he
  have hp : C.project a.val = C.project b.val := congrArg Subtype.val he
  have hzero (x : gammaGroundRVZeroPattern (hc := hc) ground Z) :
      ∀ i, x.val (C.zeroIndex i) = Section2.rvZero M :=
    fun i => Subtype.ext ((x.property _).mpr (C.zero_mem i))
  apply Subtype.ext
  rw [← C.insert_project (Section2.rvZero M) a.val (hzero a),
    ← C.insert_project (Section2.rvZero M) b.val (hzero b), hp]

def gammaGroundRVNonzeroStratum
    (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) (hf : f.FiniteFibres)
    (Z : Set (Fin k)) : GammaGroundRVObject hc ground (Section2.zeroFaceChart Z).freeArity where
  arity := m
  domain := gammaGroundRVPatternSource f Z
  volume := (gammaGroundRVSelectCoordinates (Section2.zeroFaceChart Z).freeIndex (gammaGroundRVZeroPattern (hc := hc) ground Z)).comp
    (gammaGroundRVPatternMap f Z)
  finite := (GammaGroundMap.finiteFibres_of_injective (gammaGroundZeroPattern_projection_injective Z)).comp
    (gammaGroundRVPatternMap_finite f hf Z)
  nonzero a i h := (Section2.zeroFaceChart Z).free_not_mem i
    (((gammaGroundRVPatternMap f Z a).property _).mp h)

theorem gammaGroundRVNonzeroStratum_degree_le (Z : Set (Fin k)) :
    (Section2.zeroFaceChart Z).freeArity ≤ k := by
  let C := Section2.zeroFaceChart Z
  have hi : Function.Injective C.freeIndex := by
    intro i j he
    apply Fin.ext
    have h := congrArg Fin.val (C.coordinates.injective he)
    change C.zeroArity + i.val = C.zeroArity + j.val at h
    exact Nat.add_left_cancel h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective C.freeIndex hi

theorem gammaGroundRVPatternSource_partition
    (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) (a : A) :
    ∃! Z : Set (Fin k), a.val ∈ (gammaGroundRVPatternSource f Z).carrier := by
  let Z : Set (Fin k) := {i | ((f a).val i).val = iRVZero}
  refine ⟨Z, ⟨a, rfl, fun _ => Iff.rfl⟩, ?_⟩
  rintro W ⟨b, hb, hW⟩
  have he : b = a := Subtype.ext hb
  subst b
  exact Set.ext (fun i => (hW i).symm)

def gammaGroundRVStratifiedObject
    (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) (hf : f.FiniteFibres)
    (Z : Set (Fin k)) : Σ i : Fin (k + 1), GammaGroundRVObject hc ground i.val :=
  ⟨⟨(Section2.zeroFaceChart Z).freeArity, Nat.lt_succ_of_le (gammaGroundRVNonzeroStratum_degree_le Z)⟩,
    gammaGroundRVNonzeroStratum f hf Z⟩

def gammaGroundRVPatternTags (k : ℕ) : Fin (Fintype.card (Set (Fin k))) ≃ Set (Fin k) :=
  (Fintype.equivFin (Set (Fin k))).symm

def gammaGroundRVPatternFamily (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) :
    GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) m) :=
  ⟨Fintype.card (Set (Fin k)), fun i => gammaGroundRVPatternSource f (gammaGroundRVPatternTags k i)⟩

def gammaGroundRVPatternFold (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)))
    (a : (gammaGroundRVPatternFamily f).Carrier) : A :=
  GammaGroundMap.inclusion (gammaGroundRVPatternSource_subset f (gammaGroundRVPatternTags k a.1)) a.2

theorem gammaGroundRVPatternFold_bijective (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) :
    Function.Bijective (gammaGroundRVPatternFold f) := by
  constructor
  · intro x y he
    have hx : (gammaGroundRVPatternFold f x).val ∈ (gammaGroundRVPatternSource f (gammaGroundRVPatternTags k x.1)).carrier := x.2.property
    have hy : (gammaGroundRVPatternFold f x).val ∈ (gammaGroundRVPatternSource f (gammaGroundRVPatternTags k y.1)).carrier := by
      rw [he]
      exact y.2.property
    have htag := (gammaGroundRVPatternTags k).injective ((gammaGroundRVPatternSource_partition f (gammaGroundRVPatternFold f x)).unique hx hy)
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    change i = j at htag
    subst j
    have hab : a = b := Subtype.ext (congrArg (fun a : A => a.val) he)
    cases hab
    rfl
  · intro a
    obtain ⟨Z, hZ⟩ := (gammaGroundRVPatternSource_partition f a).exists
    let i := (gammaGroundRVPatternTags k).symm Z
    have hi : a.val ∈ (gammaGroundRVPatternSource f (gammaGroundRVPatternTags k i)).carrier := by
      change a.val ∈ (gammaGroundRVPatternSource f (gammaGroundRVPatternTags k ((gammaGroundRVPatternTags k).symm Z))).carrier
      rwa [Equiv.apply_symm_apply]
    exact ⟨⟨i, ⟨a.val, hi⟩⟩, Subtype.ext rfl⟩

/-- The original domain is definably the finite disjoint union of the
strata, not merely covered by their images. -/
def gammaGroundRVPatternCarrierEquiv (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) :
    (gammaGroundRVPatternFamily f).Carrier ≃ A := Equiv.ofBijective (gammaGroundRVPatternFold f) (gammaGroundRVPatternFold_bijective f)

theorem gammaGroundRVPatternCarrierEquiv_graph
    (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k))) (i : Fin (gammaGroundRVPatternFamily f).tags) :
    GammaGroundRelationDefinable hc ground (rawRVSpace (M := M) m) (rawRVSpace m)
      (fun x y => ∃ a : (gammaGroundRVPatternFamily f).piece i,
        a.val = x ∧ (gammaGroundRVPatternCarrierEquiv f ⟨i, a⟩).val = y) :=
  (GammaGroundMap.inclusion (gammaGroundRVPatternSource_subset f (gammaGroundRVPatternTags k i))).graph_definable

end DiamondIntegral.Section3
