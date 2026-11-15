import «section 5».OriginalValuePatternSets

/-! Every actual original-base finite-value RV set has a finite disjoint
partition into original-base pieces with finite Kummer frames. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance finiteFramePartitionsStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

structure PatternFraming {n : ℕ} (p : Fin n → WithTop ℚ) where
  level : ℕ+
  weights : Fin n → ℤ
  zeros : Set (Fin n)
  equation : ∀ i, p i = if i ∈ zeros then ⊤ else
    (((weights i : ℚ) / (level : ℕ) : ℚ) : WithTop ℚ)

theorem patternFraming_nonempty {n : ℕ} (p : Fin n → WithTop ℚ) : Nonempty (PatternFraming p) := by
  obtain ⟨N, a, ha⟩ := rational_tuple_common_level n (fun i => (p i).untopD 0)
  refine ⟨⟨N, a, {i | p i = ⊤}, fun i => ?_⟩⟩
  by_cases hi : p i = ⊤
  · simp only [Set.mem_ofPred_eq, hi, ↓reduceIte]
  · have hq : (((p i).untopD 0 : ℚ) : WithTop ℚ) = p i := by
      cases hp : p i with
      | top => exact (hi hp).elim
      | coe q => simp
    rw [if_neg (show i ∉ {j | p j = ⊤} from hi), ← hq, ha i]

def patternFraming {n : ℕ} (p : Fin n → WithTop ℚ) : PatternFraming p :=
  Classical.choice (patternFraming_nonempty p)

def patternSet {n : ℕ} (p : Fin n → WithTop ℚ) :
    DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c} :=
  originalValuePattern (patternFraming p).level (patternFraming p).weights (patternFraming p).zeros

theorem patternSet_mem_iff {n : ℕ} (p : Fin n → WithTop ℚ)
    (r : Fin n → CanonicalRV.RVSort Carrier) :
    r ∈ (patternSet p).carrier ↔ (fun i => value (taggedRVEquiv (r i))) = p := by
  rw [show (patternSet p).carrier = (originalValuePattern (patternFraming p).level
    (patternFraming p).weights (patternFraming p).zeros).carrier from rfl, originalValuePattern_mem_iff]
  rw [funext_iff]
  exact forall_congr' (fun i => by rw [(patternFraming p).equation i])

def patternPiece {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) (p : Fin n → WithTop ℚ) :
    DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c} where
  carrier := A.carrier ∩ (patternSet p).carrier
  definable := Space.Definable.inter _ A.definable (patternSet p).definable

theorem patternPiece_mem_iff {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (p : Fin n → WithTop ℚ) (r : Fin n → CanonicalRV.RVSort Carrier) :
    r ∈ (patternPiece A p).carrier ↔ r ∈ A.carrier ∧
      (fun i => value (taggedRVEquiv (r i))) = p :=
  and_congr Iff.rfl (patternSet_mem_iff p r)

theorem patternPiece_support {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) (p : Fin n → WithTop ℚ) :
    HasFrameSupport (patternFraming p).level (patternFraming p).weights (patternPiece A p) := by
  intro r hr i
  exact descendedOriginalSet_frameSupport (patternFraming p).level (patternFraming p).weights
    (complexZeroPattern (patternFraming p).zeros) (complexZeroPattern_definable _) r hr.2 i

theorem original_finite_frame_partition {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite) :
    ∃ I : Type, ∃ _ : Fintype I, ∃ N : I → ℕ+, ∃ a : I → Fin n → ℤ,
      ∃ pieces : I → DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c},
        (∀ i, HasFrameSupport (N i) (a i) (pieces i)) ∧
        Pairwise (fun i j => Disjoint (pieces i).carrier (pieces j).carrier) ∧
        ∀ r, r ∈ A.carrier ↔ ∃ i, r ∈ (pieces i).carrier := by
  have hf := (native_finite_value_patterns_iff A).mp hA
  let I := Set.range (fun u : A => fun i => value (taggedRVEquiv (u.val i)))
  letI : Fintype I := hf.fintype
  refine ⟨I, inferInstance, (fun p => (patternFraming p.val).level),
    (fun p => (patternFraming p.val).weights), (fun p => patternPiece A p.val), ?_, ?_, ?_⟩
  · exact fun p => patternPiece_support A p.val
  · intro p q hpq
    apply Set.disjoint_left.mpr
    intro r hr hs
    have hpr := (patternPiece_mem_iff A p.val r).mp hr
    have hqr := (patternPiece_mem_iff A q.val r).mp hs
    exact hpq (Subtype.ext (hpr.2.symm.trans hqr.2))
  · intro r
    constructor
    · intro hr
      let p : I := ⟨fun i => value (taggedRVEquiv (r i)), ⟨⟨r, hr⟩, rfl⟩⟩
      exact ⟨p, (patternPiece_mem_iff A p.val r).mpr ⟨hr, rfl⟩⟩
    · rintro ⟨p, hp⟩
      exact ((patternPiece_mem_iff A p.val r).mp hp).1

end DiamondIntegral.Section5.PuiseuxOriginal
