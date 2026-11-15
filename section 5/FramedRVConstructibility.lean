import «section 5».FramedResidueConstructibility
import «section 5».FiniteKummerDescent
import Section3.TupleCompactness

/-! Actual original-base RV sets in finite Kummer coordinates are invariant
constructible complex sets. Zero coordinates are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7
local instance framedModelStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem linePoint_mul_residue (q : ℚ) (c : ℂ) :
    rvMul (linePoint q 1) (residueLift c) = linePoint q c := by
  by_cases hc : c = 0
  · simp [linePoint, residueLift, hc, rvMul]
  · simp only [linePoint, residueLift, one_ne_zero, hc, ↓reduceDIte, rvMul]
    congr 1
    apply Prod.ext
    · exact mul_one _
    · exact Units.ext (one_mul c)

def framedRVSet {S : Set Carrier} {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) S) : Set (Fin n → ℂ) :=
  {x | (fun i => rvTag (finiteFrame N a x i)) ∈ A.carrier}

theorem framedRVSet_constructible {S : Set Carrier} {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) S) :
    ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin n) (⊤ : Subfield ℂ))),
      IsConstructible C ∧ ∀ x : Fin n → ℂ,
        x ∈ framedRVSet N a A ↔ fieldTuplePrime (⊤ : Subfield ℂ) x ∈ C := by
  let B : LRV.Substructure Carrier := ⊤
  let A' : DefSet (rawRVSpace (M := Carrier) n) (residueExtendedBase B ⊤) :=
    ⟨A.carrier, Set.Definable.mono A.definable (fun _ _ => Or.inl trivial)⟩
  let s : Fin n → CanonicalRV.RVSort Carrier :=
    fun i => rvTag (linePoint ((a i : ℚ) / (N : ℕ)) 1)
  have hs (i : Fin n) : s i ∈ extendedCoefficients B ⊤ :=
    extendedCoefficients_base B ⊤ trivial
  obtain ⟨C, hC, hmem⟩ := complex_normalized_residue_constructible B A' s hs
  refine ⟨C, hC, fun x => ?_⟩
  have he : residueScale s (complexResidueEquiv ∘ x) =
      fun i => rvTag (finiteFrame N a x i) := by
    funext i
    change s i * residueRV (complexResidue (x i)) = _
    rw [residueRV_complexResidue]
    change rvTag (linePoint _ 1) * rvTag (residueLift (x i)) = _
    rw [← rvTag_mul, linePoint_mul_residue]
    rfl
  have hz : residueZeroPattern s (complexResidueEquiv ∘ x) := by
    intro i hi
    have h := congrArg (fun r => taggedRVEquiv r) hi
    rw [← rvTag_zero] at h
    change linePoint ((a i : ℚ) / (N : ℕ)) 1 = none at h
    simp [linePoint] at h
  have hh := hmem x
  change (residueScale s (complexResidueEquiv ∘ x) ∈ A.carrier ∧
    residueZeroPattern s (complexResidueEquiv ∘ x)) ↔ _ at hh
  rw [he, and_iff_left hz] at hh
  exact hh

theorem rawRV_preimage_mem {S : Set Carrier} {n : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) S) (r : Fin n → CanonicalRV.RVSort Carrier) :
    rvValues r ∈ (rawRVSpace n).preimage A.carrier ↔ r ∈ A.carrier := by
  change (∃ hr, (rawRVSpace n).decode ⟨rvValues r, hr⟩ ∈ A.carrier) ↔ _
  constructor
  · rintro ⟨hr, h⟩
    simpa only [decode_rvValues] using h
  · intro hr
    exact ⟨⟨r, rfl⟩, by simpa only [decode_rvValues] using hr⟩

theorem framedRVSet_finiteInvariant {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) :
    FiniteInvariant N a (framedRVSet N a A) := by
  obtain ⟨φ, hφ⟩ := raw_definable_formula_tuple A.definable
  intro ζ x
  obtain ⟨η, hη⟩ := finiteRootProjection_surjective N ζ
  have he : η.val N = ζ.val := congrArg Subtype.val hη
  have h := original_formula_invariant η φ Subtype.val (fun c => c.property) (finiteFrame N a x)
  have hframe := finiteFrame_action N a η x
  rw [he] at hframe
  have hm (y : Fin n → ℂ) :
      φ.Realize Subtype.val (fun i => Sum.inr (finiteFrame N a y i)) ↔
        y ∈ framedRVSet N a A := by
    exact (hφ _).trans (rawRV_preimage_mem A (fun i => rvTag (finiteFrame N a y i)))
  have hframe' : (fun i => Sum.inr (rvAction η (finiteFrame N a x i)) : Fin n → Carrier) =
      fun i => Sum.inr (finiteFrame N a (weightedAction a ζ.val x) i) :=
    funext (fun i => congrArg Sum.inr (congrFun hframe i))
  rw [hframe'] at h
  exact (hm _).symm.trans (h.trans (hm _))

/-- The forward finite-level comparison on actual original-base sets. -/
theorem finite_framed_RES_comparison {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) :
    FiniteInvariant N a (framedRVSet N a A) ∧
      ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin n) (⊤ : Subfield ℂ))),
        IsConstructible C ∧ ∀ x : Fin n → ℂ,
          x ∈ framedRVSet N a A ↔ fieldTuplePrime (⊤ : Subfield ℂ) x ∈ C :=
  ⟨framedRVSet_finiteInvariant N a A, framedRVSet_constructible N a A⟩

end DiamondIntegral.Section5.PuiseuxOriginal
