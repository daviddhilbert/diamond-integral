import «section 8».TruncClasses
import «section 8».IsoLattice

/-! The trace on the concrete model of a set definable over the base of Section 8.

For a definable set `A` of mixed points of the ambient `P`, definable over `⟨G.real, ∅⟩`, its trace
`traceRaw A` is the set of raw tuples of the concrete model whose image under `e` codes a point of
`A`. It is definable over `ℂ((t))` (`traceRaw_definableOver`), and its concrete points are the
points `p` with `ePoint p ∈ A` (`mem_mixedSet_trace`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2 DiamondIntegral.Section3
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues

local instance transferStructure : LRV.Structure Carrier := canonicalInterpret
local instance transferModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient) {n l : ℕ}

theorem e_sort (σ : SortTag) (x : Carrier) : sortEval σ (P.e x) ↔ sortEval σ x := by
  cases σ with
  | vf =>
    have h := P.e.map_rel Rel.memVF ![x]
    have ht : (P.e ∘ (![x] : Fin 1 → Carrier)) = ![P.e x] := by funext i; fin_cases i; rfl
    rw [ht] at h
    exact h
  | rv =>
    have h := P.e.map_rel Rel.memRV ![x]
    have ht : (P.e ∘ (![x] : Fin 1 → Carrier)) = ![P.e x] := by funext i; fin_cases i; rfl
    rw [ht] at h
    exact h

/-- The image of a concrete field element. -/
def eVF (g : Ser) : VFType (M := P.N) := ⟨P.e (Sum.inl g), (e_sort P .vf _).mpr trivial⟩

/-- The image of a concrete RV element. -/
def eRV (r : RV) : CanonicalRV.RVSort P.N := ⟨P.e (Sum.inr r), (e_sort P .rv _).mpr not_false⟩

/-- The image of a concrete mixed point. -/
def ePoint (p : (Fin n → Ser) × (Fin l → RV)) : Mixed P.N n l :=
  (fun i => eVF P (p.1 i), fun j => eRV P (p.2 j))

/-- The trace of `A` on the concrete model. -/
def traceRaw (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) : Set (Fin (n + l) → Carrier) :=
  {z | P.e ∘ z ∘ finSumFinEquiv ∈ (rawMixedSpace (M := P.N) n l).preimage A.carrier}

theorem traceRaw_definable (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) :
    {c | baseCarrier c}.Definable LRV (traceRaw P A) := by
  let C : Set (Fin (n + l) → P.N) :=
    {w | w ∘ finSumFinEquiv ∈ (rawMixedSpace (M := P.N) n l).preimage A.carrier}
  have hC0 : (P.G.real : Set P.N).Definable LRV ((rawMixedSpace (M := P.N) n l).preimage A.carrier) :=
    A.definable
  have hC : (Set.range (P.e ∘ laurentCoefficientEnumeration)).Definable LRV C := by
    have h := hC0.preimage_comp (finSumFinEquiv : Fin n ⊕ Fin l → Fin (n + l))
    have hB : ((P.G.real : Set P.N)) = Set.range (P.e ∘ laurentCoefficientEnumeration) := P.hB
    exact hB ▸ h
  have h := (elementaryActualDefinableEquiv P.e laurentCoefficientEnumeration
    (⟨C, hC⟩ : LRV.DefinableSet _ (Fin (n + l)))).property
  have h' : (Set.range laurentCoefficientEnumeration).Definable LRV {x : Fin (n + l) → Carrier | P.e ∘ x ∈ C} := h
  rw [laurentCoefficientEnumeration_range] at h'
  exact h'

theorem traceRaw_sorted (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    {z : Fin (n + l) → Carrier} (hz : z ∈ traceRaw P A) (i : Fin (n + l)) :
    sortEval (mixedSorts n l i) (z i) := by
  obtain ⟨hdom, -⟩ := hz
  obtain ⟨⟨x, hx⟩, ⟨u, hu⟩⟩ := hdom
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have h := congrFun hx a
    have hs : mixedSorts n l (Fin.castAdd l a) = .vf := by simp [mixedSorts]
    rw [hs, ← e_sort P]
    change sortEval .vf (((P.e ∘ z ∘ finSumFinEquiv) ∘ Sum.inl) a)
    rw [← h]
    exact (x a).property
  · have h := congrFun hu b
    have hs : mixedSorts n l (Fin.natAdd n b) = .rv := by simp [mixedSorts]
    rw [hs, ← e_sort P]
    change sortEval .rv (((P.e ∘ z ∘ finSumFinEquiv) ∘ Sum.inr) b)
    rw [← h]
    exact (u b).property

/-- The trace is definable over `ℂ((t))` at the mixed sorts. -/
theorem traceRaw_definableOver (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)) :
    DefinableOver {c | baseCarrier c} (mixedSorts n l) (traceRaw P A) := by
  refine (definableOver_iff_normalized_raw _ _ _).mpr ⟨?_, fun z hz i => traceRaw_sorted P A hz i⟩
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical]
  exact traceRaw_definable P A

theorem mixedValues_ePoint (p : (Fin n → Ser) × (Fin l → RV)) :
    mixedValues (ePoint P p) = P.e ∘ mixedRaw p ∘ finSumFinEquiv := by
  funext a
  cases a with
  | inl i =>
    change P.e (Sum.inl (p.1 i)) = P.e (mixedRaw p (finSumFinEquiv (Sum.inl i)))
    rw [finSumFinEquiv_apply_left, mixedRaw, Fin.append_left]
  | inr j =>
    change P.e (Sum.inr (p.2 j)) = P.e (mixedRaw p (finSumFinEquiv (Sum.inr j)))
    rw [finSumFinEquiv_apply_right, mixedRaw, Fin.append_right]

/-- **The concrete points of the trace.** -/
theorem mem_mixedSet_trace (A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (p : (Fin n → Ser) × (Fin l → RV)) : p ∈ mixedSet (traceRaw P A) ↔ ePoint P p ∈ A.carrier := by
  change P.e ∘ mixedRaw p ∘ finSumFinEquiv ∈ (rawMixedSpace (M := P.N) n l).preimage A.carrier ↔ _
  rw [← mixedValues_ePoint]
  constructor
  · rintro ⟨_, h⟩
    rwa [decode_mixedValues] at h
  · intro h
    exact ⟨mixedValues_mem_domain _, by rwa [decode_mixedValues]⟩

end DiamondIntegral.Section8.Truncation
