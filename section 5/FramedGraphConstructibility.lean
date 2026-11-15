import «section 5».FramedMaps

/-! Complete original graphs, encoded as RV tuples, have invariant
constructible framed graphs. All source and target coordinates are kept. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section7
local instance framedGraphStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]
variable {n m : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})

def originalGraphRVSet (f : Map A B) :
    DefSet (rawRVSpace (M := Carrier) (n + m)) {c | baseCarrier c} where
  carrier := {z | f.graph (fun i => z (Fin.castAdd m i)) (fun j => z (Fin.natAdd n j))}
  definable := by
    let P := rawRVSpace (M := Carrier) n
    let Q := rawRVSpace (M := Carrier) m
    let G := P.relation Q f.graph
    have hrow (z : Fin (n + m) → CanonicalRV.RVSort Carrier) :
        rvValues z ∘ finSumFinEquiv ∈ G ↔
        f.graph (fun i => z (Fin.castAdd m i)) (fun j => z (Fin.natAdd n j)) := by
      have h := Space.relation_decode P Q f.graph
        ⟨rvValues (fun i => z (Fin.castAdd m i)), ⟨_, rfl⟩⟩
        ⟨rvValues (fun j => z (Fin.natAdd n j)), ⟨_, rfl⟩⟩
      rw [decode_rvValues, decode_rvValues] at h
      exact h
    have hg := f.graph_definable.preimage_comp (finSumFinEquiv : Fin n ⊕ Fin m → Fin (n + m))
    have hd := ((rawRVSpace (M := Carrier) (n + m)).definable_domain {c | baseCarrier c}).inter hg
    change {c | baseCarrier c}.Definable LRV _
    convert hd using 1
    ext z
    constructor
    · rintro ⟨hz, hf⟩
      refine ⟨hz, ?_⟩
      have hh := (hrow ((rawRVSpace (n + m)).decode ⟨z, hz⟩)).mpr hf
      rwa [rvValues_decode] at hh
    · rintro ⟨hz, hf⟩
      refine ⟨hz, (hrow ((rawRVSpace (n + m)).decode ⟨z, hz⟩)).mp ?_⟩
      rwa [rvValues_decode]

theorem original_graph_framed_constructible (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (f : Map A B) :
    FiniteInvariant N (Fin.append a b) (framedRVSet N (Fin.append a b) (originalGraphRVSet A B f)) ∧
      ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin (n + m)) (⊤ : Subfield ℂ))),
        IsConstructible C ∧ ∀ z : Fin (n + m) → ℂ,
          f.graph (fun i => rvTag (linePoint ((a i : ℚ) / (N : ℕ)) (z (Fin.castAdd m i))))
            (fun j => rvTag (linePoint ((b j : ℚ) / (N : ℕ)) (z (Fin.natAdd n j)))) ↔
            fieldTuplePrime (⊤ : Subfield ℂ) z ∈ C := by
  obtain ⟨hi, C, hC, he⟩ := finite_framed_RES_comparison N (Fin.append a b) (originalGraphRVSet A B f)
  refine ⟨hi, C, hC, fun z => ?_⟩
  have hh := he z
  change f.graph
    (fun i => rvTag (linePoint (((Fin.append a b (Fin.castAdd m i) : ℤ) : ℚ) / (N : ℕ)) (z (Fin.castAdd m i))))
    (fun j => rvTag (linePoint (((Fin.append a b (Fin.natAdd n j) : ℤ) : ℚ) / (N : ℕ)) (z (Fin.natAdd n j)))) ↔
      fieldTuplePrime (⊤ : Subfield ℂ) z ∈ C at hh
  simpa only [Fin.append_left, Fin.append_right] using hh

end DiamondIntegral.Section5.PuiseuxOriginal
