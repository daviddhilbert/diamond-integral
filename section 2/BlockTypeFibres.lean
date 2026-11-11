import «section 2».TypeFibres

/-!
# Complete types after fixing a block of real coordinates

This is a logical parameter-promotion step used to separate singleton
closed-disc coordinates from finite-radius coordinates. It is local work;
the external results of [18, Section 3] remain accepted inputs.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem promote_tuple_definable_base (B : ParameterBase M) {p n : ℕ}
    (sp : Fin p → SortTag) (a : Fin p → M) (ha : ∀ i, sortEval (sp i) (a i))
    (sn : Fin n → SortTag) (C : Set (Fin n → M))
    (hC : GammaParameters.DefinableOverBase (tupleBase B a) sn C) :
    ∃ P : Set (Fin (p+n) → M), GammaParameters.DefinableOverBase B (Fin.append sp sn) P ∧
      ∀ x : Fin n → M, Fin.append a x ∈ P ↔ x ∈ C := by
  have hCproper := hC.proper
  obtain ⟨k, γ, hγ, Q, hQC⟩ := hC
  obtain ⟨H, hH, hInv, hHa⟩ := GammaParameters.promote_gamma_relation B.real a Q
  let sm := Fin.append sp sn
  let R : GammaParameters.Relation B.real k (p+n) sm := {
    carrier := {q | GammaParameters.Proper q.1 ∧ q.2 ∈ GammaParameters.sortedUniverse sm ∧
      (q.2 ∘ Fin.castAdd n, q.1, q.2 ∘ Fin.natAdd p) ∈ H}
    definable := by
      let Z := Fin k ⊕ Fin (p+n)
      let e : Fin p ⊕ (Fin k ⊕ Fin n) → Z := Sum.elim
        (fun i => .inr (Fin.castAdd n i))
        (Sum.elim Sum.inl (fun i => .inr (Fin.natAdd p i)))
      have hp := @Set.Definable.preimage_comp M B.real LRV (CanonicalStructure.normalize (M := M))
        (Fin k) Z Sum.inl _ (GammaParameters.proper_normalized_definable B.real)
      have hs := (definableOver_iff_normalized_raw B.real sm _).mp
        (GammaParameters.sortedUniverse_definable B.real sm)
      have hh := @Set.Definable.preimage_comp M B.real LRV (CanonicalStructure.normalize (M := M))
        (Fin p ⊕ (Fin k ⊕ Fin n)) Z e _ hH
      let N := CanonicalStructure.normalize (M := M)
      letI := N
      exact hp.inter ((hs.1.preimage_comp Sum.inr).inter hh)
    proper := fun _ h => ⟨h.1, h.2.1⟩
    invariant := by
      intro t u he z
      change (GammaParameters.Proper (GammaParameters.rawTuple t) ∧
          z ∈ GammaParameters.sortedUniverse sm ∧
          (z ∘ Fin.castAdd n, GammaParameters.rawTuple t, z ∘ Fin.natAdd p) ∈ H) ↔
        (GammaParameters.Proper (GammaParameters.rawTuple u) ∧
          z ∈ GammaParameters.sortedUniverse sm ∧
          (z ∘ Fin.castAdd n, GammaParameters.rawTuple u, z ∘ Fin.natAdd p) ∈ H)
      simp only [GammaParameters.rawTuple_proper, true_and]
      exact and_congr Iff.rfl (hInv _ _ t u he) }
  refine ⟨R.fibre γ, ⟨k, γ, hγ, R, rfl⟩, ?_⟩
  intro x
  have hleft : Fin.append a x ∘ Fin.castAdd n = a := by
    funext i
    simp only [Function.comp_apply, Fin.append_left]
  have hright : Fin.append a x ∘ Fin.natAdd p = x := by
    funext i
    simp only [Function.comp_apply, Fin.append_right]
  change (GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives γ)) ∧
    Fin.append a x ∈ GammaParameters.sortedUniverse sm ∧
    (Fin.append a x ∘ Fin.castAdd n, GammaParameters.rawTuple (GammaParameters.representatives γ),
      Fin.append a x ∘ Fin.natAdd p) ∈ H) ↔ x ∈ C
  rw [and_iff_right (GammaParameters.rawTuple_proper _), hleft, hright,
    hHa _ _ (GammaParameters.rawTuple_proper _)]
  change (_ ∧ x ∈ Q.fibre γ) ↔ x ∈ C
  rw [hQC]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_, hx⟩
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [sm, Fin.append_left] using ha i
    · simpa only [sm, Fin.append_right] using hCproper x hx i

theorem GeneratesCompleteType.block_fibre {B : ParameterBase M} {p n : ℕ}
    {sp : Fin p → SortTag} {sn : Fin n → SortTag} {A : Set (Fin (p+n) → M)}
    (hA : GeneratesCompleteType B (Fin.append sp sn) A) (a : Fin p → M)
    (hne : {x : Fin n → M | Fin.append a x ∈ A}.Nonempty) :
    GeneratesCompleteType (tupleBase B a) sn {x : Fin n → M | Fin.append a x ∈ A} := by
  have ha (i : Fin p) : sortEval (sp i) (a i) := by
    obtain ⟨x, hx⟩ := hne
    simpa only [Fin.append_left] using hA.2.1 hx (Fin.castAdd n i)
  refine ⟨hne, ?_, ?_⟩
  · intro x hx i
    simpa only [Fin.append_right] using hA.2.1 hx (Fin.natAdd p i)
  · intro C hC
    obtain ⟨P, hP, hrow⟩ := promote_tuple_definable_base B sp a ha sn C hC
    rcases hA.2.2 P hP with hsub | hdis
    · exact Or.inl (fun x hx => (hrow x).mp (hsub hx))
    · exact Or.inr (Set.disjoint_left.mpr (fun x hx hc =>
        Set.disjoint_left.mp hdis hx ((hrow x).mpr hc)))

end DiamondIntegral.Section2
