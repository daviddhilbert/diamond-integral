import «section 6».RowForms
import «section 6».GammaCodeLocus

/-! (Row-form version for Remark 6.20, replacing `GammaCodeLocus`.)
The membership locus of a row-valued function: the point together with
an element of its row, written after the RV labels. It is a definable set
with `q` extra RV coordinates, which is all the obstacle theorems need. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r q : ℕ} {S : Set M}

def gammaCodeLocusSetRow (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) : Set (Mixed M n (r+q)) :=
  {p | (p.1, p.2 ∘ Fin.castAdd q) ∈ A.carrier ∧ (p.2 ∘ Fin.natAdd r) ∈ ω (p.1, p.2 ∘ Fin.castAdd q)}

theorem gammaCodeLocusSetRow_definable (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) (hω : MixedRowGraphDefinable S A.carrier ω) :
    (rawMixedSpace (M := M) n (r+q)).Definable S (gammaCodeLocusSetRow A ω) := by
  let C := gammaCodeLocusSetRow A ω
  let idx : (Fin n ⊕ Fin r) ⊕ Fin q → Fin n ⊕ Fin (r+q) :=
    Sum.elim (Sum.elim Sum.inl (fun j => .inr (Fin.castAdd q j))) (fun k => .inr (Fin.natAdd r k))
  apply (mixed_definable_iff_values_image S C).mpr
  have hrel : S.Definable LRV ((rawMixedSpace (M := M) n r).relation (rawRVSpace (M := M) q)
      (fun x v => x ∈ A.carrier ∧ v ∈ ω x)) := hω
  convert hrel.preimage_comp idx using 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    have e1 : (mixedValues p ∘ idx) ∘ Sum.inl =
        mixedValues ((p.1, p.2 ∘ Fin.castAdd q) : Mixed M n r) := by
      funext i
      cases i <;> rfl
    have e2 : (mixedValues p ∘ idx) ∘ Sum.inr = rvValues (p.2 ∘ Fin.natAdd r) := by
      funext i
      rfl
    have hx : (mixedValues p ∘ idx) ∘ Sum.inl ∈ (rawMixedSpace (M := M) n r).domain :=
      e1 ▸ mixedValues_mem_domain _
    have hy : (mixedValues p ∘ idx) ∘ Sum.inr ∈ (rawRVSpace (M := M) q).domain := e2 ▸ ⟨_, rfl⟩
    have d1 : (rawMixedSpace (M := M) n r).decode ⟨_, hx⟩ = ((p.1, p.2 ∘ Fin.castAdd q) : Mixed M n r) :=
      mixedValues_injective ((mixedValues_decode _).trans e1)
    have d2 : (rawRVSpace (M := M) q).decode ⟨_, hy⟩ = p.2 ∘ Fin.natAdd r :=
      rvValues_injective ((rvValues_decode _).trans e2)
    refine ⟨hx, hy, ?_⟩
    rw [d1, d2]
    exact hp
  · rintro ⟨hx, hy, hA, hω'⟩
    let a := (rawMixedSpace (M := M) n r).decode ⟨_, hx⟩
    let v := (rawRVSpace (M := M) q).decode ⟨_, hy⟩
    have ha := mixedValues_decode (M := M) (n := n) (r := r) ⟨_, hx⟩
    have hv := rvValues_decode (M := M) (r := q) ⟨_, hy⟩
    let p : Mixed M n (r+q) := (a.1, Fin.append a.2 v)
    have hcast : p.2 ∘ Fin.castAdd q = a.2 := by
      funext i
      exact Fin.append_left a.2 v i
    have hnat : p.2 ∘ Fin.natAdd r = v := by
      funext i
      exact Fin.append_right a.2 v i
    refine ⟨p, ⟨?_, ?_⟩, ?_⟩
    · change (a.1, p.2 ∘ Fin.castAdd q) ∈ A.carrier
      rw [hcast]
      exact hA
    · change p.2 ∘ Fin.natAdd r ∈ ω (a.1, p.2 ∘ Fin.castAdd q)
      rw [hcast, hnat]
      exact hω'
    · funext i
      cases i with
      | inl i => exact congrFun ha (.inl i)
      | inr j =>
        refine Fin.addCases (fun j => ?_) (fun k => ?_) j
        · change (Fin.append a.2 v (Fin.castAdd q j)).val = z (.inr (Fin.castAdd q j))
          rw [Fin.append_left]
          exact congrFun ha (.inr j)
        · change (Fin.append a.2 v (Fin.natAdd r k)).val = z (.inr (Fin.natAdd r k))
          rw [Fin.append_right]
          exact congrFun hv k

def gammaCodeLocusRow (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) (hω : MixedRowGraphDefinable S A.carrier ω) :
    DefSet (rawMixedSpace (M := M) n (r+q)) S :=
  ⟨gammaCodeLocusSetRow A ω, gammaCodeLocusSetRow_definable A ω hω⟩

theorem gammaCodeLocus_at_row (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) (hω : MixedRowGraphDefinable S A.carrier ω)
    (x : Fin n → VF M) (u : Fin r → RVInfinity M) (v : Fin q → RVInfinity M) :
    (x, Fin.append u v) ∈ (gammaCodeLocusRow A ω hω).carrier ↔ (x,u) ∈ A.carrier ∧ v ∈ ω (x,u) := by
  have hcast : Fin.append u v ∘ Fin.castAdd q = u := by
    funext i
    exact Fin.append_left u v i
  have hnat : Fin.append u v ∘ Fin.natAdd r = v := by
    funext i
    exact Fin.append_right u v i
  show (x, Fin.append u v) ∈ gammaCodeLocusSetRow A ω ↔ _
  simp only [gammaCodeLocusSetRow, Set.mem_setOf_eq, hcast, hnat]

end DiamondIntegral.Section6
