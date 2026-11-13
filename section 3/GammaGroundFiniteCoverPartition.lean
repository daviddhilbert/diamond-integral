import «section 3».GammaGroundFiniteUnions
import Mathlib.Data.Fintype.Pi
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {P : Space LRV M}

theorem GammaGroundDefinable.iInter {ι : Type} [Finite ι] {T : ι → Set P.Carrier}
    (hT : ∀ i, GammaGroundDefinable hc B P (T i)) :
    GammaGroundDefinable hc B P (⋂ i, T i) := by
  apply (GammaGroundDefinable.iUnion (fun i => (hT i).compl)).compl.congr
  intro x
  simp only [Set.mem_compl_iff,Set.mem_iUnion,Set.mem_iInter,not_exists,not_not]

/-- A finite same-ground cover refines to disjoint definable pieces.
Every nonempty piece is contained in one original cover member. -/
theorem gammaGround_finite_cover_partition (A : GammaGroundDefSet hc B P) {N : ℕ}
    (E : Fin N → GammaGroundDefSet hc B P)
    (hcover : ∀ x ∈ A.carrier, ∃ i, x ∈ (E i).carrier) :
    ∃ J : ℕ, ∃ Q : Fin J → GammaGroundDefSet hc B P,
      (∀ j, (Q j).carrier ⊆ A.carrier ∧ ((Q j).carrier = ∅ ∨ ∃ i, (Q j).carrier ⊆ (E i).carrier)) ∧
      (∀ i j, i ≠ j → Disjoint (Q i).carrier (Q j).carrier) ∧
      ∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (Q i).carrier := by
  let W : (Fin N → Bool) → GammaGroundDefSet hc B P := fun b => {
    carrier := {x | x ∈ A.carrier ∧ ∀ i, x ∈ (E i).carrier ↔ b i = true}
    definable := by
      have hi : ∀ i, GammaGroundDefinable hc B P {x | x ∈ (E i).carrier ↔ b i = true} := by
        intro i
        cases hb : b i
        · exact (E i).definable.compl.congr (fun _ => by simp only [hb,Bool.false_eq_true,iff_false,Set.mem_compl_iff,Set.mem_ofPred_eq])
        · exact (E i).definable.congr (fun _ => by simp only [hb,iff_true,Set.mem_ofPred_eq])
      have hh := GammaGroundDefinable.iInter hi
      have he : (⋂ i, {x | x ∈ (E i).carrier ↔ b i = true}) =
          {x | ∀ i, x ∈ (E i).carrier ↔ b i = true} := by
        ext x
        simp only [Set.mem_iInter,Set.mem_ofPred_eq]
      rw [he] at hh
      exact A.definable.inter hh }
  let e : Fin (Fintype.card (Fin N → Bool)) ≃ (Fin N → Bool) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Fin N → Bool),fun j => W (e j),?_,?_,?_⟩
  · intro j
    refine ⟨fun x hx => hx.1,?_⟩
    by_cases hb : ∃ i, e j i = true
    · obtain ⟨i,hi⟩ := hb
      exact Or.inr ⟨i,fun x hx => (hx.2 i).mpr hi⟩
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i,hi⟩ := hcover x hx.1
      exact hb ⟨i,(hx.2 i).mp hi⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    apply hij
    apply e.injective
    funext k
    have hb : e i k = true ↔ e j k = true := (hi.2 k).symm.trans (hj.2 k)
    cases h1 : e i k <;> cases h2 : e j k <;> simp_all
  · intro x
    constructor
    · intro hx
      let b : Fin N → Bool := fun i => decide (x ∈ (E i).carrier)
      obtain ⟨i,hi⟩ := e.surjective b
      refine ⟨i,hx,?_⟩
      intro k
      rw [hi]
      simp only [b,decide_eq_true_eq]
    · rintro ⟨i,hi⟩
      exact hi.1
end DiamondIntegral.Section3
