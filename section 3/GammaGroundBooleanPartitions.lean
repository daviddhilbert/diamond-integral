import «section 3».GammaGroundFiniteCoverPartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P : Space LRV M} {N : ℕ}

/-- The finite Boolean atom of a definable domain for prescribed sets.
All atoms use the original ground and require no cover hypothesis. -/
def gammaGroundBooleanAtom (A : GammaGroundDefSet hc B P)
    (E : Fin N → GammaGroundDefSet hc B P) (b : Fin N → Bool) : GammaGroundDefSet hc B P where
  carrier := {x | x ∈ A.carrier ∧ ∀ i, x ∈ (E i).carrier ↔ b i = true}
  definable := by
    have hi : ∀ i, GammaGroundDefinable hc B P {x | x ∈ (E i).carrier ↔ b i = true} := by
      intro i
      cases hb : b i
      · exact (E i).definable.compl.congr (fun _ => by
          simp only [Bool.false_eq_true,iff_false,Set.mem_compl_iff,Set.mem_ofPred_eq])
      · exact (E i).definable.congr (fun _ => by simp only [iff_true,Set.mem_ofPred_eq])
    have h := GammaGroundDefinable.iInter hi
    apply A.definable.inter (h.congr ?_)
    intro x
    simp only [Set.mem_iInter]
    rfl

theorem gammaGroundBooleanAtom_subset (A : GammaGroundDefSet hc B P)
    (E : Fin N → GammaGroundDefSet hc B P) (b : Fin N → Bool) :
    (gammaGroundBooleanAtom A E b).carrier ⊆ A.carrier := fun _ h => h.1

theorem gammaGroundBooleanAtom_disjoint (A : GammaGroundDefSet hc B P)
    (E : Fin N → GammaGroundDefSet hc B P) (b c : Fin N → Bool) (hbc : b ≠ c) :
    Disjoint (gammaGroundBooleanAtom A E b).carrier (gammaGroundBooleanAtom A E c).carrier := by
  apply Set.disjoint_left.mpr
  intro x hb hc
  apply hbc
  funext i
  have h : b i = true ↔ c i = true := (hb.2 i).symm.trans (hc.2 i)
  cases hb' : b i <;> cases hc' : c i <;> simp_all

theorem gammaGroundBooleanAtom_cover (A : GammaGroundDefSet hc B P)
    (E : Fin N → GammaGroundDefSet hc B P) (x : P.Carrier) :
    x ∈ A.carrier ↔ ∃ b, x ∈ (gammaGroundBooleanAtom A E b).carrier := by
  constructor
  · intro hx
    exact ⟨(fun i => decide (x ∈ (E i).carrier)),hx,by intro i; simp only [decide_eq_true_eq]⟩
  · rintro ⟨b,hb⟩
    exact hb.1

/-- Selecting the true bit of one prescribed set gives exactly its
partition by the original atoms, when it lies in the domain. -/
theorem gammaGroundBooleanAtom_selected_cover (A : GammaGroundDefSet hc B P)
    (E : Fin N → GammaGroundDefSet hc B P) (i : Fin N)
    (hE : (E i).carrier ⊆ A.carrier) (x : P.Carrier) :
    x ∈ (E i).carrier ↔
      ∃ b : {b : Fin N → Bool // b i = true}, x ∈ (gammaGroundBooleanAtom A E b.val).carrier := by
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := (gammaGroundBooleanAtom_cover A E x).mp (hE hx)
    exact ⟨⟨b,(hb.2 i).mp hx⟩,hb⟩
  · rintro ⟨b,hb⟩
    exact (hb.2 i).mpr b.property
end DiamondIntegral.Section3
