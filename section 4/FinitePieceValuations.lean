import «section 4».Section3FiniteGammaChartBridge

/-! Inclusion-exclusion on finite native Gamma pieces follows from
disjoint additivity and uses no cancellation or embedding premise. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.FinitePieceValuations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

abbrev Piece (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (n : ℕ) :=
  {G : GammaGroundGammaPiece hc B n // G.carrier.Finite}

theorem scissor {R : Type*} [AddCommMonoid R] (v : Piece hc B n → R)
    (hp : ∀ G A D : Piece hc B n, A.val.carrier ⊆ G.val.carrier → D.val.carrier ⊆ G.val.carrier →
      Disjoint A.val.carrier D.val.carrier → (A.val.union D.val).carrier = G.val.carrier → v G = v A + v D)
    (A D U E : Piece hc B n)
    (hU : U.val.carrier = A.val.carrier ∪ D.val.carrier)
    (hE : E.val.carrier = A.val.carrier ∩ D.val.carrier) : v U + v E = v A + v D := by
  let X : Piece hc B n := ⟨D.val.sdiff A.val, D.property.subset (fun _ hx => hx.1)⟩
  have hA : A.val.carrier ⊆ U.val.carrier := by rw [hU]; exact Set.subset_union_left
  have hX : X.val.carrier ⊆ U.val.carrier := by intro x hx; rw [hU]; exact Or.inr hx.1
  have hd1 : Disjoint A.val.carrier X.val.carrier := Set.disjoint_left.mpr (fun _ ha hx => hx.2 ha)
  have hu1 : (A.val.union X.val).carrier = U.val.carrier := by
    ext x
    rw [hU]
    change (x ∈ A.val.carrier ∨ x ∈ D.val.carrier ∧ x ∉ A.val.carrier) ↔ x ∈ A.val.carrier ∨ x ∈ D.val.carrier
    tauto
  have hED : E.val.carrier ⊆ D.val.carrier := by rw [hE]; exact Set.inter_subset_right
  have hXD : X.val.carrier ⊆ D.val.carrier := fun _ hx => hx.1
  have hd2 : Disjoint E.val.carrier X.val.carrier := Set.disjoint_left.mpr (fun x he hx => hx.2 ((Set.ext_iff.mp hE x).mp he).1)
  have hu2 : (E.val.union X.val).carrier = D.val.carrier := by
    ext x
    change (x ∈ E.val.carrier ∨ x ∈ D.val.carrier ∧ x ∉ A.val.carrier) ↔ x ∈ D.val.carrier
    rw [hE]
    change (x ∈ A.val.carrier ∧ x ∈ D.val.carrier ∨ x ∈ D.val.carrier ∧ x ∉ A.val.carrier) ↔ x ∈ D.val.carrier
    tauto
  rw [hp U A X hA hX hd1 hu1, hp D E X hED hXD hd2 hu2]
  ac_rfl

end DiamondIntegral.Section4.FinitePieceValuations
