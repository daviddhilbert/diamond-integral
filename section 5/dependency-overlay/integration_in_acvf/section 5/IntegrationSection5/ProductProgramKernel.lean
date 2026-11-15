import IntegrationSection5.ProductContractionProgram

/-! The full product contraction has precisely the joint kernel of the
two prepared unary RV keys. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {b c m : ℕ}

theorem unary_contractionMap_eq_iff {A : DefSet (M := M) S 1 m}
    (T : HeadPreparation A) (a b : A) :
    T.contractionMap a = T.contractionMap b ↔ SameRV (T.map a).val (T.map b).val := by
  rw [T.contractionMap_eq_iff]
  exact ⟨And.right,fun h => ⟨fun j => j.elim0,h⟩⟩

namespace ProductContractionProgram
variable {H : DefSet (M := M) S 2 0} {AD AE : DefSet (M := M) S 1 0}
variable {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
variable {d : Map AD BD} {e : Map AE BE}

theorem kernel_formula (P : ProductContractionProgram (G := G) H AD AE BD BE d e) (a b : H) :
    P.program.toMap a = P.program.toMap b ↔
      SameRV (d (P.dSource a)).val (d (P.dSource b)).val ∧
        SameRV (e (P.eSource a)).val (e (P.eSource b)).val := by
  change P.tail.contractionMap (P.first.contractionMap a) =
    P.tail.contractionMap (P.first.contractionMap b) ↔ _
  rw [unary_contractionMap_eq_iff,
    lifted_unary_sameRV_iff P.tail.map P.tail.special P.retained_le P.tailProjection P.tail_cover,
    P.tail_square a,P.tail_square b]
  have hlabels (a : H) : (P.first.contractionMap a).val.2 = (headKey (P.first.map a).val).2 :=
    congrArg Prod.snd (headKeyMap_apply P.first.target (P.first.map a))
  rw [hlabels a,hlabels b,headKey_labels_projection_iff P.firstProjection P.firstProjection_bijective.2,
    P.first_square a,P.first_square b]
  exact and_comm

end ProductContractionProgram
end IntegrationInACVF.Section5
