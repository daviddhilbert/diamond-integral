import «section 6».ContinuousRVTemplateOperations

/-! Exact actual values of the continuous template operations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6.ContinuousRVGraphTemplate
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r R n m : ℕ}

theorem reindexRV_value (T : ContinuousRVGraphTemplate (M := M) S p r n m) (σ : Fin r → Fin R)
    (a : Fin p → M) (ha : a ∈ T.good) (hNew : a ∈ (T.reindexRV σ).good) :
    (T.reindexRV σ).value a hNew=fun u => T.value a ha (u ∘ σ) :=
  (T.reindexRV σ).value_eq_of_rows a hNew _ (T.reindexRV_row σ a ha)

theorem zero_value (a : Fin p → M)
    (ha : a ∈ (zero (M := M) (S := S) (p := p) (r := r) (n := n) (m := m)).good) :
    zero.value a ha=fun _ _ _ => (0 : VF M) :=
  zero.value_eq_of_rows a ha _ (zero_row a)

theorem rvCases_value (T U : ContinuousRVGraphTemplate (M := M) S p r n m)
    (P : Set (Fin r → M)) (hP : S.Definable LRV P) (a : Fin p → M)
    (hT : a ∈ T.good) (hU : a ∈ U.good) (hNew : a ∈ (T.rvCases U P hP).good) :
    (T.rvCases U P hP).value a hNew=
      fun u x => if rvValues u ∈ P then T.value a hT u x else U.value a hU u x :=
  (T.rvCases U P hP).value_eq_of_rows a hNew _ (T.rvCases_row U P hP a hT hU)

end DiamondIntegral.Section6.ContinuousRVGraphTemplate
