import IntegrationSection5.CoordinateCanonicalFibre
import Section5.ParameterExtension

/-! Every actual unary special bijection is special relative to its sole
VF coordinate, with the actual fibre witnesses and their parameter bases. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

def specialCastBoth {A A' : DefSet (M := M) S n m} {B B' : DefSet (M := M) S n l}
    (T : SpecialBijection A B) (hA : A = A') (hB : B = B') : SpecialBijection A' B' := by
  cases hA
  cases hB
  exact T

theorem specialCastBoth_val {A A' : DefSet (M := M) S n m} {B B' : DefSet (M := M) S n l}
    (T : SpecialBijection A B) (hA : A = A') (hB : B = B') (a : A') :
    ((specialCastBoth T hA hB).toMap a).val =
      (T.toMap ⟨a.val,by cases hA; exact a.property⟩).val := by
  cases hA
  cases hB
  rfl

theorem coordinateInsert_unary (u : Fin 1 → VF (M := M)) (p : Point (M := M) 1 m) :
    coordinateInsert 0 u p = p := by
  refine Prod.ext ?_ rfl
  funext j
  fin_cases j
  simp [coordinateInsert,vfAt]

theorem coordinateProject_unary (p : Point (M := M) 1 m) : coordinateProject 0 p = p := by
  refine Prod.ext ?_ rfl
  funext j
  fin_cases j
  rfl

theorem unary_specialRelative {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (T : SpecialBijection A B) : SpecialRelative T.toMap 0 := by
  refine ⟨unaryRelative_one T.toMap,?_⟩
  intro u
  let hSR : S ⊆ coordinateFibreBase S (0 : Fin 1) u := Set.subset_union_left
  have hA : extendBase A hSR = coordinateFibre A 0 u := by
    apply PresentedSet.eq_of_carrier_eq
    ext p
    change p ∈ carrier A ↔ coordinateInsert 0 u p ∈ carrier A
    rw [coordinateInsert_unary]
  have hB : extendBase B hSR = coordinateFibre B 0 u := by
    apply PresentedSet.eq_of_carrier_eq
    ext p
    change p ∈ carrier B ↔ coordinateInsert 0 u p ∈ carrier B
    rw [coordinateInsert_unary]
  let U := specialCastBoth (T.extendBase hSR) hA hB
  refine ⟨U,?_⟩
  intro p
  apply Subtype.ext
  rw [specialCastBoth_val]
  have hp := coordinateInsert_unary u p.val
  have hpA : p.val ∈ carrier A := hp ▸ p.property
  let a : A := ⟨p.val,hpA⟩
  have hpEq : (⟨coordinateInsert 0 u p.val,p.property⟩ : A) = a := Subtype.ext hp
  rw [coordinateFibreMap_apply,hpEq,coordinateProject_unary]
  exact T.chain.extendBase_apply hSR a

end IntegrationInACVF.Section5
