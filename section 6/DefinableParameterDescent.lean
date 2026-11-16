import «section 6».GenericMeasuredRVLifting
import Section3.DefinableConstants

/-! Descent of complete finite-presentation graphs when every temporary
real parameter is individually definable over the original base. This
retains actual carriers and maps, rather than a normalized replacement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M}

theorem definable_finite_index_parameter_descent {ι : Type} [Finite ι]
    (C : Set (ι → M)) (hC : T.Definable LRV C)
    (hParams : ∀ b ∈ T, S.Definable₁ LRV {b}) : S.Definable LRV C := by
  letI : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have hFin : T.Definable LRV {x : Fin (Fintype.card ι) → M | x ∘ e ∈ C} := hC.preimage_comp e
  have hS := SpecialTransformations.DefinableConstants.eliminate_parameters _ hParams hFin
  convert hS.preimage_comp e.symm using 1
  ext x
  change x ∈ C ↔ (x ∘ e.symm) ∘ e ∈ C
  simp only [Function.comp_assoc,e.symm_comp_self,Function.comp_id]

def extendDefSetBase {P : SpecialTransformations.DefinableGeometry.Space LRV M}
    (hST : S ⊆ T) (A : DefSet P S) : DefSet P T := ⟨A.carrier,A.definable.mono P hST⟩

def extendMapBase {P Q : SpecialTransformations.DefinableGeometry.Space LRV M}
    {A : DefSet P S} {B : DefSet Q S} (hST : S ⊆ T) (f : Map A B) :
    Map (extendDefSetBase hST A) (extendDefSetBase hST B) := ⟨f,f.graph_definable.mono P Q hST⟩

def descendMapBase {P Q : SpecialTransformations.DefinableGeometry.Space LRV M}
    {A : DefSet P S} {B : DefSet Q S} (hST : S ⊆ T)
    (hParams : ∀ b ∈ T, S.Definable₁ LRV {b})
    (f : Map (extendDefSetBase hST A) (extendDefSetBase hST B)) : Map A B :=
  ⟨f,definable_finite_index_parameter_descent _ f.graph_definable hParams⟩

theorem descendMapBase_value {P Q : SpecialTransformations.DefinableGeometry.Space LRV M}
    {A : DefSet P S} {B : DefSet Q S} (hST : S ⊆ T)
    (hParams : ∀ b ∈ T, S.Definable₁ LRV {b})
    (f : Map (extendDefSetBase hST A) (extendDefSetBase hST B)) (p : A) :
    descendMapBase hST hParams f p = f p := rfl

end DiamondIntegral.Section6
