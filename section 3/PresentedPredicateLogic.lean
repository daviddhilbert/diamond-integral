import Section4.DefinableGeometry
import Mathlib.Data.Set.Finite.Lattice
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] (P : Space L M) (S : Set M)

abbrev PresentedPredicateDefinable (φ : P.Carrier → Prop) : Prop := P.Definable S {x | φ x}

namespace PresentedPredicateDefinable
variable {P S} {φ ψ : P.Carrier → Prop}

theorem and (hφ : PresentedPredicateDefinable P S φ) (hψ : PresentedPredicateDefinable P S ψ) :
    PresentedPredicateDefinable P S (fun x => φ x ∧ ψ x) := Space.Definable.inter P hφ hψ

theorem or (hφ : PresentedPredicateDefinable P S φ) (hψ : PresentedPredicateDefinable P S ψ) :
    PresentedPredicateDefinable P S (fun x => φ x ∨ ψ x) := Space.Definable.union P hφ hψ

theorem not (hφ : PresentedPredicateDefinable P S φ) : PresentedPredicateDefinable P S (fun x => ¬ φ x) :=
  Space.Definable.compl P hφ

theorem congr (hφ : PresentedPredicateDefinable P S φ) (h : ∀ x, φ x ↔ ψ x) :
    PresentedPredicateDefinable P S ψ := by
  have he : {x | φ x} = {x | ψ x} := Set.ext h
  change P.Definable S {x | ψ x}
  rw [← he]
  exact hφ

theorem bool_pattern (hφ : PresentedPredicateDefinable P S φ) (b : Bool) :
    PresentedPredicateDefinable P S (fun x => φ x ↔ b = true) := by
  cases b
  · exact hφ.not.congr (fun _ => by simp)
  · exact hφ.congr (fun _ => by simp)

theorem forall_finite {ι : Type} [Finite ι] {F : ι → P.Carrier → Prop}
    (hF : ∀ i, PresentedPredicateDefinable P S (F i)) :
    PresentedPredicateDefinable P S (fun x => ∀ i, F i x) := by
  have hh : S.Definable L {z : P.Index → M | ∀ i, z ∈ P.preimage {x | F i x}} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite hF
  have hd := (P.definable_domain S).inter hh
  change S.Definable L (P.preimage {x | ∀ i, F i x})
  convert hd using 1
  ext z
  change (∃ hz : z ∈ P.domain, ∀ i, F i (P.decode ⟨z,hz⟩)) ↔
    (z ∈ P.domain ∧ ∀ i, ∃ hz : z ∈ P.domain, F i (P.decode ⟨z,hz⟩))
  exact ⟨fun ⟨hz,h⟩ => ⟨hz,fun i => ⟨hz,h i⟩⟩,fun ⟨hz,h⟩ => ⟨hz,fun i => (h i).choose_spec⟩⟩
end PresentedPredicateDefinable
end DiamondIntegral.Section3
