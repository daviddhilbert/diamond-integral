import «section 4».FieldDefinableRing
import Section4.ResiduePureFunctions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Tuple.Basic

/-! A finite family of equal-arity pure-field sets is represented by a
single pure-field set with one tag coordinate. Tags need not be named
over the manuscript's original parameter base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.FieldTaggedFamilies
variable {K I : Type} [Field K] {n : ℕ}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def domain (tag : I → K) (D : I → Set (Fin n → K)) : Set (Fin (n + 1) → K) :=
  {x | ∃ i, x 0 = tag i ∧ Fin.tail x ∈ D i}

theorem definable [Finite I] (tag : I → K) (D : I → Set (Fin n → K))
    (hD : ∀ i, PureDef (D i)) : PureDef (domain tag D) := by
  have hi (i : I) : PureDef {x : Fin (n + 1) → K | x 0 = tag i ∧ Fin.tail x ∈ D i} :=
    ((pure_proj (0 : Fin (n + 1))).eq_const (tag i)).inter ((hD i).preimage_comp Fin.succ)
  convert Set.definable_iUnion_of_finite hi using 1
  ext x
  simp only [domain, Set.mem_setOf_eq, Set.mem_iUnion]

def encode (tag : I → K) (D : I → Set (Fin n → K)) (y : Σ i, D i) : domain tag D :=
  ⟨Fin.cons (tag y.1) y.2.val, y.1, by simp, by simpa using y.2.property⟩

theorem encode_injective (tag : I → K) (htag : Function.Injective tag)
    (D : I → Set (Fin n → K)) : Function.Injective (encode tag D) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ he
  have hv := congrArg Subtype.val he
  have hij : i = j := htag (by simpa [encode] using congrFun hv 0)
  subst j
  have hxy : x = y := Subtype.ext (by
    have ht := congrArg Fin.tail hv
    simpa [encode] using ht)
  subst y
  rfl

theorem encode_surjective (tag : I → K) (D : I → Set (Fin n → K)) :
    Function.Surjective (encode tag D) := by
  intro x
  obtain ⟨i, hi, hx⟩ := x.property
  refine ⟨⟨i, ⟨Fin.tail x.val, hx⟩⟩, Subtype.ext ?_⟩
  change Fin.cons (tag i) (Fin.tail x.val) = x.val
  rw [← hi]
  exact Fin.cons_self_tail x.val

def equiv (tag : I → K) (htag : Function.Injective tag) (D : I → Set (Fin n → K)) :
    (Σ i, D i) ≃ domain tag D :=
  Equiv.ofBijective (encode tag D) ⟨encode_injective tag htag D, encode_surjective tag D⟩

def tag [Fintype I] [Infinite K] (i : I) : K :=
  Infinite.natEmbedding K (Fintype.equivFin I i).val

theorem tag_injective [Fintype I] [Infinite K] : Function.Injective (tag (K := K) (I := I)) := by
  intro i j he
  apply (Fintype.equivFin I).injective
  apply Fin.ext
  exact (Infinite.natEmbedding K).injective he

def chart [Finite I] (tag : I → K) (D : I → Set (Fin n → K))
    (hD : ∀ i, PureDef (D i)) : FieldDefinableRing.Chart K :=
  ⟨n + 1, domain tag D, definable tag D hD⟩

end DiamondIntegral.Section4.FieldTaggedFamilies
