import «section 3».DefinableBijections
import «section 2».Dimension
import Section4.RealPresentations

/-! Definition 3.4 (`defn:VF:cat`) at a fixed real parameter base. The
dimension is the section 2 coordinate-interior definition, including bottom
for the empty set. All RV fibres are finite. The topology is an explicit
parameter here and is specialized to the valuation topology in applications. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [TopologicalSpace (Section2.VF M)]

structure VFObject (S : Set M) (k : ℕ) where
  vfArity : ℕ
  rvArity : ℕ
  domain : DefSet (rawMixedSpace (M := M) vfArity rvArity) S
  dimension : Section2.vfDimension domain.carrier ≤ (k : WithBot ℕ)
  finite : ∀ a : Fin vfArity → Section2.VF M, {t | (a, t) ∈ domain.carrier}.Finite

variable {S : Set M} {k : ℕ}

noncomputable instance : Groupoid (VFObject (M := M) S k) where
  Hom U V := DefinableBijection U.domain V.domain
  id U := DefinableBijection.id U.domain
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  comp_id f := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  assoc f g h := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  inv_comp f := by apply DefinableBijection.ext; apply Map.ext; intro a; exact f.apply_symm_apply a
  comp_inv f := by apply DefinableBijection.ext; apply Map.ext; intro a; exact f.symm_apply_apply a

def VFObject.raise (U : VFObject (M := M) S k) {l : ℕ} (hkl : k ≤ l) : VFObject S l :=
  { U with dimension := U.dimension.trans (by exact_mod_cast hkl) }

theorem vf_dimension_le_arity {n m : ℕ} (A : Set (Section2.Mixed M n m)) :
    Section2.vfDimension A ≤ (n : WithBot ℕ) := by
  classical
  apply Finset.sup_le
  intro i _
  split_ifs with h
  · exact_mod_cast Nat.le_of_lt_succ i.isLt
  · exact bot_le

/-- Every finite-RV-fibre mixed definable set has an ambient degree bound. -/
def vfObjectOfFiniteFibres {n m : ℕ} (A : DefSet (rawMixedSpace (M := M) n m) S)
    (hf : ∀ a : Fin n → Section2.VF M, {t | (a, t) ∈ A.carrier}.Finite) :
    VFObject S n := ⟨n, m, A, vf_dimension_le_arity A.carrier, hf⟩

theorem hasVFInteriorDim_mono {n m d : ℕ} {A B : Set (Section2.Mixed M n m)}
    (hAB : A ⊆ B) (hA : Section2.HasVFInteriorDim A d) : Section2.HasVFInteriorDim B d := by
  obtain ⟨e, t, a, ha⟩ := hA
  refine ⟨e, t, a, ?_⟩
  have hf : Section2.vfFibre A t ⊆ Section2.vfFibre B t := fun _ hx => hAB hx
  exact interior_mono (Set.image_mono hf) ha

theorem vf_dimension_mono {n m : ℕ} {A B : Set (Section2.Mixed M n m)} (hAB : A ⊆ B) :
    Section2.vfDimension A ≤ Section2.vfDimension B := by
  classical
  apply Finset.sup_le
  intro i _
  split_ifs with h
  · exact Section2.HasVFInteriorDim.le_dimension (hasVFInteriorDim_mono hAB h)
  · exact bot_le

def VFObject.restrict (U : VFObject (M := M) S k)
    (A : DefSet (rawMixedSpace (M := M) U.vfArity U.rvArity) S)
    (hA : A.carrier ⊆ U.domain.carrier) : VFObject S k where
  vfArity := U.vfArity
  rvArity := U.rvArity
  domain := A
  dimension := (vf_dimension_mono hA).trans U.dimension
  finite a := (U.finite a).subset (fun _ hx => hA hx)

noncomputable def VFObject.empty (S : Set M) (k : ℕ) : VFObject (M := M) S k where
  vfArity := 0
  rvArity := 0
  domain := DefSet.empty (rawMixedSpace 0 0) S
  dimension := by
    change Section2.vfDimension (∅ : Set (Section2.Mixed M 0 0)) ≤ (k : WithBot ℕ)
    rw [Section2.vfDimension_empty]
    exact bot_le
  finite _ := Set.finite_empty

end DiamondIntegral.Section3
