import «section 3».DiagonalWeightFaithfulness
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Hom
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {Q : Type*} [CommGroup Q] {n m : ℕ}

/-- The exact finitely generated character group, without saturating
or dividing the original-ground value subgroup. -/
def diagonalWeightGroup (a : Fin n → Q) (b : Fin m → Q) : AddSubgroup (Additive Q) :=
  AddSubgroup.closure (Set.range (Additive.ofMul ∘ a) ∪ Set.range (Additive.ofMul ∘ b))

def sourceDiagonalWeights (a : Fin n → Q) (b : Fin m → Q) : Fin n → diagonalWeightGroup a b :=
  fun i => ⟨Additive.ofMul (a i),AddSubgroup.subset_closure (Or.inl (Set.mem_range_self i))⟩

def targetDiagonalWeights (a : Fin n → Q) (b : Fin m → Q) : Fin m → diagonalWeightGroup a b :=
  fun i => ⟨Additive.ofMul (b i),AddSubgroup.subset_closure (Or.inr (Set.mem_range_self i))⟩

def diagonalWeightGroupEmbedding (a : Fin n → Q) (b : Fin m → Q) :
    Multiplicative (diagonalWeightGroup a b) →* Q where
  toFun w := w.toAdd.val.toMul
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diagonalWeightGroupEmbedding_injective (a : Fin n → Q) (b : Fin m → Q) :
    Function.Injective (diagonalWeightGroupEmbedding a b) := by
  intro x y h
  exact Subtype.ext h

@[simp] theorem diagonalWeightGroupEmbedding_source (a : Fin n → Q) (b : Fin m → Q) (i : Fin n) :
    diagonalWeightGroupEmbedding a b (Multiplicative.ofAdd (sourceDiagonalWeights a b i)) = a i := rfl

@[simp] theorem diagonalWeightGroupEmbedding_target (a : Fin n → Q) (b : Fin m → Q) (i : Fin m) :
    diagonalWeightGroupEmbedding a b (Multiplicative.ofAdd (targetDiagonalWeights a b i)) = b i := rfl

/-- The displayed source and target weights generate this exact group,
including its torsion; no divisibility closure is introduced. -/
theorem diagonalWeightGroup_joint_generation (a : Fin n → Q) (b : Fin m → Q) :
    AddSubgroup.closure (Set.range (sourceDiagonalWeights a b) ∪ Set.range (targetDiagonalWeights a b)) = ⊤ := by
  let L := diagonalWeightGroup a b
  let T := AddSubgroup.closure (Set.range (sourceDiagonalWeights a b) ∪ Set.range (targetDiagonalWeights a b))
  apply AddSubgroup.map_injective (f := L.subtype) Subtype.val_injective
  change T.map L.subtype = (⊤ : AddSubgroup L).map L.subtype
  rw [AddMonoidHom.map_closure,AddSubgroup.map_top]
  have he : L.subtype '' (Set.range (sourceDiagonalWeights a b) ∪ Set.range (targetDiagonalWeights a b)) =
      Set.range (Additive.ofMul ∘ a) ∪ Set.range (Additive.ofMul ∘ b) := by
    rw [Set.image_union,← Set.range_comp,← Set.range_comp]
    rfl
  rw [he]
  exact (AddSubgroup.range_subtype L).symm

end DiamondIntegral.Section3
