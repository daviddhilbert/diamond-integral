import «section 5».GraphDecompositionVarieties
import «section 5».VarietyImmersionPartitions

/-! The actual equivariant graph decomposition gives equal geometric
classes on its two sides. Both finite partition identities are derived
from closed/open scissors, including the common reduced fibre products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety
attribute [local instance] basicConstructibleCoordinate_reduced basicConstructibleCoordinate_finiteType
variable {n m : ℕ} {N : ℕ+} {w : Fin n → ℤ} {v : Fin m → ℤ}
variable {G : Set (Fin n ⊕ Fin m → ℂ)}

theorem EquivariantGraphDecomposition.source_class_partition
    (d : EquivariantGraphDecomposition N w v G) (i : d.source.index) :
    letI := d.target.finite
    objectClass (d.sourceVariety i) = ∑ j, objectClass (d.commonVariety i j) := by
  letI := d.target.finite
  letI (j : d.target.index) : IsImmersion (d.commonToSource i j).hom := (d.common_immersions i j).1
  exact objectClass_finite_immersed_partition (d.sourceVariety i)
    (fun j => d.commonVariety i j) (fun j => d.commonToSource i j)
    (certifiedCommon_left_partition d.source d.target i)

theorem EquivariantGraphDecomposition.target_class_partition
    (d : EquivariantGraphDecomposition N w v G) (j : d.target.index) :
    letI := d.source.finite
    objectClass (d.targetVariety j) = ∑ i, objectClass (d.commonVariety i j) := by
  letI := d.source.finite
  letI (k : d.index) := d.left_immersion k
  letI (i : d.source.index) : IsImmersion (d.commonToTarget i j).hom := (d.common_immersions i j).2
  exact objectClass_finite_immersed_partition (d.targetVariety j)
    (fun i => d.commonVariety i j) (fun i => d.commonToTarget i j)
    (certifiedCommon_right_partition
      (graph_branches_complex_compatible d.data G d.graph_contained d.forward_unique)
      (graph_branches_inverse_complex_compatible d.data G d.graph_contained d.inverse_unique)
      d.source d.target j)

theorem EquivariantGraphDecomposition.geometric_classes_eq
    (d : EquivariantGraphDecomposition N w v G) :
    letI := d.source.finite
    letI := d.target.finite
    (∑ i, objectClass (d.sourceVariety i)) = ∑ j, objectClass (d.targetVariety j) := by
  letI := d.source.finite
  letI := d.target.finite
  simp_rw [d.source_class_partition, d.target_class_partition]
  exact Finset.sum_comm

end DiamondIntegral.Section5
