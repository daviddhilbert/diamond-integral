import «section 4».GammaOrdinaryFiniteSupportUnionPresentation
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual formal finite-union and product operations retain the chosen
Gamma degree and agree with addition/multiplication in the finite-union
ring. The empty family has class zero. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFiniteSupportUnionOperations
open GammaOrdinaryCharts GammaOrdinaryFiniteCharts GammaOrdinaryFiniteSupportUnionPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def empty (B : Base (M := M)) (n : ℕ) : Family B n := ⟨0, Fin.elim0⟩
def coproduct {B : Base (M := M)} {n : ℕ} (a b : Family B n) : Family B n :=
  ⟨a.size + b.size, Fin.addCases a.chart b.chart⟩
def product {B : Base (M := M)} {n m : ℕ} (a : Family B m) (b : Family B n) : Family B (n + m) :=
  ⟨a.size * b.size, fun p => GammaOrdinaryFiniteCharts.product (a.chart (finProdFinEquiv.symm p).1) (b.chart (finProdFinEquiv.symm p).2)⟩

theorem class_empty (B : Base (M := M)) (n : ℕ) : objectClass (empty B n) = 0 := by
  have hz : (∑ i : Fin 0, singleClass (Fin.elim0 i : FiniteChart B n)) = 0 := by simp
  exact (class_family (empty B n)).trans hz

theorem class_coproduct {B : Base (M := M)} {n : ℕ} (a b : Family B n) :
    objectClass (coproduct a b) = objectClass a + objectClass b := by
  rw [class_family, class_family a, class_family b]
  change (∑ i : Fin (a.size + b.size), singleClass (Fin.addCases a.chart b.chart i)) = _
  simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

theorem class_product {B : Base (M := M)} {n m : ℕ} (a : Family B m) (b : Family B n) :
    objectClass (product a b) = objectClass a * objectClass b := by
  rw [class_family, class_family a, class_family b]
  change (∑ p : Fin (a.size * b.size), singleClass (GammaOrdinaryFiniteCharts.product
    (a.chart (finProdFinEquiv.symm p).1) (b.chart (finProdFinEquiv.symm p).2))) = _
  have he := Equiv.sum_comp (finProdFinEquiv (m := a.size) (n := b.size)).symm
    (fun p : Fin a.size × Fin b.size => singleClass (GammaOrdinaryFiniteCharts.product (a.chart p.1) (b.chart p.2)))
  rw [he]
  simp only [Fintype.sum_prod_type, GammaOrdinaryFiniteSupportUnionPresentation.class_product, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end DiamondIntegral.Section4.GammaOrdinaryFiniteSupportUnionOperations
