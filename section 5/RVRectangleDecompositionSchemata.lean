import «section 5».RVRectanglePieceSchemata
import «section 5».OriginalFinitePartitionValidity

/-! A complete finite RV rectangle package retains full disjoint
coverage, every product bijection and every Euler certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

structure RVRectangleDecompositionSchema (D : GammaDomainFormula B p a sp) where
  size : ℕ
  cells : Fin size → RVRectanglePieceSchema B p a sp

def RVRectangleDecompositionSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D) (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧ (∀ i, (W.cells i).Valid hc z) ∧
    (∀ x : Fin a → M, Fin.append z x ∈ D.val ↔ ∃ i, Fin.append z x ∈ (W.cells i).source.val) ∧
    ∀ i j, i ≠ j → ∀ x : Fin a → M,
      ¬ (Fin.append z x ∈ (W.cells i).source.val ∧ Fin.append z x ∈ (W.cells j).source.val)

theorem RVRectangleDecompositionSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D) :
    DefinableOverBase B sp {z | W.Valid hc z} := by
  have hc : OriginalSortedPredicate B sp (fun z => ∀ i, (W.cells i).Valid hc z) :=
    OriginalSortedPredicate.finite_all (fun i => OriginalSortedPredicate.of_definable ((W.cells i).valid_definable hc))
  have hp := original_finite_partition_validity_definable B sp (fun _ : Fin a => .rv)
    D.val (fun i => (W.cells i).source.val) D.property (fun i => (W.cells i).source.property)
  exact hc.conj hp

def RVRectangleDecompositionSchema.recode (R : GammaParameterRecode B p q sp sq)
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D) :
    RVRectangleDecompositionSchema (R.domain D) := ⟨W.size,fun i => (W.cells i).recode R⟩

theorem RVRectangleDecompositionSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) {D : GammaDomainFormula B p a sp}
    (W : RVRectangleDecompositionSchema D) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hD : R.DomainAgreement D z t) (hC : ∀ i, (W.cells i).RowAgreement R z t) :
    W.Valid hc z ↔ (W.recode R).Valid hc t := by
  constructor
  · rintro ⟨_,hvalid,hcover,hdis⟩
    refine ⟨ht,(fun i => ((W.cells i).recode_valid_iff hc R z t hz ht (hC i)).mp (hvalid i)),?_,?_⟩
    · intro x
      exact (hD x).symm.trans ((hcover x).trans (exists_congr (fun i => (hC i).1 x)))
    · intro i j hij x hboth
      exact hdis i j hij x ⟨((hC i).1 x).mpr hboth.1,((hC j).1 x).mpr hboth.2⟩
  · rintro ⟨_,hvalid,hcover,hdis⟩
    refine ⟨hz,(fun i => ((W.cells i).recode_valid_iff hc R z t hz ht (hC i)).mpr (hvalid i)),?_,?_⟩
    · intro x
      exact (hD x).trans ((hcover x).trans (exists_congr (fun i => ((hC i).1 x).symm)))
    · intro i j hij x hboth
      exact hdis i j hij x ⟨((hC i).1 x).mp hboth.1,((hC j).1 x).mp hboth.2⟩

end DiamondIntegral.Section5
