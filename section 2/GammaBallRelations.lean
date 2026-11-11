import «section 2».PartitionEscape
import Section8.NeighbourhoodRelations

/-! Uniform open polydiscs with an actual Gamma input represented by all
its nonzero RV codes. The relation is invariant in the code's value. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rawGammaBallRelation (n : ℕ) : Set ((Fin n ⊕ Fin n) ⊕ Fin 1 → M) :=
  {z | GammaParameters.NonzeroRV (z (.inr 0)) ∧
    (∀ i, iVF (z (.inl (.inl i)))) ∧ (∀ i, iVF (z (.inl (.inr i)))) ∧
    ∀ i, ¬ iLe (iRv (iVFAdd (z (.inl (.inr i))) (iVFNeg (z (.inl (.inl i)))))) (z (.inr 0))}

theorem rawGammaBallRelation_definable (S : Set M) (n : ℕ) :
    S.Definable LRV (rawGammaBallRelation (M := M) n) := by
  let Z := (Fin n ⊕ Fin n) ⊕ Fin 1
  have hcmp (i : Fin n) : S.Definable LRV {z : Z → M |
      ¬ iLe (iRv (iVFAdd (z (.inl (.inr i))) (iVFNeg (z (.inl (.inl i)))))) (z (.inr 0))} := by
    let c (z : Z → M) := z (.inl (.inl i))
    let x (z : Z → M) := z (.inl (.inr i))
    let negc (z : Z → M) := iVFNeg (c z)
    let diff (z : Z → M) := iVFAdd (x z) (negc z)
    let r (z : Z → M) := iRv (diff z)
    have hn : S.DefinableFun LRV negc :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
        (show S.DefinableMap LRV (fun z : Z → M => ![c z]) from by
          intro j
          fin_cases j
          exact Set.DefinableFun.proj LRV)
    have hd : S.DefinableFun LRV diff :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
        (show S.DefinableMap LRV (fun z : Z → M => ![x z,negc z]) from by
          intro j
          fin_cases j
          · exact Set.DefinableFun.proj LRV
          · exact hn)
    have hr : S.DefinableFun LRV r :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
        (show S.DefinableMap LRV (fun z : Z → M => ![diff z]) from by
          intro j
          fin_cases j
          exact hd)
    exact ((GammaParameters.raw_le_definable S).preimage_map
      (show S.DefinableMap LRV (fun z : Z → M => ![r z,z (.inr 0)]) from by
        intro j
        fin_cases j
        · exact hr
        · exact Set.DefinableFun.proj LRV)).compl
  have h := ((GammaParameters.nonzero_rv_definable S).preimage_comp
    (fun _ : Fin 1 => (Sum.inr 0 : Z))).inter
    (((vfRawUniverse_definable S n).preimage_comp (fun i => (Sum.inl (.inl i) : Z))).inter
      (((vfRawUniverse_definable S n).preimage_comp (fun i => (Sum.inl (.inr i) : Z))).inter
        (Set.definable_iInter_of_finite hcmp)))
  convert h using 1
  ext z
  simp only [rawGammaBallRelation,Set.mem_inter_iff,Set.mem_preimage,Set.mem_iInter,
    Set.mem_ofPred_eq,vfRawUniverse,Function.comp_apply]
  rfl

theorem rawGammaBallRelation_iff {n : ℕ} (a x : Fin n → VF M) (t : M)
    (ht : GammaParameters.NonzeroRV t) :
    Sum.elim (Sum.elim (vfValues a) (vfValues x)) (fun _ : Fin 1 => t) ∈ rawGammaBallRelation n ↔
      x ∈ vfBall a (GammaParameters.codeValue t) := by
  change (GammaParameters.NonzeroRV t ∧ (∀ i, iVF (a i).val) ∧ (∀ i, iVF (x i).val) ∧ _) ↔ _
  rw [and_iff_right ht,and_iff_right (fun i => (a i).property),
    and_iff_right (fun i => (x i).property)]
  have hv : (GammaParameters.codeValue t).val = Values.vrv (⟨t,ht.1⟩ : RVInfinity M) := by
    rw [GammaParameters.codeValue,dite_eq_left ht]
    rfl
  apply forall_congr'
  intro i
  change (¬ iLe (rv M (x i - a i)).val t) ↔ (GammaParameters.codeValue t).val < vfValue (x i - a i)
  rw [← Values.vrv_le_iff (rv M (x i - a i)) (⟨t,ht.1⟩ : RVInfinity M),hv,not_le]
  rfl

end DiamondIntegral.Section2
