import «section 4».GammaQuantifierLogic
import «section 4».GammaBaseExtension

/-! Fibres of Gamma relations are definable after naming exactly their
actual Gamma parameter tuple. Every RV code remains in the preimage. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFamilySlices
open GammaOrderLogic GammaRelationLogic GammaQuantifierLogic GammaBaseExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem slice_definable_base (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (y : Fin n → Values.Gamma (M := M)) :
    GammaDefinableOverBase (withGamma B (Set.range y)) {x | Fin.cons x y ∈ R} := by
  let B' := withGamma B (Set.range y)
  have hfix (i : Fin n) : GammaDefinable B'
      {z : Fin (n + 1) → Values.Gamma (M := M) | z i.succ = y i} :=
    preimage_definable_base B' _ ((unary_definable_iff B' {y i}).mpr
      (gammaName_extend B (Set.range y) (y i) (Set.mem_range_self i)))
      (fun _ : Fin 1 => i.succ)
  have hfixall := finite_iInter_definable_base B' _ hfix
  have hA := inter_definable_base B' R _ (gammaRelation_extend B (Set.range y) hR) hfixall
  have h := image_definable_base B' _ hA (fun _ : Fin 1 => (0 : Fin (n + 1)))
    (fun a b _ => Subsingleton.elim a b)
  apply (unary_definable_iff B' _).mp
  convert h using 1
  ext z
  change Fin.cons (z 0) y ∈ R ↔
    ∃ w ∈ R ∩ (⋂ i : Fin n, {z | z i.succ = y i}), w ∘ (fun _ => 0) = z
  constructor
  · intro hz
    refine ⟨Fin.cons (z 0) y, ⟨hz, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq, Fin.cons_succ, implies_true]
    · funext i
      exact congrArg z (Subsingleton.elim 0 i)
  · rintro ⟨w, ⟨hwR, hw⟩, he⟩
    have hzero : w 0 = z 0 := congrFun he 0
    have hs (i : Fin n) : w i.succ = y i := Set.mem_iInter.mp hw i
    have heq : Fin.cons (z 0) y = w := by
      funext i
      exact Fin.cases hzero.symm (fun j => (hs j).symm) i
    rwa [heq]

end DiamondIntegral.Section4.GammaFamilySlices
