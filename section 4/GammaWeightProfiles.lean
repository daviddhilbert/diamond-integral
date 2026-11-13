import «section 4».GammaHigherPushforward
import «section 4».GammaDefinableMaps

/-! Corrected weight profiles for actual definable Gamma sets. The native
Gamma product is the manuscript's sum of coordinates. These are actual
function-valued profiles; descent to graded categories is a later theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaWeightProfiles
open GammaDefinableEuler GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaIndicators
open GammaDefinableMaps GammaHigherPushforward GammaIteratedIntegral

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem finset_prod_definable {ι : Type} (B : Base (M := M)) {n : ℕ} (s : Finset ι)
    (f : ι → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : ∀ i ∈ s, MapDefinable B (f i)) : MapDefinable B (fun z => ∏ i ∈ s, f i z) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using
      constant_definable (n := n) B 1 (GammaGroupNames.one_definable_base B)
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using mul_definable B _ _
      (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

def correctedWeight {n : ℕ}
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (z : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) := μ z * ∏ i, z i

theorem correctedWeight_definable (B : Base (M := M)) {n : ℕ}
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    MapDefinable B (correctedWeight μ) := by
  apply mul_definable B μ _ hμ
  exact finset_prod_definable B Finset.univ (fun i z => z i)
    (fun i _ => projection_definable B i)

def extendWeight {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M)))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (z : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) := if z ∈ I then μ z else 1

theorem extendWeight_definable (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
      Fin.tail z ∈ I ∧ z 0 = μ (Fin.tail z)}) : MapDefinable B (extendWeight I μ) := by
  have htail := GammaRelationLogic.preimage_definable_base B I hI Fin.succ
  have hnot := GammaRelationLogic.complement_definable_base B _ htail
  have hone := constant_definable (n := n) B 1 (GammaGroupNames.one_definable_base B)
  have h := GammaQuantifierLogic.union_definable_base B _ _ hμ
    (GammaRelationLogic.inter_definable_base B _ _ hnot hone)
  unfold MapDefinable
  convert h using 1
  ext z
  change z 0 = extendWeight I μ (fun i => z i.succ) ↔
    (Fin.tail z ∈ I ∧ z 0 = μ (Fin.tail z)) ∨ (¬(z ∘ Fin.succ ∈ I) ∧ z 0 = 1)
  have he : Fin.tail z = z ∘ Fin.succ := by funext i; rfl
  unfold extendWeight
  rw [he]
  have hcomp : z ∘ Fin.succ = (fun i => z i.succ) := by funext i; rfl
  rw [hcomp]
  by_cases hz : (fun i => z i.succ) ∈ I <;> simp [hz]

def profile (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    GammaDefinableConvolution.baseSubgroup B k :=
  pushforward h00 hκ hs B hr hγ k (correctedWeight μ) (by
    have h := correctedWeight_definable B μ hμ
    unfold MapDefinable at h
    convert h using 1
    ext z
    have he : Fin.tail z = (fun i => z i.succ) := by funext i; rfl
    change z 0 = correctedWeight μ (Fin.tail z) ↔ z 0 = correctedWeight μ (fun i => z i.succ)
    rw [he]) (indicatorFamily B I hI)

theorem profile_integral (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    EulerFunction.totalEuler k (profile h00 hκ hs B hr hγ k I hI μ hμ).val =
      integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B I hI) := by
  exact pushforward_integral h00 hκ hs B hr hγ k linear hΓ _ _ _

end DiamondIntegral.Section4.GammaWeightProfiles
