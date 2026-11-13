import «section 3».GammaGroundRVFiniteValueFibres
import «section 3».GammaFixedPrefixProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- The identity Gamma point is definable over every original mixed base. -/
theorem gammaDefinableClosure_one (B : Base (M := M)) :
    GammaDefinableClosureAtBase B (1 : Values.Gamma (M := M)) :=
  (gammaScalar_definable_iff_native B {1}).mpr (FullGammaSyntax.one_definable (integrationGammaBase B))

/-- Translate a native Gamma set by a definable Gamma tuple. Its
first-order definition uses the Gamma tuple, without an RV lift. -/
def gammaGroundGammaTranslate (G : GammaGroundGammaPiece hc B n)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) :
    GammaGroundGammaPiece hc B n := by
  let f (i : Fin n) (η : Fin n → Values.Gamma (M := M)) := (δ i)⁻¹ * η i
  have hf : ∀ i, FullGammaFunction (integrationGammaBase B) (f i) := fun i =>
    ((FullGammaFunction.constant (δ i) (integrationGammaDefinable (hδ i))).inv).mul
      (FullGammaFunction.proj (integrationGammaBase B) i)
  have hG := (gammaGroundGammaPower_definable_iff G.carrier).mp G.definable
  exact ⟨{η : Fin n → Values.Gamma (M := M) | (fun i => (δ i)⁻¹ * η i) ∈ G.carrier},
    gammaGroundGammaPower_predicate_definable _ (FullGammaFunction.substitute hG f hf)⟩

theorem gammaGroundGammaTranslate_shift (G : GammaGroundGammaPiece hc B n)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (γ : Fin n → Values.Gamma (M := M)) :
    γ ∈ G.carrier ↔ (fun i => δ i * γ i) ∈ (gammaGroundGammaTranslate G δ hδ).carrier := by
  change γ ∈ G.carrier ↔ (fun i => (δ i)⁻¹ * (δ i * γ i)) ∈ G.carrier
  have he : (fun i => (δ i)⁻¹ * (δ i * γ i)) = γ := funext (fun i => inv_mul_cancel_left _ _)
  rw [he]

theorem gammaGroundGammaTranslate_one (G : GammaGroundGammaPiece hc B n) :
    gammaGroundGammaTranslate G (fun _ => 1) (fun _ => gammaDefinableClosure_one B) = G := by
  apply gammaGroundDefSet_eq_of_carrier_eq
  ext γ
  change Fin n → Values.Gamma (M := M) at γ
  change ((fun i => (1 : Values.Gamma (M := M))⁻¹ * γ i) ∈ G.carrier) ↔ γ ∈ G.carrier
  simp only [inv_one,one_mul]

/-- Partial products of a value tuple will translate one coordinate at a time. -/
def gammaValuePrefix (δ : Fin n → Values.Gamma (M := M)) (k : ℕ) : Fin n → Values.Gamma (M := M) :=
  fun i => if i.val < k then δ i else 1

theorem gammaValuePrefix_definable (δ : Fin n → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) (k : ℕ) :
    ∀ i, GammaDefinableClosureAtBase B (gammaValuePrefix δ k i) := by
  intro i
  by_cases hi : i.val < k
  · simpa only [gammaValuePrefix,ite_eq_left hi] using hδ i
  · simpa only [gammaValuePrefix,ite_eq_right hi] using gammaDefinableClosure_one B

@[simp] theorem gammaValuePrefix_zero (δ : Fin n → Values.Gamma (M := M)) :
    gammaValuePrefix δ 0 = fun _ => 1 := by
  funext i
  simp only [gammaValuePrefix,Nat.not_lt_zero,ite_false]

@[simp] theorem gammaValuePrefix_all (δ : Fin n → Values.Gamma (M := M)) :
    gammaValuePrefix δ n = δ := by
  funext i
  exact ite_eq_left i.isLt
end DiamondIntegral.Section3
