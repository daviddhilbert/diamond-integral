import «section 4».GammaOrdinaryEulerEvaluation
import «section 4».GammaOrdinaryGrading
import «section 4».GammaOrdinaryFiniteMaps
import «section 4».GammaOrdinaryEvaluation

/-! Ordinary Gamma Euler maps into ordinary reduced RES are graded and
balance over the entire ordinary finite-Gamma coefficient ring. The
proof descends the established finite balancing through the proved
surjective measured-forget map. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryRESEvaluation
open GammaOrdinaryCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def resMap (B : Base (M := M)) : GammaOrdinaryFiniteRing.Ring B →+* RESOrdinaryReduction.ReducedRing B :=
  (RESOrdinaryReduction.quotient B).comp (GammaOrdinaryFiniteMaps.sharp B)

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def evaluation (k : EulerKind) : GammaOrdinaryRing.Ring B →+* RESOrdinaryReduction.ReducedRing B :=
  GammaOrdinaryEulerEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ (RESOrdinaryReduction.torusClass B) k

theorem evaluation_class (k : EulerKind) {n : ℕ} (a : Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (GammaOrdinaryRing.objectClass a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n (GammaIndicators.indicatorFamily B a.support a.support_definable) : RESOrdinaryReduction.ReducedRing B) *
        RESOrdinaryReduction.torusClass B ^ n :=
  GammaOrdinaryEulerEvaluation.evaluation_class h00 linear hκ hs B hr hγ hΓ (RESOrdinaryReduction.torusClass B) k a

theorem evaluation_class_mem (k : EulerKind) {n : ℕ} (a : Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (GammaOrdinaryRing.objectClass a) ∈ RESReductionGradings.ordinaryPiece B n := by
  rw [evaluation_class]
  simpa only [zero_add] using SetLike.mul_mem_graded
    (RESPsiGradings.ordinary_intCast_mem B (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n (GammaIndicators.indicatorFamily B a.support a.support_definable)))
    (RESPsiGradings.ordinary_torus_pow_mem B n)

theorem evaluation_coaction (k : EulerKind) :
    (Polynomial.mapRingHom (evaluation h00 linear hκ hs B hr hγ hΓ k)).comp (GammaOrdinaryGrading.coaction B) =
      (RESReductionGradings.ordinaryCoaction B).map.comp (evaluation h00 linear hκ hs B hr hγ hΓ k) := by
  apply GammaOrdinaryRing.hom_ext B
  intro n a
  change (GammaOrdinaryGrading.coaction B (GammaOrdinaryRing.objectClass a)).map (evaluation h00 linear hκ hs B hr hγ hΓ k) =
    (RESReductionGradings.ordinaryCoaction B).map (evaluation h00 linear hκ hs B hr hγ hΓ k (GammaOrdinaryRing.objectClass a))
  rw [GammaOrdinaryGrading.coaction_class, Polynomial.map_monomial]
  exact (evaluation_class_mem h00 linear hκ hs B hr hγ hΓ k a).symm

theorem evaluation_mem (k : EulerKind) {n : ℕ} {x : GammaOrdinaryRing.Ring B} (hx : x ∈ GammaOrdinaryGrading.gradedPiece B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k x ∈ RESReductionGradings.ordinaryPiece B n := by
  change GammaOrdinaryGrading.coaction B x = Polynomial.monomial n x at hx
  change (RESReductionGradings.ordinaryCoaction B).map (evaluation h00 linear hκ hs B hr hγ hΓ k x) =
    Polynomial.monomial n (evaluation h00 linear hκ hs B hr hγ hΓ k x)
  have he := RingHom.congr_fun (evaluation_coaction h00 linear hκ hs B hr hγ hΓ k) x
  change (GammaOrdinaryGrading.coaction B x).map (evaluation h00 linear hκ hs B hr hγ hΓ k) =
    (RESReductionGradings.ordinaryCoaction B).map (evaluation h00 linear hκ hs B hr hγ hΓ k x) at he
  rw [← he, hx, Polynomial.map_monomial]

def gradedEvaluation (k : EulerKind) : GradedRingHom (GammaOrdinaryGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B) where
  toRingHom := evaluation h00 linear hκ hs B hr hγ hΓ k
  map_mem := fun hx => evaluation_mem h00 linear hκ hs B hr hγ hΓ k hx

theorem evaluation_forget (k : EulerKind) :
    (evaluation h00 linear hκ hs B hr hγ hΓ k).comp (GammaOrdinaryRing.forget B) =
      GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k :=
  GammaOrdinaryEulerEvaluation.evaluation_forget h00 linear hκ hs B hr hγ hΓ (RESOrdinaryReduction.torusClass B) k

theorem finite_balance_apply (k : EulerKind) (c : GammaOrdinaryFiniteRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (GammaOrdinaryFiniteMaps.full B c) = resMap B c := by
  obtain ⟨x, rfl⟩ := GammaOrdinaryFiniteRing.forget_surjective B c
  have hl := RingHom.congr_fun (GammaOrdinaryFiniteMaps.full_forget_square B) x
  have hr' := RingHom.congr_fun (GammaOrdinaryFiniteMaps.sharp_forget_square B) x
  change GammaOrdinaryFiniteMaps.full B (GammaOrdinaryFiniteRing.forget B x) = GammaOrdinaryRing.forget B (GammaFiniteRVMaps.forget B x) at hl
  change GammaOrdinaryFiniteMaps.sharp B (GammaOrdinaryFiniteRing.forget B x) = RESOrdinaryRing.forget B (GammaFiniteRVMaps.sharp B x) at hr'
  change evaluation h00 linear hκ hs B hr hγ hΓ k (GammaOrdinaryFiniteMaps.full B (GammaOrdinaryFiniteRing.forget B x)) =
    RESOrdinaryReduction.quotient B (GammaOrdinaryFiniteMaps.sharp B (GammaOrdinaryFiniteRing.forget B x))
  rw [hl, hr']
  have he := RingHom.congr_fun (evaluation_forget h00 linear hκ hs B hr hγ hΓ k) (GammaFiniteRVMaps.forget B x)
  change evaluation h00 linear hκ hs B hr hγ hΓ k (GammaOrdinaryRing.forget B (GammaFiniteRVMaps.forget B x)) =
    GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (GammaFiniteRVMaps.forget B x) at he
  rw [he]
  exact (GammaOrdinaryEvaluation.finite_balance_apply h00 linear hκ hs B hr hγ hΓ k x).symm

theorem finite_balance (k : EulerKind) :
    (evaluation h00 linear hκ hs B hr hγ hΓ k).comp (GammaOrdinaryFiniteMaps.full B) = resMap B := by
  apply RingHom.ext
  exact finite_balance_apply h00 linear hκ hs B hr hγ hΓ k

end DiamondIntegral.Section4.GammaOrdinaryRESEvaluation
