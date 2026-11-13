import «section 4».GammaHigherPushforward
import «section 4».GammaProductFamilies

/-! Projection formula for actual weighted pushforward Gamma^n -> Gamma.
Every multiplier is an actual original-base finite-range integer family. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaHigherProjection
open GammaDefinableEuler GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaIteratedIntegral
open GammaHigherPushforward GammaParameterExtension GammaProductFamilies EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def unaryCompose (B : Base (M := M)) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (g : familySubgroup B 1) : familySubgroup B n :=
  ⟨(fun z => g.val ![T z]), by
    have hg : IntegerFamilyDefinable B g.val := g.property
    refine ⟨hg.1.subset ?_, ?_⟩
    · rintro a ⟨z, rfl⟩
      exact ⟨![T z], rfl⟩
    · intro m
      have hgl : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | g.val ![z 0] = m} := by
        convert GammaRelationLogic.preimage_definable_base B {z | g.val z = m} (hg.2 m)
          (fun _ : Fin 1 => (0 : Fin (n + 1))) using 1
        ext z
        have he : ![z 0] = z ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))) := by
          funext i
          fin_cases i
          rfl
        change g.val ![z 0] = m ↔ g.val (z ∘ (fun _ => 0)) = m
        rw [he]
      have h := GammaRelationLogic.exists_definable_base B _
        (GammaRelationLogic.inter_definable_base B _ _ hT hgl)
      convert h using 1
      ext z
      change g.val ![T z] = m ↔ ∃ a, a = T z ∧ g.val ![a] = m
      constructor
      · intro hz
        exact ⟨T z, rfl, hz⟩
      · rintro ⟨a, rfl, hz⟩
        exact hz⟩

def multiplyFamily (B : Base (M := M)) {n : ℕ} (f g : familySubgroup B n) : familySubgroup B n :=
  ⟨(fun z => f.val z * g.val z), combine_definable B _ _ f.property g.property (fun a b => a * b)⟩

theorem pushforwardFamily_projection_at (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (g : familySubgroup B 1) (a : Values.Gamma (M := M)) :
    (pushforwardFamily h00 hκ hs B hr hγ k T hT (multiplyFamily B f (unaryCompose B T hT g))).val ![a] =
      (pushforwardFamily h00 hκ hs B hr hγ k T hT f).val ![a] * g.val ![a] := by
  let F := fibreFamily B T hT f a
  let H := fibreFamily B T hT (multiplyFamily B f (unaryCompose B T hT g)) a
  have he : H = (g.val ![a]) • F := by
    apply Subtype.ext
    funext u
    change H.val u = (g.val ![a]) • F.val u
    rw [fibreFamily_eval, fibreFamily_eval]
    change (if T u = a then f.val u * g.val ![T u] else 0) =
      (g.val ![a]) • (if T u = a then f.val u else 0)
    by_cases hu : T u = a
    · simp [hu, mul_comm]
    · simp [hu]
  rw [pushforwardFamily_fibre, pushforwardFamily_fibre]
  change integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range ![a])) hr
      (finite_gamma_extension_small hκ B hγ ![a]) k n H =
    integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range ![a])) hr
      (finite_gamma_extension_small hκ B hγ ![a]) k n F * g.val ![a]
  rw [he, map_zsmul]
  simp only [zsmul_eq_mul, Int.cast_id, mul_comm]

theorem pushforward_projection (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (g : familySubgroup B 1) :
    (pushforward h00 hκ hs B hr hγ k T hT (multiplyFamily B f (unaryCompose B T hT g))).val =
      pointwiseProduct k (pushforward h00 hκ hs B hr hγ k T hT f).val
        (GammaUnaryFamilyBridge.toEuler h00 B k g).val := by
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (GammaUnaryFamilyBridge.toEuler h00 B k
      (pushforwardFamily h00 hκ hs B hr hγ k T hT (multiplyFamily B f (unaryCompose B T hT g)))).val
      (toPaperGamma a) =
    pointwiseProduct k
      (GammaUnaryFamilyBridge.toEuler h00 B k (pushforwardFamily h00 hκ hs B hr hγ k T hT f)).val
      (GammaUnaryFamilyBridge.toEuler h00 B k g).val (toPaperGamma a)
  rw [pointwiseProduct_eval, GammaUnaryFamilyBridge.toEuler_eval,
    GammaUnaryFamilyBridge.toEuler_eval, GammaUnaryFamilyBridge.toEuler_eval]
  exact pushforwardFamily_projection_at h00 hκ hs B hr hγ k T hT f g a

theorem integral_projection (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (g : familySubgroup B 1) :
    integrateAll h00 hκ hs B hr hγ k n (multiplyFamily B f (unaryCompose B T hT g)) =
      totalEuler k (pointwiseProduct k (pushforward h00 hκ hs B hr hγ k T hT f).val
        (GammaUnaryFamilyBridge.toEuler h00 B k g).val) := by
  rw [← pushforward_integral h00 hκ hs B hr hγ k linear hΓ T hT,
    pushforward_projection]

end DiamondIntegral.Section4.GammaHigherProjection
