import IntegrationSection5.LiftedUnaryProductGeometry
import IntegrationSection5.HeadPreparation

/-! Product preparation constructs its saturated target from the exact
image formula of the actual lifted unary special chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n b l r : ℕ}

theorem unary_product_head_saturated {B : DefSet (M := M) S 1 b}
    (hB : IsRVPullback (carrier B)) {K : DefSet (M := M) S (n+1) r}
    (σ : Fin b → Fin r) (hle : l ≤ r) (Q : Point (M := M) (n+1) l → Prop)
    (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hK : carrier K = {q | activeUnaryProjection 0 σ q ∈ carrier B ∧ Q (retainedPoint hle q)}) :
    HeadSaturated (carrier K) := by
  intro q hq x hx
  have h := (Set.ext_iff.mp hK q).mp hq
  apply (Set.ext_iff.mp hK (replace 0 q x)).mpr
  constructor
  · rw [activeUnaryProjection_replace]
    exact (isRVPullback_iff _).mp hB _ h.1 _ (sameRV_replace 0 (activeUnaryProjection 0 σ q) x hx)
  · rw [retainedPoint_replace]
    exact (hQ _ _).mpr h.2

theorem unary_product_head_preparation
    {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
    (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B))
    (H : DefSet (M := M) S (n+1) l) (hH : GammaSetDefinable G (carrier H))
    (Q : Point (M := M) (n+1) l → Prop) (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hSource : carrier H = {p | activeUnaryProjection 0 Fin.elim0 p ∈ carrier A ∧ Q p}) :
    ∃ T : HeadPreparation H, ∃ σ : Fin b → Fin T.arity, ∃ hle : l ≤ T.arity,
      GammaSetDefinable G (carrier T.target) ∧ GammaGraphDefinable G (pointMapGraph T.map) ∧
      (l = 0 → Function.Bijective σ) ∧
      (∀ j : Fin T.arity, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j) ∧
      carrier T.target = {q | activeUnaryProjection 0 σ q ∈ carrier B ∧ Q (retainedPoint hle q)} ∧
      ∀ p : H, activeUnaryProjection 0 σ (T.map p).val =
        (u.toMap ⟨activeUnaryProjection 0 Fin.elim0 p.val,
          ((Set.ext_iff.mp hSource p.val).mp p.property).1⟩).val := by
  have hHA : ∀ p ∈ carrier H, activeUnaryProjection 0 Fin.elim0 p ∈ carrier A :=
    fun p hp => ((Set.ext_iff.mp hSource p).mp hp).1
  obtain ⟨r,K,σ,hle,f,hf,hσ,hK,hfG,hcompat,hcover,hcomm⟩ :=
    gamma_unary_coordinateLift u.chain hu H hH 0 Fin.elim0 hHA none u.alternating
  have hImage := coordinate_lift_product_image u.toMap u.bijective f 0
    (specialRelativeBoundary_forget hf) hle σ Q hQ hSource hcomm hcover
  let T : HeadPreparation H := ⟨r,K,f,specialRelativeBoundary_forget hf,
    unary_product_head_saturated hB σ hle Q hQ hImage⟩
  refine ⟨T,σ,hle,hK,hfG,?_,hcover,hImage,hcomm⟩
  intro hl
  subst l
  exact hσ ⟨fun j => j.elim0,fun j => j.elim0⟩

end IntegrationInACVF.Section5
