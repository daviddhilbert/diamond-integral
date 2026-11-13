import «section 3».FullGammaTupleAbstraction
import «section 3».FullGammaPartialFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Splitting a Gamma tuple off its scalar final block retains every
coordinate, using only the canonical singleton-index identification. -/
theorem gammaTuple_scalar_eta {α : Type} (z : α ⊕ Fin 1 → Values.Gamma (M := M)) :
    Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => z (.inr 0)) = z := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rfl

def gammaUniqueScalar {n : ℕ} (Q : (Fin n ⊕ Fin 1 → Values.Gamma (M := M)) → Prop)
    (γ : Fin n → Values.Gamma (M := M)) (δ : Values.Gamma (M := M)) : Prop :=
  Q (Sum.elim γ (fun _ : Fin 1 => δ)) ∧
    ∀ c : Fin 1 → Values.Gamma (M := M), Q (Sum.elim γ c) → c 0 = δ

theorem gammaUniqueScalar_definable {n : ℕ} (B : FullBaseAtomicity.Base (M := M))
    (Q : (Fin n ⊕ Fin 1 → Values.Gamma (M := M)) → Prop) (hQ : FullGammaSyntax.Definable B Q) :
    FullGammaSyntax.Definable B (fun z : Fin n ⊕ Fin 1 → Values.Gamma (M := M) => gammaUniqueScalar Q (z ∘ Sum.inl) (z (.inr 0))) := by
  have hbase : FullGammaSyntax.Definable B (fun z : Fin n ⊕ Fin 1 → Values.Gamma (M := M) =>
      Q (Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => z (.inr 0)))) :=
    hQ.congr (fun z => by rw [gammaTuple_scalar_eta])
  let e : Fin n ⊕ Fin 1 → (Fin n ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  have hcand := hQ.reindex e
  have heq := FullGammaSyntax.eq_definable B (Sum.inr (0 : Fin 1) : (Fin n ⊕ Fin 1) ⊕ Fin 1) (Sum.inl (Sum.inr 0))
  have hall := (hcand.imp heq).forall_block
  have hall' : FullGammaSyntax.Definable B (fun z : Fin n ⊕ Fin 1 → Values.Gamma (M := M) =>
      ∀ c : Fin 1 → Values.Gamma (M := M), Q (Sum.elim (z ∘ Sum.inl) c) → c 0 = z (.inr 0)) := by
    apply hall.congr
    intro z
    apply forall_congr'
    intro c
    have he : (Sum.elim z c) ∘ e = Sum.elim (z ∘ Sum.inl) c := by
      funext i
      cases i <;> rfl
    change (Q ((Sum.elim z c) ∘ e) → c 0 = z (.inr 0)) ↔ _
    rw [he]
  exact hbase.and hall' 

/-- Gamma definable closure over a finite Gamma tuple supplies an
original-ground definable partial Gamma function through that pair. -/
theorem gammaDcl_tuple_partial_function (B : Base (M := M)) {n : ℕ}
    (γ : Fin n → Values.Gamma (M := M)) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase (adjoinGammaTuple B γ) δ) :
    ∃ D : FullGammaPartialFunction (integrationGammaBase B) n, D.graph γ δ := by
  have hp0 := (FullGammaSyntax.scalar_definable_iff {δ}).mpr (integrationGammaDefinable hδ)
  have hp : FullGammaSyntax.Definable (integrationGammaBase (adjoinGammaTuple B γ))
      (fun c : Fin 1 → Values.Gamma (M := M) => c 0 = δ) := hp0.congr (fun _ => Set.mem_singleton_iff)
  obtain ⟨Q,hQ,hQx⟩ := fullGamma_tuple_abstraction B γ _ hp
  let D : FullGammaPartialFunction (integrationGammaBase B) n := {
    graph := gammaUniqueScalar Q
    definable := gammaUniqueScalar_definable _ Q hQ
    functional := by
      intro η a b ha hb
      exact (ha.2 (fun _ => b) hb.1).symm }
  refine ⟨D,?_,?_⟩
  · exact (hQx (fun _ => δ)).mpr rfl
  · intro c hc
    exact (hQx c).mp hc

/-- A value Gamma-definable from a finite Gamma input tuple lies on a
total original-ground Gamma function; the totalization names no code. -/
theorem gammaDcl_tuple_function (B : Base (M := M)) {n : ℕ}
    (γ : Fin n → Values.Gamma (M := M)) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase (adjoinGammaTuple B γ) δ) :
    ∃ f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M),
      FullGammaFunction (integrationGammaBase B) f ∧ f γ = δ := by
  obtain ⟨D,hD⟩ := gammaDcl_tuple_partial_function B γ δ hδ
  exact ⟨D.eval,D.eval_definable,D.eval_eq γ δ hD⟩
end DiamondIntegral.Section3
