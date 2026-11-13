import «section 3».FullRawLogic
import «section 3».OrderBoundary
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Real-code expression of an order boundary in Gamma. All quantified
Gamma variables range over their entire nonzero RV-code fibres. -/
def codedGammaBoundary {X : Type} (P : X → M → Prop) (a : X) (t : M) : Prop :=
  NonzeroRV t ∧ ¬ ∃ l u, NonzeroRV l ∧ NonzeroRV u ∧ EndpointLogic.codeLt l t ∧ EndpointLogic.codeLt t u ∧
    ∀ v, NonzeroRV v → EndpointLogic.codeLt l v → EndpointLogic.codeLt v u → (P a v ↔ P a t)

theorem codedGammaBoundary_definable {α : Type} [Finite α]
    (B : FullBaseAtomicity.Base (M := M)) (P : (α → M) → M → Prop)
    (hp : FullRawDefinable B (fun z : α ⊕ Fin 1 → M => P (z ∘ Sum.inl) (z (.inr 0)))) :
    FullRawDefinable B (fun z : α ⊕ Fin 1 → M => codedGammaBoundary P (z ∘ Sum.inl) (z (.inr 0))) := by
  let i : (α ⊕ Fin 1) ⊕ Fin 2 := .inl (.inr 0)
  let l : (α ⊕ Fin 1) ⊕ Fin 2 := .inr 0
  let u : (α ⊕ Fin 1) ⊕ Fin 2 := .inr 1
  let inj : (α ⊕ Fin 1) ⊕ Fin 2 → ((α ⊕ Fin 1) ⊕ Fin 2) ⊕ Fin 1 := Sum.inl
  let v : ((α ⊕ Fin 1) ⊕ Fin 2) ⊕ Fin 1 := .inr 0
  let px : α ⊕ Fin 1 → ((α ⊕ Fin 1) ⊕ Fin 2) ⊕ Fin 1 :=
    Sum.elim (fun a => inj (.inl (.inl a))) (fun _ => inj i)
  let pv : α ⊕ Fin 1 → ((α ⊕ Fin 1) ⊕ Fin 2) ⊕ Fin 1 :=
    Sum.elim (fun a => inj (.inl (.inl a))) (fun _ => v)
  have heq := (hp.reindex pv).iff (hp.reindex px)
  have hz := (fullRaw_nonzero B v).imp ((fullRaw_codeLt B (inj l) v).imp
    ((fullRaw_codeLt B v (inj u)).imp heq))
  have hall := FullRawDefinable.forall_one
    (R := fun z v => NonzeroRV v → EndpointLogic.codeLt (z l) v →
      EndpointLogic.codeLt v (z u) →
      (P (fun a => z (.inl (.inl a))) v ↔ P (fun a => z (.inl (.inl a))) (z i))) hz
  have hbody := (fullRaw_nonzero B l).and ((fullRaw_nonzero B u).and
    ((fullRaw_codeLt B l i).and ((fullRaw_codeLt B i u).and hall)))
  have hex := FullRawDefinable.exists_two
    (R := fun (z : α ⊕ Fin 1 → M) l u => NonzeroRV l ∧ NonzeroRV u ∧
      EndpointLogic.codeLt l (z (.inr 0)) ∧ EndpointLogic.codeLt (z (.inr 0)) u ∧
      ∀ v, NonzeroRV v → EndpointLogic.codeLt l v → EndpointLogic.codeLt v u →
        (P (z ∘ Sum.inl) v ↔ P (z ∘ Sum.inl) (z (.inr 0)))) hbody
  exact (fullRaw_nonzero B (Sum.inr (0 : Fin 1) : α ⊕ Fin 1)).and hex.not

/-- Code formula and actual Gamma boundary agree on every representative. -/
theorem codedGammaBoundary_iff {X : Type} (P : X → M → Prop)
    (R : X → Values.Gamma (M := M) → Prop)
    (hP : ∀ a t, NonzeroRV t → (P a t ↔ R a (codeValue t)))
    (a : X) (t : M) : codedGammaBoundary P a t ↔
      NonzeroRV t ∧ codeValue t ∈ orderBoundary {γ | R a γ} := by
  by_cases ht : NonzeroRV t
  · have hlocal : (∃ l u, NonzeroRV l ∧ NonzeroRV u ∧ EndpointLogic.codeLt l t ∧ EndpointLogic.codeLt t u ∧
        ∀ v, NonzeroRV v → EndpointLogic.codeLt l v → EndpointLogic.codeLt v u → (P a v ↔ P a t)) ↔
      ∃ l u : Values.Gamma (M := M), l < codeValue t ∧ codeValue t < u ∧
        ∀ γ, l < γ → γ < u → (R a γ ↔ R a (codeValue t)) := by
      constructor
      · rintro ⟨l,u,hl,hu,hlt,htu,hall⟩
        refine ⟨codeValue l,codeValue u,(EndpointLogic.codeLt_iff l t hl ht).mp hlt,
          (EndpointLogic.codeLt_iff t u ht hu).mp htu,?_⟩
        intro γ hlγ hγu
        let c := representative γ
        have hc : NonzeroRV (raw c) := ⟨raw_rv _,raw_ne_zero _⟩
        have hcv : codeValue (raw c) = γ := (codeValue_raw c).trans (representative_value γ)
        have h1 : EndpointLogic.codeLt l (raw c) := (EndpointLogic.codeLt_iff l (raw c) hl hc).mpr (hcv.symm ▸ hlγ)
        have h2 : EndpointLogic.codeLt (raw c) u := (EndpointLogic.codeLt_iff (raw c) u hc hu).mpr (hcv.symm ▸ hγu)
        have hh := (hP a (raw c) hc).symm.trans ((hall (raw c) hc h1 h2).trans (hP a t ht))
        exact hcv ▸ hh
      · rintro ⟨l,u,hl,hu,hall⟩
        let lc := representative l
        let uc := representative u
        have hlc : NonzeroRV (raw lc) := ⟨raw_rv _,raw_ne_zero _⟩
        have huc : NonzeroRV (raw uc) := ⟨raw_rv _,raw_ne_zero _⟩
        have hlv : codeValue (raw lc) = l := (codeValue_raw lc).trans (representative_value l)
        have huv : codeValue (raw uc) = u := (codeValue_raw uc).trans (representative_value u)
        refine ⟨raw lc,raw uc,hlc,huc,?_,?_,?_⟩
        · exact (EndpointLogic.codeLt_iff _ _ hlc ht).mpr (hlv.symm ▸ hl)
        · exact (EndpointLogic.codeLt_iff _ _ ht huc).mpr (huv.symm ▸ hu)
        · intro v hv hlv' hvu
          have h1 := (EndpointLogic.codeLt_iff _ _ hlc hv).mp hlv'
          have h2 := (EndpointLogic.codeLt_iff _ _ hv huc).mp hvu
          rw [hlv] at h1
          rw [huv] at h2
          exact (hP a v hv).trans ((hall (codeValue v) h1 h2).trans (hP a t ht).symm)
    exact and_congr Iff.rfl (not_congr hlocal)
  · simp only [codedGammaBoundary,ht,false_and]
end DiamondIntegral.Section3
