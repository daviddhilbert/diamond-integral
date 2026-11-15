import IntegrationSection5.RVBranchProductHeadSaturation
import IntegrationSection5.GammaRVPredicateChain
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {H D : DefSet (M := M) S (n+1) l}

structure ProductRVBranchHead (u : SpecialBijection A B) (H : DefSet (M := M) S (n+1) l)
    (ρ : Fin a → Fin l) (E : Set (Fin a → RV (M := M))) (previous : Option Bool) where
  preparation : HeadPreparation H
  projection : Fin b → Fin preparation.arity
  arity_le : l ≤ preparation.arity
  embedding : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ E → activeUnaryProjection 0 ρ p ∈ carrier A
  special : SpecialRelativeBoundary preparation.map 0 previous (u.chain.lastKind previous)
  target_gamma : GammaSetDefinable G (carrier preparation.target)
  graph : GammaGraphDefinable G (pointMapGraph preparation.map)
  compatibility : ∀ j, projection (suffixIndex (special_chain_rvArity_le u.chain) j) = suffixIndex arity_le (ρ j)
  coverage : ∀ j : Fin preparation.arity, (∃ k, projection k = j) ∨ ∃ k, suffixIndex arity_le k = j
  square : ∀ p : H, ∀ hp : p.val.2 ∘ ρ ∈ E,
    activeUnaryProjection 0 projection (preparation.map p).val =
      (u.toMap ⟨activeUnaryProjection 0 ρ p.val,embedding p.val p.property hp⟩).val
  inactive_vf : ∀ p : H, p.val.2 ∘ ρ ∉ E → vfAt (preparation.map p).val 0 = vfAt p.val 0
  inactive_sameRV : ∀ p q : H, p.val.2 ∘ ρ ∉ E → q.val.2 ∘ ρ ∉ E →
    SameRV p.val q.val → SameRV (preparation.map p).val (preparation.map q).val
  ending_tag : u.chain.lastKind previous ≠ some true → ∃ kH, Tagged (carrier preparation.target) 0 kH

theorem product_rv_branch_head (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B)) (hH : GammaSetDefinable G (carrier H))
    (ρ : Fin a → Fin l) (E : Set (Fin a → RV (M := M)))
    (hD : carrier D = {p | p ∈ carrier H ∧ p.2 ∘ ρ ∈ E})
    (Q : Point (M := M) (n+1) l → Prop) (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hProduct : carrier D = {p | activeUnaryProjection 0 ρ p ∈ carrier A ∧ Q p})
    (hFlag : ∀ p ∈ carrier A, p.2 ∈ E)
    (hInactive : HeadSaturated {p | p ∈ carrier H ∧ p.2 ∘ ρ ∉ E})
    (previous : Option Bool) (hTag : previous ≠ some true → ∃ kH, Tagged (carrier H) 0 kH)
    (hAlt : u.chain.Alternating previous) : Nonempty (ProductRVBranchHead (G := G) u H ρ E previous) := by
  have hEmb : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ E → activeUnaryProjection 0 ρ p ∈ carrier A := by
    intro p hp he
    exact ((Set.ext_iff.mp hProduct p).mp ((Set.ext_iff.mp hD p).mpr ⟨hp,he⟩)).1
  obtain ⟨r,K,σ,hle,f,hf,hK,hfG,hCompat,hCover,hComm,hOff,hOffRV,hEnd⟩ :=
    gamma_unary_chain_rvPredicateLift u.chain hu E hFlag H hH 0 ρ hEmb previous hTag hAlt
  have hSat := headSaturated_rvBranch_product_lift u hB f hf hle ρ σ E hD Q hQ hProduct hEmb
    hComm hCompat hCover hInactive hOff hOffRV
  let T : HeadPreparation H := ⟨r,K,f,specialRelativeBoundary_forget hf,hSat⟩
  exact ⟨⟨T,σ,hle,hEmb,hf,hK,hfG,hCompat,hCover,hComm,hOff,hOffRV,hEnd⟩⟩

end IntegrationInACVF.Section5
