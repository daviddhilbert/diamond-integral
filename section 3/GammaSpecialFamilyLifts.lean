import «section 3».GammaRVProjectionChain

/-! A base special preparation acts on a mixed family by an actual
special chain. Existing Gamma certificates and all old RV labels remain
available in the resulting presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a : ℕ}
variable {X : SpecialTransformations.Section5.DefSet (M := M) S p 0}
variable {Z : SpecialTransformations.Section5.DefSet (M := M) S p l}

structure GammaSpecialFamilyLift (T : SpecialBijection X Z)
    (H : SpecialTransformations.Section5.DefSet (M := M) S p a)
    (hHX : ∀ q ∈ carrier H, (q.1,Fin.elim0) ∈ carrier X) where
  arity : ℕ
  target : SpecialTransformations.Section5.DefSet (M := M) S p arity
  special : SpecialBijection H target
  graph : GammaChainDefinable B special.chain
  projection : Fin l → Fin arity
  square : ∀ q : H, gammaRVProjection projection (special.toMap q).val =
    (T.toMap ⟨(q.val.1,Fin.elim0),hHX q.val q.property⟩).val
  cover : ∀ j : Fin arity, (∃ k, projection k = j) ∨ ∃ k, gammaChainOldLabelIndex special.chain k = j

theorem gammaSpecialFamilyLift_exists (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
    (H : SpecialTransformations.Section5.DefSet (M := M) S p a)
    (hH : GammaSetDefinable B (carrier H))
    (hHX : ∀ q ∈ carrier H, (q.1,Fin.elim0) ∈ carrier X) :
    Nonempty (GammaSpecialFamilyLift (B := B) T H hHX) := by
  have hHA : ∀ q ∈ carrier H, gammaRVProjection (Fin.elim0 : Fin 0 → Fin a) q ∈ carrier X := by
    intro q hq
    have he : gammaRVProjection (Fin.elim0 : Fin 0 → Fin a) q = (q.1,Fin.elim0) :=
      Prod.ext rfl (by funext i; exact Fin.elim0 i)
    exact he.symm ▸ hHX q hq
  obtain ⟨r,K,σ,W,hW,hWG,hSquare,_,hCover⟩ :=
    gammaRVProjection_chain_lift T.chain hT H hH Fin.elim0 hHA none T.alternating
  refine ⟨⟨r,K,⟨W,hW⟩,hWG,σ,?_,hCover⟩⟩
  intro q
  have he : (⟨gammaRVProjection (Fin.elim0 : Fin 0 → Fin a) q.val,hHA q.val q.property⟩ : X) =
      ⟨(q.val.1,Fin.elim0),hHX q.val q.property⟩ :=
    Subtype.ext (Prod.ext rfl (by funext i; exact Fin.elim0 i))
  exact (hSquare q).trans (congrArg (fun x : X => (T.toMap x).val) he)

end DiamondIntegral.Section3
