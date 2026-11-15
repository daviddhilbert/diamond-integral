import IntegrationSection5.SharedRVProductSource
import IntegrationSection5.ProjectionPaddingProductRefinement
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m b : ℕ}
variable {R : DefSet (M := M) S 2 m} {AD AE : DefSet (M := M) S 1 m} {BD : DefSet (M := M) S 1 b}

structure SharedProductFirst (R : DefSet (M := M) S 2 m)
    (AD AE : DefSet (M := M) S 1 m) (BD : DefSet (M := M) S 1 b) (d : SpecialBijection AD BD) where
  dSource : Map R AD
  d_spec : ∀ p : R, (dSource p).val = activeUnaryProjection 0 id p.val
  preparation : HeadPreparation R
  projection : Fin b → Fin preparation.arity
  projection_bijective : Function.Bijective projection
  arity_le : m ≤ preparation.arity
  compatibility : ∀ j, projection (suffixIndex (special_chain_rvArity_le d.chain) j) = suffixIndex arity_le j
  graph : GammaGraphDefinable G (pointMapGraph preparation.map)
  target_gamma : GammaSetDefinable G (carrier preparation.target)
  square : ∀ p : R, activeUnaryProjection 0 projection (preparation.map p).val = (d.toMap (dSource p)).val
  head_source : carrier preparation.contractedSet =
    {p | activeUnaryProjection 0 (Fin.natAdd 1 ∘ suffixIndex arity_le) p ∈ carrier AE ∧
      productHeadRVCondition BD projection p.2}

theorem shared_product_first (d : SpecialBijection AD BD) (hd : GammaChainDefinable G d.chain)
    (hBD : IsRVPullback (carrier BD)) (hRΓ : GammaSetDefinable G (carrier R))
    (hR : carrier R = {p | activeUnaryProjection 0 id p ∈ carrier AD ∧ activeUnaryProjection 1 id p ∈ carrier AE}) :
    Nonempty (SharedProductFirst (G := G) R AD AE BD d) := by
  have hRA : ∀ p ∈ carrier R, activeUnaryProjection 0 id p ∈ carrier AD :=
    fun p hp => ((Set.ext_iff.mp hR p).mp hp).1
  let dSource := Map.corestrict (activeUnaryProjectionMap 0 id R) (fun p => hRA p.val p.property)
  let Q : Point (M := M) 2 m → Prop := fun p => activeUnaryProjection 1 id p ∈ carrier AE
  have hQ : ∀ p x, Q (replace 0 p x) ↔ Q p := by
    intro p x
    simp only [Q,activeUnaryProjection,replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  obtain ⟨T,σ,hle,hTG,hTΓ,hσ,hCompat,hCover,hShape,hComm⟩ :=
    sharedRV_unary_product_head_preparation d hd hBD R hRΓ id Q hQ hR
  have hHead := sharedRV_product_head_contracted_shape AE BD T.target σ (suffixIndex hle) hShape
  exact ⟨⟨dSource,fun _ => rfl,T,σ,hσ Function.bijective_id,hle,hCompat,hTΓ,hTG,hComm,hHead⟩⟩

namespace SharedProductFirst
variable {d : SpecialBijection AD BD}

theorem head_source_class (P : SharedProductFirst (G := G) R AD AE BD d)
    (hAE : ∀ p ∈ carrier AE, ∀ q ∈ carrier AE, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    ∀ p ∈ carrier P.preparation.contractedSet, ∀ q ∈ carrier P.preparation.contractedSet,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) :=
  rvclass_of_projection_product _ (fun p => productHeadRVCondition BD P.projection p.2) P.head_source hAE

end SharedProductFirst
end IntegrationInACVF.Section5
