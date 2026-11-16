import «section 6».UnaryLiftGraphs
import «section 2».Jacobian

/-! Everywhere total mixed derivatives imply continuity on the actual
fixed-label graph fibers. The local chart also supplies an open graph
fiber neighborhood. No implication from partial derivatives is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousOnGraphFibres_of_mixedDerivatives
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B)
    (hDiff : ∀ p : A, ∃ L, HasMixedVFDerivativeAt f p L) : ContinuousOnGraphFibres f := by
  intro u v a ha
  obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph f u v ha
  have hpa : p.val.1 = a := congrArg Prod.fst hp
  have hpu : p.val.2 = u := congrArg Prod.snd hp
  have hfv : (f p).val.2 = v := congrArg Prod.snd hfp
  obtain ⟨L,F,⟨ρ,hρ⟩,hL⟩ := hDiff p
  have hcont : ContinuousAt F p.val.1 :=
    DiamondIntegral.Section2.HasDerivativeAt.continuousAt hv
      ((hasDerivativeAt_iff_companion F p.val.1 L).mpr hL)
  rw [hpa] at hcont
  apply (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [vfBall_mem_nhds hv a ρ] with x hx
  have hxp : x ∈ vfBall p.val.1 ρ := by rw [hpa]; exact hx
  obtain ⟨hxA,hfx⟩ := hρ x hxp
  have hgraph : graphFibre f u v x (F x) :=
    ⟨⟨(x,p.val.2),hxA⟩,Prod.ext rfl hpu,hfx.trans (Prod.ext rfl hfv)⟩
  exact graphFibre_functional f u v (graphFibreMap_graph f u v ⟨F x,hgraph⟩) hgraph

theorem UnaryFinitaryLift.continuousOnGraphFibres
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {R : M → M → Prop}
    {hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))}}
    (T : UnaryFinitaryLift R hR) :
    ContinuousOnGraphFibres (unaryCenterMap T.center T.definable (unaryRVRelationDomain R hR)) :=
  continuousOnGraphFibres_of_mixedDerivatives hv _ T.differentiable

end DiamondIntegral.Section6
