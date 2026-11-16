import «section 6».VFProjection
import «section 6».RVFocusContinuity

/-! A continuous function constant along active fibres descends
continuously to the inactive coordinates. Invariance makes that
projection clopen, so extension by zero stays continuous. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuous_init_descent_of_invariant
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {Y : Type} [TopologicalSpace Y] [Zero Y]
    (α : Fin (n+1) → Gamma M) (D : Set (Fin (n+1) → VF M)) (hD : AlphaInvariant α D)
    (g : (Fin (n+1) → VF M) → Y) (hG : Continuous g)
    (h : (Fin n → VF M) → Y)
    (hFactor : ∀ x ∈ D,h (Fin.init x)=g x)
    (hZero : ∀ b ∉ Fin.init '' D,h b=0) : Continuous h := by
  apply continuous_of_clopen_zero_complement (Fin.init '' D) (hD.image_init.isClopen hv) h ?_ hZero
  intro b hb
  obtain ⟨x,hx,hxb⟩ := hb
  let sectionPoint (c : Fin n → VF M) : Fin (n+1) → VF M := Fin.snoc c (x (Fin.last n))
  have hSection : Continuous sectionPoint := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [sectionPoint,Fin.snoc_last] using
        (continuous_const : Continuous (fun _ : Fin n → VF M => x (Fin.last n)))
    · simpa only [sectionPoint,Fin.snoc_castSucc] using
        (continuous_apply j : Continuous (fun c : Fin n → VF M => c j))
  have hAt : sectionPoint b=x := by
    change (Fin.snoc b (x (Fin.last n)) : Fin (n+1) → VF M)=x
    rw [← hxb,Fin.snoc_init_self]
  have hAtMem : sectionPoint b ∈ D := hAt.symm ▸ hx
  have hNear : ∀ᶠ c in 𝓝 b,sectionPoint c ∈ D :=
    hSection.continuousAt.preimage_mem_nhds ((hD.isClopen hv).isOpen.mem_nhds hAtMem)
  have hEq : h =ᶠ[𝓝 b] (fun c => g (sectionPoint c)) := by
    filter_upwards [hNear] with c hc
    simpa only [sectionPoint,Fin.init_snoc] using hFactor (sectionPoint c) hc
  exact ((hG.comp hSection).continuousAt.congr_of_eventuallyEq hEq).continuousWithinAt

end DiamondIntegral.Section6
