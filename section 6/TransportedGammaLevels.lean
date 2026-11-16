import «section 6».RetainedInverseFibres

/-! Transport of open Gamma levels by an actual retained-label inverse.
Each target tag fixes the unique old source tag, so inverse graph-fiber
continuity applies on the entire target VF fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem transported_gamma_levels_open (f : Map A B) (hf : Function.Bijective f) (h : r ≤ s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (rvTailIndex h i) = p.val.2 i)
    (hCont : ContinuousOnGraphFibres (f.inverse hf))
    (hBOpen : ∀ v, IsOpen (vfFibre B.carrier v))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) :
    ∀ v γ, IsOpen {b : Fin m → VF M | (b,v) ∈ B.carrier ∧
      gammaFormExtension (ω.comp (f.inverse hf)) (b,v) = γ} := by
  intro v γ
  let u : Fin r → RVInfinity M := fun i => v (rvTailIndex h i)
  let g := graphFibreMap (f.inverse hf) v u
  have hg : ContinuousOn g (vfFibre B.carrier v) := by
    have hc := hCont v u
    rw [retained_inverse_fiber_source f hf h hRetain v] at hc
    exact hc
  have hInput (x : Fin m → VF M) (hx : (x,v) ∈ B.carrier) : (g x,u) ∈ A.carrier := by
    have hp := (f.inverse hf ⟨(x,v),hx⟩).property
    rwa [retained_inverse_point f hf h hRetain v x hx] at hp
  have hValue (x : Fin m → VF M) (hx : (x,v) ∈ B.carrier) :
      gammaFormExtension (ω.comp (f.inverse hf)) (x,v) = gammaFormExtension ω (g x,u) := by
    have hc := gammaFormExtension_comp_at ω (f.inverse hf) (⟨(x,v),hx⟩ : B)
    rw [retained_inverse_point f hf h hRetain v x hx] at hc
    exact hc
  have hEq : {x : Fin m → VF M | (x,v) ∈ B.carrier ∧
      gammaFormExtension (ω.comp (f.inverse hf)) (x,v) = γ} =
      vfFibre B.carrier v ∩ g ⁻¹' {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ} := by
    ext x
    constructor
    · rintro ⟨hx,hγ⟩
      exact ⟨hx,hInput x hx,(hValue x hx).symm.trans hγ⟩
    · rintro ⟨hx,_,hγ⟩
      exact ⟨hx,(hValue x hx).trans hγ⟩
  rw [hEq]
  exact hg.isOpen_inter_preimage (hBOpen v) (hLevels u γ)

end DiamondIntegral.Section6
