import «section 2».GammaPowerRadii
import Section8.UniformBalls

/-! Parametric definability and neighbourhoods of the actual punctured
Gamma discs used in the inverse-germ argument of 2.51. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem puncturedGammaDisc_raw_eq
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : VF M) (γ : Gamma M) (r : VF M) (hr : r ≠ 0) (hval : vfValue r = γ.val) :
    Subtype.val '' puncturedGammaDisc a γ = rawOpenBall a.val r.val \ {a.val} := by
  have hcomp (x : VF M) (hxa : x ≠ a) :
      Valued.v (x-a) < Valued.v r ↔ γ.val < vfValue (x-a) := by
    rw [GammaThresholdGeometry.value_lt_gamma Valued.v hv (x-a) r (sub_ne_zero.mpr hxa) hr]
    change vfValue r < vfValue (x-a) ↔ γ.val < vfValue (x-a)
    rw [hval]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(mem_rawOpenBall_iff Valued.v hv a r x hr).mpr ((hcomp x hx.1).mpr hx.2),
      fun he => hx.1 (Subtype.ext he)⟩
  · rintro ⟨hz,hza⟩
    let x : VF M := ⟨z,hz.2.1⟩
    have hxa : x ≠ a := fun he => hza (congrArg Subtype.val he)
    exact ⟨x,⟨hxa,(hcomp x hxa).mp ((mem_rawOpenBall_iff Valued.v hv a r x hr).mp hz)⟩,rfl⟩

theorem puncturedGammaDisc_parametrically_definable
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : VF M) (γ : Gamma M) :
    (Set.univ : Set M).Definable₁ LRV (Subtype.val '' puncturedGammaDisc a γ) := by
  obtain ⟨r,hr,hval⟩ := gamma_has_vf_representative γ
  rw [puncturedGammaDisc_raw_eq hv a γ r hr hval]
  exact (rawOpenBall_definable (Set.mem_univ _) (Set.mem_univ _)).sdiff
    (Set.Definable.singleton_of_mem LRV (Set.mem_univ _))

theorem exists_puncturedGammaDisc_subset_nhds
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : VF M) {U : Set (VF M)} (hU : U ∈ 𝓝 a) :
    ∃ γ : Gamma M, puncturedGammaDisc a γ ⊆ U := by
  obtain ⟨γ,hγ⟩ := (exists_gammaPuncturedBallHolds_iff_eventually hv a (fun x => x ∈ U)).mpr
    (Filter.Eventually.mono hU (fun _ hx _ => hx))
  exact ⟨γ,fun x hx => hγ x hx.1 hx.2⟩

end DiamondIntegral.Section2
