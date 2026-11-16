import «section 6».OpenGraphRestrictions

/-! Volume compatibility for the actual restricted-image map of a paired
core. Its bijectivity and Jacobian charts are constructed from the given
ambient map and open core, rather than supplied as a new certificate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r s : ℕ} {S : Set M}

theorem literal_paired_core_volume_identity [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A C : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) (hf : Function.Injective f) (hCA : C.carrier ⊆ A.carrier)
    (hOpen : ∀ u, IsOpen (vfFibre C.carrier u))
    (a b : VF M) (α β ω σ : Gamma M)
    (hC : ∀ x : Fin 1 → VF M, (∃ p : C, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc a α)
    (hImage : ∀ x : Fin 1 → VF M, (∃ p : (f.restrict hCA).image, p.val.1 = x) ↔
      x 0 ∈ centeredGammaDisc b β)
    (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∈ C.carrier → p.val ∉ Z.carrier →
      ∃ J, HasMixedVFJacobianAt f p J ∧ vfValue J = (ω/σ).val) :
    ω*α = σ*β := by
  let g := (f.restrict hCA).toImage
  have hg := restrict_toImage_bijective f hf hCA
  have hRestricted (p : C) (hp : p.val ∉ Z.carrier) :
      ∃ J, HasMixedVFJacobianAt g p J ∧ vfValue J = (ω/σ).val := by
    obtain ⟨J,hJ,hVal⟩ := hconst ⟨p.val,hCA p.property⟩ p.property hp
    refine ⟨J,?_,hVal⟩
    exact mixed_jacobian_of_literal_open_restriction f g hCA (fun _ => rfl) p J
      (open_fiber_contains_chart_ball hv C.carrier hOpen p) hJ
  exact paired_core_volume_forms_identity hc hκ hs h00 hsmall Valued.v hv g hg a b α β ω σ
    hC hImage Z hZ hRestricted

end DiamondIntegral.Section6
