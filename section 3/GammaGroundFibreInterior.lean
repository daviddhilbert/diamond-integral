import «section 3».GammaGroundJacobianGraph
import «section 3».GammaGroundDifferentiation

/-! Fibre interiors are definable over the original Gamma ground and
retain every independent point. Taking the interior of a cofull set
therefore gives a cofull set with open VF fibres. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r : ℕ}

def gammaGroundFibreInterior (hn : 0 < n) (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :=
  gammaGroundDifferentiabilityLocus hn (GammaGroundMap.id E)

theorem mem_gammaGroundFibreInterior (hn : 0 < n)
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (x : (rawMixedSpace (M := M) n r).Carrier) :
    x ∈ (gammaGroundFibreInterior hn E).carrier ↔ x ∈ E.carrier ∧
      ∃ ρ : Values.Gamma (M := M), ∀ b ∈ vfBall x.1 ρ, (b, x.2) ∈ E.carrier := by
  rw [gammaGroundFibreInterior, mem_gammaGroundDifferentiabilityLocus]
  constructor
  · rintro ⟨p, rfl, L, F, ⟨ρ, hρ⟩, hder⟩
    exact ⟨p.property, ρ, fun b hb => (hρ b hb).choose⟩
  · rintro ⟨hx, ρ, hρ⟩
    let p : E := ⟨x, hx⟩
    have hd : HasVFDerivativeAt (fun b : Fin n → VFType (M := M) => b) x.1 LinearMap.id := by
      simpa only [LinearMap.id_apply, add_zero] using
        hasVFDerivativeAt_affine (LinearMap.id : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M))) 0 x.1
    exact ⟨p, rfl, LinearMap.id, (fun b => b), ⟨ρ, fun b hb => ⟨hρ b hb, rfl⟩⟩, hd⟩

theorem gammaGroundFibreInterior_subset (hn : 0 < n)
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :
    (gammaGroundFibreInterior hn E).carrier ⊆ E.carrier :=
  fun x hx => ((mem_gammaGroundFibreInterior hn E x).mp hx).1

theorem gammaGroundFibreInterior_open_fibres (hn : 0 < n)
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (p : gammaGroundFibreInterior hn E) :
    ∃ ρ : Values.Gamma (M := M), ∀ b ∈ vfBall p.val.1 ρ,
      (b, p.val.2) ∈ (gammaGroundFibreInterior hn E).carrier := by
  obtain ⟨hp, ρ, hρ⟩ := (mem_gammaGroundFibreInterior hn E p.val).mp p.property
  refine ⟨ρ, fun b hb => (mem_gammaGroundFibreInterior hn E (b, p.val.2)).mpr ⟨hρ b hb, ρ, ?_⟩⟩
  intro x hx
  exact hρ x (mem_vfBall_of_common_center (vfBall_symm hb) hx)

theorem gammaGroundFibreInterior_preserves_cofull
    [CharZero (Section2.VF M)] {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
    (A E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)
    (hE : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ)) :
    Section2.vfDimension (A.sdiff (gammaGroundFibreInterior hn E)).carrier < (n : WithBot ℕ) := by
  apply gammaGround_small_complement_of_generic A _ hκ hs hS hv hn
  intro a
  let p : E := ⟨a.val.val, gammaGround_mem_of_small_complement E hκ hs hS hv hn hE a⟩
  obtain ⟨L, hL⟩ := gammaGround_differentiable_of_independent hκ hs hS hv (GammaGroundMap.id E) p a.property
  exact (mem_gammaGroundDifferentiabilityLocus hn (GammaGroundMap.id E) a.val.val).mpr ⟨p, rfl, L, hL⟩

end DiamondIntegral.Section3
