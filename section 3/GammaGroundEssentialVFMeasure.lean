import «section 3».GammaGroundEssentialVFComposition
import «section 3».GammaGroundDifferentiation
import «section 3».MixedVFJacobianRestriction

/-! The Jacobian measure equation on independent points of actual
essential Gamma-ground representatives. The same-ground cofull refinement
is proved in GammaGroundPointwiseVFMeasure. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3.GammaGroundEssentialVFMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r s t : ℕ}
variable {W : Type} [CommMonoidWithZero W]

section Data
variable [TopologicalSpace (Section2.VF M)]
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}

def PreservesGeneric (j : Section2.VF M →*₀ W) (a : A → W) (b : B → W)
    (f : GammaGroundEssentialVFMap A B) : Prop :=
  ∀ p : f.source, AlgebraicIndependent (vfParameterField ground.real) p.val.1 →
    ∃ J : Section2.VF M, HasMixedVFJacobianAt f.map p J ∧
      a ⟨p.val, f.source_subset p.property⟩ =
        b ⟨(f.map p).val, f.target_subset (f.map p).property⟩ * j J
end Data

variable [hchar : CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
variable {C : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n t)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

include hchar hκ hs hS hv in
theorem preservesGeneric_id (j : Section2.VF M →*₀ W) (a : A → W) :
    PreservesGeneric j a a (GammaGroundEssentialVFMap.id A) := by
  intro p hp
  obtain ⟨L, F, ⟨ρ, hρ⟩, hder⟩ := gammaGround_differentiable_of_independent hκ hs hS hv (GammaGroundMap.id A) p hp
  have hchart : IsVFChartAt (GammaGroundMap.id A) p (fun x => x) := by
    refine ⟨ρ, fun x hx => ?_⟩
    obtain ⟨ha, _⟩ := hρ x hx
    exact ⟨ha, rfl⟩
  have hId : HasVFDerivativeAt (fun x : Fin n → Section2.VF M => x) p.val.1 LinearMap.id := by
    simpa only [LinearMap.id_apply, add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id : (Fin n → Section2.VF M) →ₗ[Section2.VF M] (Fin n → Section2.VF M)) 0 p.val.1
  refine ⟨1, ⟨_, hchart, ?_⟩, ?_⟩
  · simpa only [LinearMap.toMatrix'_id, Matrix.det_one] using hId.hasJacobianAt
  · simp only [map_one, mul_one]; rfl

include hchar hκ hs hS hv in
theorem preservesGeneric_symm (j : Section2.VF M →*₀ W) (a : A → W) (b : B → W)
    (f : GammaGroundEssentialVFMap A B) (hf : PreservesGeneric j a b f) :
    PreservesGeneric j b a f.symm := by
  intro p hp
  let q := f.symm.map p
  have hq := gammaGround_independent_map f.symm.map
    (GammaGroundMap.finiteFibres_of_injective f.symm.bijective.injective) hκ hS p hp
  obtain ⟨J, K, hJ, hK, hprod⟩ := gammaGround_jacobian_inverse_of_independent hκ hs hS hv
    (show GammaGroundBijection f.source f.target from ⟨f.map, f.bijective⟩) q hq
  have he : f.map q = p := f.map.apply_inverse f.bijective p
  rw [he] at hK
  obtain ⟨L, hL, hw⟩ := hf q hq
  rw [hL.unique hJ] at hw
  have hb : (⟨(f.map q).val, f.target_subset (f.map q).property⟩ : B) =
      ⟨p.val, f.target_subset p.property⟩ := Subtype.ext (congrArg (fun z : f.target => z.val) he)
  refine ⟨K, hK, ?_⟩
  change b ⟨p.val, f.target_subset p.property⟩ = a ⟨q.val, f.source_subset q.property⟩ * j K
  rw [hw, hb, mul_assoc, ← map_mul, mul_comm J K, hprod, map_one, mul_one]

theorem preservesGeneric_comp (j : Section2.VF M →*₀ W) (a : A → W) (b : B → W) (c : C → W)
    (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C)
    (hf : PreservesGeneric j a b f) (hg : PreservesGeneric j b c g) :
    PreservesGeneric j a c (comp hκ hs hS hv hn f g) := by
  intro p hp
  let m := f.compMiddle g
  obtain ⟨J, K, hJ, hK, hC⟩ := gammaGround_jacobian_comp_of_independent hκ hs hS hv
    m g.map (GammaGroundMap.finiteFibres_of_injective (f.compMiddle_injective g)) p hp
  let i (x : (comp hκ hs hS hv hn f g).source) : f.source := ⟨x.val, f.compSource_subset g x.property⟩
  obtain ⟨L, hL, hw⟩ := hf (i p) hp
  have hLJ := mixedJacobian_eq_of_restriction f.map m i (fun _ => rfl) (fun _ => rfl) p hL hJ
  obtain ⟨D, hD, hwg⟩ := hg (m p)
    (gammaGround_independent_map m (GammaGroundMap.finiteFibres_of_injective (f.compMiddle_injective g)) hκ hS p hp)
  rw [hLJ] at hw
  rw [hD.unique hK] at hwg
  refine ⟨K * J, ?_, ?_⟩
  · obtain ⟨F, hF, hdet⟩ := hC
    exact ⟨F, hF, hdet⟩
  · calc
      _ = b ⟨(m p).val, g.source_subset (m p).property⟩ * j J := hw
      _ = _ := by rw [hwg, mul_assoc, map_mul]; rfl

end DiamondIntegral.Section3.GammaGroundEssentialVFMap
