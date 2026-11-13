import «section 3».GammaGroundRVDimension
import «section 3».GammaGroundRealFibres
import Section4.RVFibreDimension
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r : ℕ}

def gammaGroundFixedVFFibre (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (a : Fin n → Section2.VF M) :
    GammaGroundDefSet hc ⟨ground.real ∪ Set.range (vfValues a), ground.gamma⟩ (rawRVSpace (M := M) r) where
  carrier := {t | (a, t) ∈ A.carrier}
  definable := by
    let c : (rawVFSpace (M := M) n).domain := ⟨vfValues a, ⟨a, rfl⟩⟩
    have hd := (A.definable.preimage
      (universalProductSwap (rawRVSpace r) (rawVFSpace n) ground.real)).fibreRealPoint c
    change GammaGroundDefinable hc ⟨ground.real ∪ Set.range (vfValues a), ground.gamma⟩ (rawRVSpace r)
      {t | ((rawVFSpace n).decode c, t) ∈ A.carrier} at hd
    have he : (rawVFSpace n).decode c = a := decode_vfValues a
    rwa [he] at hd

def gammaGroundRVFibreDim (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) : ℕ :=
  ⨆ a : A, gammaGroundRVDim (gammaGroundFixedVFFibre A a.val.1)

theorem gammaGroundRVFibreDim_bounded (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :
    BddAbove (Set.range (fun a : A => gammaGroundRVDim (gammaGroundFixedVFFibre A a.val.1))) := by
  refine ⟨r, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact gammaGroundRVDim_le_arity _

theorem gammaGroundRVFibreDim_le_arity (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :
    gammaGroundRVFibreDim A ≤ r := ciSup_le' (fun _ => gammaGroundRVDim_le_arity _)

theorem gammaGroundRVFibreDim_attained (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (hne : A.carrier.Nonempty) :
    ∃ a : A, gammaGroundRVDim (gammaGroundFixedVFFibre A a.val.1) = gammaGroundRVFibreDim A := by
  obtain ⟨a, ha⟩ := hne
  have hne' : (Set.range (fun a : A => gammaGroundRVDim (gammaGroundFixedVFFibre A a.val.1))).Nonempty :=
    ⟨_, ⟨a, ha⟩, rfl⟩
  exact Nat.sSup_mem hne' (gammaGroundRVFibreDim_bounded A)
end DiamondIntegral.Section3
