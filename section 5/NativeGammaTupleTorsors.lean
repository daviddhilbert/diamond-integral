import «section 5».NativeGammaTorsorTowers
import «section 3».GammaGroundMapTuples

/-! A varying tuple of Gamma values defines its full literal RV torsor
with all representatives and the exact native factor g to the tuple arity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

def gammaGroundMapCoordinate
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin r))))
    (j : Fin r) : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :=
  (GammaGroundMap.ofGlobal _ _ (universalPowerCoordinate (volumeGammaSpace hc) B.real j)
    (fun _ => Set.mem_univ _)).comp f

def unitGammaTupleTorsor
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin r)))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+r)) :=
  (unitGammaTorsorTower X r (fun j => gammaGroundMapCoordinate f j)).domain

theorem unitGammaTupleTorsor_mem
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin r))))
    (u : Fin (n+r) → (CanonicalRV.RVSort M)ˣ) :
    u ∈ (unitGammaTupleTorsor f).carrier ↔
      ∃ x : X, (∀ i, u (Fin.castAdd r i) = x.val i) ∧
        rvUnitTupleValues (fun j => u (Fin.natAdd n j)) = (f x).val := by
  rw [show (unitGammaTupleTorsor f).carrier =
    (unitGammaTorsorTower X r (fun j => gammaGroundMapCoordinate f j)).domain.carrier from rfl,
    unitGammaTorsorTower_mem_iff]
  constructor
  · rintro ⟨x, hp, hv⟩
    exact ⟨x, hp, funext hv⟩
  · rintro ⟨x, hp, hv⟩
    exact ⟨x, hp, fun j => congrFun hv j⟩

theorem native_gamma_tuple_torsor_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin r)))) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (unitGammaTupleTorsor f) =
      nativeTorusClass B ^ r * nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X :=
  native_gamma_torsor_tower_value h00 linear hκ hs hr hγ hΓ kind r (fun j => gammaGroundMapCoordinate f j)

end DiamondIntegral.Section5
