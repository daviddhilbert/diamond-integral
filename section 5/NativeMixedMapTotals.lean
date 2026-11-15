import «section 5».NativeMixedMapFibres
import «section 5».NativeMixedFamilyTotals
import «section 3».GammaGroundMixedProducts
import «section 3».GammaGroundCarrierBijections
import «section 3».GammaGroundFiniteFibreInvariance

/-! The literal total of the actual fibres of a native mixed map is
actually Gamma-ground bijective to its original domain. Thus the row
presentation retains the original VF object and its finite RV fibres. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r p q : ℕ}

def nativeMixedMapTotal
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+n) (q+r)) :=
  nativeMixedFamilyTotal (nativeMixedDomain C) (nativeMixedDomain_definable C)
    (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f).property

def nativeMixedMapGraphPacking
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) (p+n) (q+r))) :=
  (gammaGroundMixedPack C A).comp (f.pair (GammaGroundMap.id A))

theorem nativeMixedMapGraphPacking_value
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) (a : A) :
    ((nativeMixedMapGraphPacking f) a).val =
      (Fin.append (f a).val.1 a.val.1,Fin.append (f a).val.2 a.val.2) := rfl

theorem nativeMixedMapGraphPacking_injective
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) :
    Function.Injective (nativeMixedMapGraphPacking f) := by
  intro a b hab
  have he := gammaGroundMixedPack_injective C A
    (show gammaGroundMixedPack C A ((f.pair (GammaGroundMap.id A)) a) =
      gammaGroundMixedPack C A ((f.pair (GammaGroundMap.id A)) b) from hab)
  exact Subtype.ext (congrArg (fun u : C.prod A => u.val.2) he)

theorem nativeMixedMapGraphPacking_image
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) :
    (nativeMixedMapGraphPacking f).image.carrier = (nativeMixedMapTotal f).carrier := by
  ext w
  constructor
  · rintro ⟨a,ha⟩
    rw [←ha]
    change ((nativeMixedMapGraphPacking f) a).val ∈ (nativeMixedMapTotal f).carrier
    rw [nativeMixedMapGraphPacking_value]
    change (Fin.append (f a).val.1 a.val.1,Fin.append (f a).val.2 a.val.2) ∈
      (nativeMixedFamilyTotal (nativeMixedDomain C) (nativeMixedDomain_definable C)
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f).property).carrier
    rw [nativeMixedFamilyTotal_mem]
    exact ⟨⟨(f a).val,(f a).property,rfl⟩,⟨a,rfl⟩⟩
  · intro hw
    let z : Section2.Mixed M p q := (w.1 ∘ Fin.castAdd n,w.2 ∘ Fin.castAdd r)
    let x : Section2.Mixed M n r := (w.1 ∘ Fin.natAdd p,w.2 ∘ Fin.natAdd q)
    have hpack : (Fin.append z.1 x.1,Fin.append z.2 x.2) = w :=
      Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd
    have hm : nativeMixedCode z ∈ nativeMixedDomain C ∧
        Fin.append (nativeMixedCode z) (nativeMixedCode x) ∈ (nativeMixedMapFibreFormula f).val := by
      have h := hpack.symm ▸ hw
      exact (nativeMixedFamilyTotal_mem (nativeMixedDomain C) (nativeMixedDomain_definable C)
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f).property z.1 z.2 x.1 x.2).mp h
    obtain ⟨a,hz,hx⟩ := (nativeMixedMapFibreFormula_row f (nativeMixedCode z) (nativeMixedCode x)).mp hm.2
    have hz' : (f a).val = z := nativeMixedCode_injective hz
    have hx' : a.val = x := nativeMixedCode_injective hx
    refine ⟨a,?_⟩
    change ((nativeMixedMapGraphPacking f) a).val = w
    rw [nativeMixedMapGraphPacking_value,hz',hx']
    exact hpack

def nativeMixedMapTotalBijection
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) :
    GammaGroundBijection A (nativeMixedMapTotal f) :=
  (GammaGroundBijection.ofCarrierEq (nativeMixedMapGraphPacking_image f)).comp
    ⟨(nativeMixedMapGraphPacking f).toImage,
      (nativeMixedMapGraphPacking f).toImage_bijective (nativeMixedMapGraphPacking_injective f)⟩

theorem nativeMixedMapTotal_finite
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) :
    ∀ x : Fin (p+n) → Section2.VF M,{t | (x,t) ∈ (nativeMixedMapTotal f).carrier}.Finite :=
  (gammaGroundFiniteRVFibres_iff (nativeMixedMapTotalBijection f) hκ hs h00 hr).mp hf

end DiamondIntegral.Section5
