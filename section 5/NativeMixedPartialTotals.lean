import «section 5».NativeMixedMapTotals
import «section 5».NativeVFLiftFamilies
import «section 3».GammaGroundMapPreimages

/-! Restricting an actual native map to any original-ground base piece
identifies its source preimage with the literal mixed row total over that
piece. The entire old RV tuple is retained by the graph-packing map. -/
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
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p q n r : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}

def nativeMixedPartialTotal (f : GammaGroundMap A C)
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+n) (q+r)) :=
  nativeMixedFamilyTotal (nativeMixedDomain Z) (nativeMixedDomain_definable Z)
    (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f).property

def nativeMixedPartialTotalMap (f : GammaGroundMap A C)
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)) :
    GammaGroundMap (f.preimage Z) (nativeMixedPartialTotal f Z) :=
  ((nativeMixedMapGraphPacking f).restrict (f.preimage_subset Z)).corestrict (by
    intro x
    let a : A := ⟨x.val,f.preimage_subset Z x.property⟩
    have hZ : (f a).val ∈ Z.carrier := by
      obtain ⟨b,hb,hz⟩ := x.property
      have he : b = a := Subtype.ext hb
      exact he ▸ hz
    have hm := (nativeMixedFamilyTotal_mem (hc := hc) (nativeMixedDomain Z) (nativeMixedDomain_definable Z)
      (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f).property
      (f a).val.1 (f a).val.2 a.val.1 a.val.2).mpr
      ⟨⟨(f a).val,hZ,rfl⟩,(nativeMixedMapFibreFormula_row f _ _).mpr ⟨a,rfl,rfl⟩⟩
    exact hm)

theorem nativeMixedPartialTotalMap_bijective (f : GammaGroundMap A C)
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)) :
    Function.Bijective (nativeMixedPartialTotalMap f Z) := by
  constructor
  · intro a b hab
    have hv : ((nativeMixedPartialTotalMap f Z) a).val = ((nativeMixedPartialTotalMap f Z) b).val :=
      congrArg (fun w : nativeMixedPartialTotal f Z => w.val) hab
    have he : (nativeMixedMapGraphPacking f) ⟨a.val,f.preimage_subset Z a.property⟩ =
        (nativeMixedMapGraphPacking f) ⟨b.val,f.preimage_subset Z b.property⟩ := Subtype.ext hv
    have hi := (nativeMixedMapGraphPacking_injective f) he
    exact Subtype.ext (congrArg (fun x : A => x.val) hi)

  · intro w
    let z : Section2.Mixed M p q := (w.val.1 ∘ Fin.castAdd n,w.val.2 ∘ Fin.castAdd r)
    let x : Section2.Mixed M n r := (w.val.1 ∘ Fin.natAdd p,w.val.2 ∘ Fin.natAdd q)
    have hpack : (Fin.append z.1 x.1,Fin.append z.2 x.2) = w.val :=
      Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd
    have hm := (nativeMixedFamilyTotal_mem (hc := hc) (nativeMixedDomain Z) (nativeMixedDomain_definable Z)
      (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f).property z.1 z.2 x.1 x.2).mp
      (hpack.symm ▸ w.property)
    obtain ⟨a,hz,hx⟩ := (nativeMixedMapFibreFormula_row f (nativeMixedCode z) (nativeMixedCode x)).mp hm.2
    have hz' : (f a).val = z := nativeMixedCode_injective hz
    have hx' : a.val = x := nativeMixedCode_injective hx
    have hZ : (f a).val ∈ Z.carrier := hz'.symm ▸
      ((nativeMixedCode_mem_domain_iff Z z).mp hm.1)
    let aZ : f.preimage Z := ⟨a.val,a,rfl,hZ⟩
    refine ⟨aZ,Subtype.ext ?_⟩
    change ((nativeMixedMapGraphPacking f) ⟨a.val,f.preimage_subset Z aZ.property⟩).val = w.val
    have he : (⟨a.val,f.preimage_subset Z aZ.property⟩ : A) = a := Subtype.ext rfl
    rw [he,nativeMixedMapGraphPacking_value,hz',hx']
    exact hpack

def nativeMixedPartialTotalBijection (f : GammaGroundMap A C)
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)) :
    GammaGroundBijection (f.preimage Z) (nativeMixedPartialTotal f Z) :=
  ⟨nativeMixedPartialTotalMap f Z,nativeMixedPartialTotalMap_bijective f Z⟩

end DiamondIntegral.Section5
