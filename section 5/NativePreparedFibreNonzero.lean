import «section 5».NativePreparedLiftPullbacks

/-! Preparing the VF base retains every fibre VF coordinate. The actual
prepared lift therefore has nonzero fibre coordinates whenever the whole
original finite label maps are nonzero on their source base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p q a k l : ℕ}

theorem nativeVFPrepareLift_fibre_nonzero
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
    (hP : ∀ x : nativeVFLiftFamily Z F,
      ((nativeMixedCoordinateMap (nativeVFLiftFamily Z F) (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin (q+a))) x).val ∈ P.carrier)
    (hv : ∀ z ∈ nativeMixedDomain Z,nativeFiniteRVSchemaValid F z)
    (w : (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image) (i : Fin k) :
    w.val.1 (Fin.natAdd p i) ≠ 0 := by
  obtain ⟨x,hx⟩ := w.property
  let b := x.val.1 ∘ Fin.castAdd k
  let y := x.val.1 ∘ Fin.natAdd p
  let v := x.val.2 ∘ Fin.castAdd a
  let u := x.val.2 ∘ Fin.natAdd q
  have hpack : (Fin.append b y,Fin.append v u) = x.val :=
    Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd
  have hn := nativeVFLiftFamily_fibre_nonzero Z F hv b v y u (hpack.symm ▸ x.property) i
  have hx' : ((nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP) x).val = w.val := hx
  have he : y i = w.val.1 (Fin.natAdd p i) := by
    have h := congrArg (fun z : Section2.Mixed M (p+k) (l+(q+a)) => z.1 (Fin.natAdd p i)) hx'
    rw [nativeVFPrepareBaseMap_value] at h
    simpa only [Fin.append_right] using h
  exact he ▸ hn

end DiamondIntegral.Section5
