import «section 3».GammaLiftProductGeometry
import «section 3».GammaGroundBijectionProducts
import Integration7.MixedDomainProductJacobians

/-! Actual Gamma-ground Cartesian product maps use the existing
block-product Jacobian theorem, including zero-arity factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n m a a' b b' : ℕ}
variable {U : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a)}
variable {U' : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a')}
variable {V : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b)}
variable {V' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b')}

def gammaMixedPackBijection (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a))
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b)) :
    GammaGroundBijection (A.prod D) (gammaGroundMixedProductDomain A D) :=
  ⟨(gammaGroundMixedPack A D).toImage,(gammaGroundMixedPack A D).toImage_bijective (gammaGroundMixedPack_injective A D)⟩

theorem gammaMixedUnpack_pack (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a))
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b)) (p : A.prod D) :
    gammaGroundMixedUnpack A D ((gammaGroundMixedPack A D).toImage p) = p :=
  (gammaMixedPackBijection A D).map.inverse_apply (gammaMixedPackBijection A D).bijective p

theorem gammaMixedPack_unpack (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a))
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b)) (p : gammaGroundMixedProductDomain A D) :
    (gammaGroundMixedPack A D).toImage (gammaGroundMixedUnpack A D p) = p :=
  (gammaMixedPackBijection A D).map.apply_inverse (gammaMixedPackBijection A D).bijective p

def gammaMixedProductMap (f : GammaGroundMap U U') (g : GammaGroundMap V V') :
    GammaGroundMap (gammaGroundMixedProductDomain U V) (gammaGroundMixedProductDomain U' V') :=
  (gammaGroundMixedPack U' V').toImage.comp ((f.prodMap g).comp (gammaGroundMixedUnpack U V))

def gammaMixedProductBijection (f : GammaGroundBijection U U') (g : GammaGroundBijection V V') :
    GammaGroundBijection (gammaGroundMixedProductDomain U V) (gammaGroundMixedProductDomain U' V') :=
  (gammaMixedPackBijection U' V').comp ((f.prodMap g).comp (gammaMixedPackBijection U V).symm)

theorem gammaMixedProductMap_pair (f : GammaGroundMap U U') (g : GammaGroundMap V V') (u : U) (v : V) :
    gammaMixedProductMap f g ((gammaGroundMixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩) =
      (gammaGroundMixedPack U' V').toImage ⟨((f u).val,(g v).val),(f u).property,(g v).property⟩ := by
  change (gammaGroundMixedPack U' V').toImage ((f.prodMap g)
    (gammaGroundMixedUnpack U V ((gammaGroundMixedPack U V).toImage _))) = _
  rw [gammaMixedUnpack_pack]
  rfl

theorem gammaMixedProduct_chart
    (f : GammaGroundMap U U') (g : GammaGroundMap V V') (u : U) (v : V)
    (F : (Fin n → Section2.VF M) → Fin n → Section2.VF M)
    (H : (Fin m → Section2.VF M) → Fin m → Section2.VF M)
    (hF : IsVFChartAt f u F) (hH : IsVFChartAt g v H) :
    IsVFChartAt (gammaMixedProductMap f g)
      ((gammaGroundMixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩) (tupleBlockProduct F H) := by
  obtain ⟨ρF,hρF⟩ := hF
  obtain ⟨ρH,hρH⟩ := hH
  refine ⟨max ρF ρH,?_⟩
  intro x hx
  change x ∈ vfBall (Fin.append u.val.1 v.val.1) (max ρF ρH) at hx
  let xl : Fin n → Section2.VF M := x ∘ Fin.castAdd m
  let xr : Fin m → Section2.VF M := x ∘ Fin.natAdd n
  have hBallF : xl ∈ vfBall u.val.1 ρF := by
    intro i
    apply lt_of_le_of_lt (show ρF.val ≤ (max ρF ρH).val from le_max_left _ _)
    simpa only [xl,Function.comp_apply,Fin.append_left] using hx (Fin.castAdd m i)
  have hBallH : xr ∈ vfBall v.val.1 ρH := by
    intro i
    apply lt_of_le_of_lt (show ρH.val ≤ (max ρF ρH).val from le_max_right _ _)
    simpa only [xr,Function.comp_apply,Fin.append_right] using hx (Fin.natAdd n i)
  obtain ⟨hu,hfu⟩ := hρF xl hBallF
  obtain ⟨hv,hgv⟩ := hρH xr hBallH
  let u₀ : U := ⟨(xl,u.val.2),hu⟩
  let v₀ : V := ⟨(xr,v.val.2),hv⟩
  let w := (gammaGroundMixedPack U V).toImage ⟨(u₀.val,v₀.val),u₀.property,v₀.property⟩
  have hw : w.val = (x,Fin.append u.val.2 v.val.2) := Prod.ext Fin.append_castAdd_natAdd rfl
  have hmem : (x,Fin.append u.val.2 v.val.2) ∈ (gammaGroundMixedProductDomain U V).carrier := hw ▸ w.property
  refine ⟨hmem,?_⟩
  have hpoint : (⟨(x,Fin.append u.val.2 v.val.2),hmem⟩ : gammaGroundMixedProductDomain U V) = w := Subtype.ext hw.symm
  change (gammaMixedProductMap f g ⟨(x,Fin.append u.val.2 v.val.2),hmem⟩).val = _
  rw [hpoint]
  dsimp only [w]
  rw [gammaMixedProductMap_pair,gammaMixedProductMap_pair]
  change (Fin.append (f u₀).val.1 (g v₀).val.1,Fin.append (f u₀).val.2 (g v₀).val.2) =
    (Fin.append (F xl) (H xr),Fin.append (f u).val.2 (g v).val.2)
  have hF1 := congrArg Prod.fst hfu
  have hH1 := congrArg Prod.fst hgv
  have hF2 := congrArg Prod.snd hfu
  have hH2 := congrArg Prod.snd hgv
  exact Prod.ext (congrArg₂ Fin.append hF1 hH1) (congrArg₂ Fin.append hF2 hH2)

theorem gammaMixedProduct_jacobian
    (f : GammaGroundMap U U') (g : GammaGroundMap V V') (u : U) (v : V)
    (J K : Section2.VF M) (hf : HasMixedVFJacobianAt f u J) (hg : HasMixedVFJacobianAt g v K) :
    HasMixedVFJacobianAt (gammaMixedProductMap f g)
      ((gammaGroundMixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩) (J*K) := by
  obtain ⟨F,hF,hJF⟩ := hf
  obtain ⟨H,hH,hJH⟩ := hg
  exact ⟨tupleBlockProduct F H,gammaMixedProduct_chart f g u v F H hF hH,
    has_vf_jacobian_block_product F H u.val.1 v.val.1 J K hJF hJH⟩

end DiamondIntegral.Section3
