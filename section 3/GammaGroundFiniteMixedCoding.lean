import «section 3».GammaGroundFiniteVFCodeMaps
import «section 3».GammaGroundRVProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n r : ℕ}

/-- A finite mixed VF/RV domain is coded injectively by RV coordinates
without changing its Gamma ground. Existing RV coordinates are retained. -/
theorem gammaGroundFiniteMixedCodeMap (h00 : M ⊨ Axioms.ACVF00)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hfin : A.carrier.Finite) :
    ∃ m : ℕ, ∃ f : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) m)),
      Function.Injective f := by
  let p : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawVFSpace (M := M) n)) :=
    GammaGroundMap.ofGlobal A _ (universalProductFst (rawVFSpace n) (rawRVSpace r) B.real)
      (fun _ => Set.mem_univ _)
  have hpfin : p.image.carrier.Finite := (hfin.image Prod.fst).subset (by
    rintro a ⟨x,rfl⟩
    exact ⟨x.val,x.property,rfl⟩)
  obtain ⟨m,c,hinj⟩ := gammaGroundFiniteVFCodeMap h00 p.image hpfin
  let v := c.comp p.toImage
  let t : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) r)) :=
    GammaGroundMap.ofGlobal A _ (universalProductSnd (rawVFSpace n) (rawRVSpace r) B.real)
      (fun _ => Set.mem_univ _)
  let f := gammaGroundRVAppendTargets.comp (v.pair t)
  refine ⟨m+r,f,?_⟩
  intro a b he
  have he' : rvAppend (v a).val (t a).val = rvAppend (v b).val (t b).val :=
    congrArg Subtype.val he
  have hab := @rvAppend_injective M _ m r ((v a).val,(t a).val) ((v b).val,(t b).val) he'
  have hv : p.toImage a = p.toImage b := hinj (Subtype.ext (congrArg Prod.fst hab))
  apply Subtype.ext
  have ht : a.val.2 = b.val.2 := congrArg
    (fun x : (Fin m → CanonicalRV.RVSort M) × (Fin r → CanonicalRV.RVSort M) => x.2) hab
  exact Prod.ext (congrArg (fun x : p.image => x.val) hv) ht
end DiamondIntegral.Section3
