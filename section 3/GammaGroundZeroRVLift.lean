import «section 3».GammaGroundMeasuredVFData
import Section4.MapProduct
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

def universalEmptyVFMap (Q : Space LRV M) (S : Set M) :
    Map (DefSet.univ Q S) (DefSet.univ (rawVFSpace (M := M) 0) S) :=
  Map.ofCodes _ (fun _ => Fin.elim0) (fun _ => Fin.elim0)
    (fun i => i.elim0) (fun _ => ⟨Fin.elim0,funext (fun i => i.elim0)⟩)
    (fun _ => funext (fun i => i.elim0))

def universalRVInsertEmptyVF (S : Set M) (r : ℕ) :
    Map (DefSet.univ (rawRVSpace (M := M) r) S) (DefSet.univ (rawMixedSpace (M := M) 0 r) S) :=
  ((universalEmptyVFMap (rawRVSpace r) S).pair (Map.id (DefSet.univ (rawRVSpace r) S))).toUniv

/-- The degree-zero object lift simply inserts the empty VF tuple. -/
def gammaGroundZeroRVLiftBijection (U : GammaGroundRVObject hc B 0) :
    GammaGroundBijection (gammaGroundObjectLift U) U.domain where
  map := gammaGroundObjectLiftLabel U
  bijective := by
    constructor
    · intro a b he
      apply Subtype.ext
      apply Prod.ext
      · exact funext (fun i => i.elim0)
      · exact congrArg Subtype.val he
    · intro u
      refine ⟨⟨(Fin.elim0,u.val),u,rfl,funext (fun i => i.elim0)⟩,rfl⟩

variable [TopologicalSpace (Section2.VF M)]

def gammaGroundZeroRVToVF : GammaGroundRVObject hc B 0 ⥤ GammaGroundVFObject hc B 0 where
  obj := gammaGroundObjectLiftVF
  map {U V} f := (gammaGroundZeroRVLiftBijection V).symm.comp
    (f.comp (gammaGroundZeroRVLiftBijection U))
  map_id U := by
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro a
    exact (gammaGroundZeroRVLiftBijection U).map.inverse_apply _ a
  map_comp {U V W} f g := by
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro a
    change (gammaGroundZeroRVLiftBijection W).map.inverse _ (g.map (f.map ((gammaGroundZeroRVLiftBijection U).map a))) =
      (gammaGroundZeroRVLiftBijection W).map.inverse _ (g.map
        ((gammaGroundZeroRVLiftBijection V).map
          ((gammaGroundZeroRVLiftBijection V).map.inverse _ (f.map ((gammaGroundZeroRVLiftBijection U).map a)))))
    exact congrArg (fun u => (gammaGroundZeroRVLiftBijection W).map.inverse _ (g.map u))
      ((gammaGroundZeroRVLiftBijection V).map.apply_inverse _ _).symm

instance gammaGroundZeroRVToVF_faithful :
    (gammaGroundZeroRVToVF (hc := hc) (B := B)).Faithful where
  map_injective {U V} f g he := by
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro u
    have h := congrArg (fun f : gammaGroundObjectLiftVF U ⟶ gammaGroundObjectLiftVF V =>
      (gammaGroundZeroRVLiftBijection V).map (f.map ((gammaGroundZeroRVLiftBijection U).symm.map u))) he
    change (gammaGroundZeroRVLiftBijection V).map
      ((gammaGroundZeroRVLiftBijection V).map.inverse _
        (f.map ((gammaGroundZeroRVLiftBijection U).map ((gammaGroundZeroRVLiftBijection U).map.inverse _ u)))) =
      (gammaGroundZeroRVLiftBijection V).map
      ((gammaGroundZeroRVLiftBijection V).map.inverse _
        (g.map ((gammaGroundZeroRVLiftBijection U).map ((gammaGroundZeroRVLiftBijection U).map.inverse _ u)))) at h
    simpa only [GammaGroundMap.apply_inverse] using h

instance gammaGroundZeroRVToVF_full :
    (gammaGroundZeroRVToVF (hc := hc) (B := B)).Full where
  map_surjective {U V} f := by
    refine ⟨(gammaGroundZeroRVLiftBijection V).comp (f.comp (gammaGroundZeroRVLiftBijection U).symm),?_⟩
    apply GammaGroundBijection.ext
    apply GammaGroundMap.ext
    intro a
    change (gammaGroundZeroRVLiftBijection V).map.inverse _
      ((gammaGroundZeroRVLiftBijection V).map
        (f.map ((gammaGroundZeroRVLiftBijection U).map.inverse _ ((gammaGroundZeroRVLiftBijection U).map a)))) = f.map a
    simp only [GammaGroundMap.inverse_apply]

end DiamondIntegral.Section3
