import «section 5».NativeMixedCoordinateMaps
import «section 3».GammaGroundFiniteFibreInvariance

/-! Preparing only the VF base coordinates transports a whole mixed
family by an actual original-ground map. Its fibre VF coordinates and
all old RV parameters are retained. The complete map is injective and
preserves finite RV fibres. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k r l : ℕ}

def nativeVFBaseParameterMap
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r))
    (P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0))
    (hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈ P.carrier) :
    GammaGroundMap A P :=
  (nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)).corestrict hP

def nativeVFPrepareBaseMap
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r))
    {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)}
    (T : GammaGroundBijection P C)
    (hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈ P.carrier) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) (p+k) (l+r))) :=
  (gammaGroundMixedPack C (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) k r))).comp
    ((T.map.comp (nativeVFBaseParameterMap A P hP)).pair (nativeMixedCoordinateMap A (Fin.natAdd p) id))

theorem nativeVFPrepareBaseMap_value
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r))
    {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
    (hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈ P.carrier)
    (a : A) :
    ((nativeVFPrepareBaseMap A T hP) a).val =
      (Fin.append (T.map ((nativeVFBaseParameterMap A P hP) a)).val.1 (a.val.1 ∘ Fin.natAdd p),
        Fin.append (T.map ((nativeVFBaseParameterMap A P hP) a)).val.2 a.val.2) := rfl

theorem nativeVFPrepareBaseMap_injective
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r))
    {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
    (hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈ P.carrier) :
    Function.Injective (nativeVFPrepareBaseMap A T hP) := by
  intro a b hab
  let D := GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) k r)
  let f := T.map.comp (nativeVFBaseParameterMap A P hP)
  let g := nativeMixedCoordinateMap A (Fin.natAdd p) (id : Fin r → Fin r)
  have he := gammaGroundMixedPack_injective C D
    (show gammaGroundMixedPack C D ((f.pair g) a) = gammaGroundMixedPack C D ((f.pair g) b) from hab)
  have hbase : f a = f b := Subtype.ext (congrArg (fun u : C.prod D => u.val.1) he)
  have hparam := T.bijective.1 hbase
  have hprefix := congrArg (fun u : P => u.val.1) hparam
  change a.val.1 ∘ Fin.castAdd k = b.val.1 ∘ Fin.castAdd k at hprefix
  have hfibre : (a.val.1 ∘ Fin.natAdd p,a.val.2) = (b.val.1 ∘ Fin.natAdd p,b.val.2) :=
    congrArg (fun u : C.prod D => u.val.2) he
  have hr : a.val.2 = b.val.2 := congrArg (fun u : Section2.Mixed M k r => u.2) hfibre
  apply Subtype.ext
  refine Prod.ext (funext (fun i => ?_)) hr
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact congrFun hprefix j
  · exact congrFun (congrArg Prod.fst hfibre) j

def nativeVFPrepareBaseBijection
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r))
    {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
    (hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈ P.carrier) :
    GammaGroundBijection A (nativeVFPrepareBaseMap A T hP).image :=
  ⟨(nativeVFPrepareBaseMap A T hP).toImage,
    (nativeVFPrepareBaseMap A T hP).toImage_bijective (nativeVFPrepareBaseMap_injective A T hP)⟩

theorem nativeVFPrepareBaseMap_finite
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) r))
    {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
    (hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈ P.carrier)
    (hf : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) :
    ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFPrepareBaseMap A T hP).image.carrier}.Finite :=
  (gammaGroundFiniteRVFibres_iff (nativeVFPrepareBaseBijection A T hP) hκ hs h00 hr).mp hf

end DiamondIntegral.Section5
