import «section 4».Section3GammaRVCodeBridge
import «section 4».Section3GammaMapBridge

/-! A chart Gamma isomorphism supplies actual native Gamma and full-code
bijections over the same base, with their quotient equation proved. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaNativeCodeMaps
open GammaRVChartPresentation Section3GammaCodeBridge Section3GammaRVCodeBridge Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {n : ℕ} {a b : GammaOrdinaryCharts.Chart B n}

def gammaBijection (f : GammaOrdinaryCharts.Iso a b) :
    GammaGroundBijection (native hc a.support a.support_definable) (native hc b.support b.support_definable) where
  map := (Section3GammaMapBridge.nativeMap hc a.support a.support_definable f.map f.graph_definable).corestrict
    (fun u => f.bijective.mapsTo u.property)
  bijective := ⟨(by
    intro u v he
    exact Subtype.ext (f.bijective.injOn u.property v.property (congrArg (fun t => t.val) he))), (by
    intro v
    obtain ⟨x, hx, hv⟩ := f.bijective.surjOn v.property
    exact ⟨⟨x, hx⟩, Subtype.ext hv⟩)⟩

theorem lift_graph (f : GammaOrdinaryCharts.Iso a b) :
    DefinableOverBase B (fun _ : Fin (n + n) => .rv) (RVMeasuredCharts.graphOn (sharp a.support) f.lift) := by
  have he : RVMeasuredCharts.graphOn (sharp a.support) f.lift = rawGraphOn a.support f.lift := by
    ext w
    exact and_congr_right (fun _ => eq_comm)
  exact (congrArg (fun T => DefinableOverBase B (fun _ : Fin (n + n) => .rv) T) he).mpr f.lift_definable

def rawBijection (f : GammaOrdinaryCharts.Iso a b) :
    GammaGroundBijection (ofRaw (hc := hc) (sharp a.support) (sharp_definable _ a.support_definable))
      (ofRaw (sharp b.support) (sharp_definable _ b.support_definable)) :=
  bijectionOfRaw _ _ _ _ f.lift (lift_graph f) f.lift_bijective

def codeBijection (f : GammaOrdinaryCharts.Iso a b) :
    GammaGroundBijection (gammaGroundCodePreimage (native hc a.support a.support_definable))
      (gammaGroundCodePreimage (native hc b.support b.support_definable)) :=
  (Section3GammaRVCodeBridge.codeBijection (native hc b.support b.support_definable)).symm.comp
    ((rawBijection f).comp (Section3GammaRVCodeBridge.codeBijection (native hc a.support a.support_definable)))

theorem codeBijection_raw (f : GammaOrdinaryCharts.Iso a b)
    (c : gammaGroundCodePreimage (native hc a.support a.support_definable)) :
    rawCode ((codeBijection f).map c) = f.lift (rawCode c) := by
  let E := Section3GammaRVCodeBridge.codeBijection (native hc b.support b.support_definable)
  let u := (rawBijection f).map ((Section3GammaRVCodeBridge.codeBijection (native hc a.support a.support_definable)).map c)
  have he := congrArg (fun z : ofRaw (hc := hc) (sharp b.support) (sharp_definable _ b.support_definable) => rvValues z.val)
    (E.map.apply_inverse E.bijective u)
  change rvValues (E.map ((codeBijection f).map c)).val = f.lift (rawCode c) at he
  exact (codeBijection_value _ _).symm.trans he

theorem codeBijection_quotient (f : GammaOrdinaryCharts.Iso a b)
    (c : gammaGroundCodePreimage (native hc a.support a.support_definable)) :
    ((volumeGammaSpace hc).power (Fin n)).decode ((codeBijection f).map c).val =
      f.map (((volumeGammaSpace hc).power (Fin n)).decode c.val) := by
  have hz : rawCode c ∈ sharp a.support := ⟨rawCode_proper c, (rawCode_value c).symm ▸ c.property⟩
  exact (rawCode_value ((codeBijection f).map c)).symm.trans
    ((congrArg codeValues (codeBijection_raw f c)).trans
      ((f.contraction _ hz).trans (congrArg f.map (rawCode_value c))))

end DiamondIntegral.Section4.Section3GammaNativeCodeMaps
