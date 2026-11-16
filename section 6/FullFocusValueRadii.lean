import «section 6».FocusCutoffValueMaps
import «section 6».GammaFibreValueChoice

/-! Complete graph data have canonical named active radii before
any permitted component has been reconstructed. This avoids making
RV-indexed choices of covariance witnesses in a graph template. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
namespace FullFocusGraphData

theorem map_nonzero (F : FullFocusGraphData (G := G) A) (p : focusActive A F.activeTags) :
    (F.map p).val 0 ≠ 0 := by
  intro hZero
  have hrv : (rv M (p.val.1 F.coordinate)).val=iRVZero := by
    rw [← F.leadingTerm p,hZero]
    exact (CanonicalRV.encodedRv_zero_iff 0).mpr rfl
  exact F.doublyBounded.nonzero p.property.1 F.coordinate
    ((CanonicalRV.encodedRv_zero_iff _).mp hrv)

def cutoffMap (F : FullFocusGraphData (G := G) A)
    (c : VF M) (hc : S.Definable₁ LRV {c.val}) :
    Map (focusActive A F.activeTags) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (scalarGammaValueMap S).comp (scalarFocusProductMap F.map c hc)

theorem cutoffMap_value (F : FullFocusGraphData (G := G) A)
    (c : VF M) (hc : S.Definable₁ LRV {c.val}) (hc0 : c ≠ 0) (p : focusActive A F.activeTags) :
    (F.cutoffMap c hc p).val.val=vfValue (c*(F.map p).val 0) := by
  have hn : (scalarFocusProductMap F.map c hc p).val 0 ≠ 0 := by
    rw [scalarFocusProductMap_at]
    exact mul_ne_zero hc0 (F.map_nonzero p)
  exact (scalarGammaValueMap_nonzero S _ hn).trans
    (congrArg vfValue (scalarFocusProductMap_at F.map c hc p))

theorem cutoffMap_constant (F : FullFocusGraphData (G := G) A)
    (c : VF M) (hc : S.Definable₁ LRV {c.val}) (hc0 : c ≠ 0)
    (p q : focusActive A F.activeTags) (hu : p.val.2=q.val.2) :
    (F.cutoffMap c hc p).val=(F.cutoffMap c hc q).val := by
  apply Subtype.ext
  rw [F.cutoffMap_value c hc hc0 p,F.cutoffMap_value c hc hc0 q]
  have hRV : rv M ((F.map p).val 0)=rv M ((F.map q).val 0) :=
    (F.leadingTerm p).trans ((congrFun (F.tagged p.val p.property.1 q.val q.property.1 hu) F.coordinate).trans
      (F.leadingTerm q).symm)
  have hValue : vfValue ((F.map p).val 0)=vfValue ((F.map q).val 0) := congrArg Values.vrv hRV
  change Values.vfValueHom (c*(F.map p).val 0)=Values.vfValueHom (c*(F.map q).val 0)
  rw [map_mul,map_mul]
  exact congrArg (fun x : GammaInfinity M => vfValue c*x) hValue

def activeRadius (F : FullFocusGraphData (G := G) A) (c : VF M) (hc : S.Definable₁ LRV {c.val}) :=
  gammaFibreValue (F.cutoffMap c hc)

theorem activeRadius_value (F : FullFocusGraphData (G := G) A)
    (c : VF M) (hc : S.Definable₁ LRV {c.val}) (hc0 : c ≠ 0) (p : focusActive A F.activeTags) :
    (F.activeRadius c hc p.val.2).val=vfValue (c*(F.map p).val 0) := by
  change (gammaFibreValue (F.cutoffMap c hc) p.val.2).val=_
  rw [gammaFibreValue_at _ (F.cutoffMap_constant c hc hc0)]
  exact F.cutoffMap_value c hc hc0 p

theorem activeRadius_named (hcModel : CanonicalStructure.IsCanonical (M := M))
    (F : FullFocusGraphData (G := G) A) (c : VF M) (hc : S.Definable₁ LRV {c.val}) (hc0 : c ≠ 0)
    (u : Fin r → RVInfinity M) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {F.activeRadius c hc u}} :=
  gammaFibreValue_named hcModel (F.cutoffMap c hc) (F.cutoffMap_constant c hc hc0) u

end FullFocusGraphData
end DiamondIntegral.Section6
