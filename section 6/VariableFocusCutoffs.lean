import «section 6».PointwiseScalarProducts
import «section 6».FullFocusValueRadii

/-! Old aperture radii from an actual varying coefficient map and a
complete joint focus. Leading-term data make their complete Gamma
graph constant on each old-label fibre; no global old VF coefficient
or chosen RV representative is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FullFocusGraphData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def variableCutoffMap (F : FullFocusGraphData (G := G) A)
    (c : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)) :=
  scalarPointwiseGammaProductMap c F.map

theorem variableCutoffMap_value (F : FullFocusGraphData (G := G) A)
    (c : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hc : ∀ p : focusActive A F.activeTags,(c p).val 0 ≠ 0) (p : focusActive A F.activeTags) :
    (F.variableCutoffMap c p).val.val=vfValue ((c p).val 0*(F.map p).val 0) :=
  scalarPointwiseGammaProductMap_value c F.map p (hc p) (F.map_nonzero p)

theorem variableCutoffMap_constant (F : FullFocusGraphData (G := G) A)
    (c : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hc : ∀ p : focusActive A F.activeTags,(c p).val 0 ≠ 0)
    (hRV : ∀ p q : focusActive A F.activeTags,p.val.2=q.val.2 →
      rv M ((c p).val 0)=rv M ((c q).val 0))
    (p q : focusActive A F.activeTags) (hTags : p.val.2=q.val.2) :
    (F.variableCutoffMap c p).val=(F.variableCutoffMap c q).val := by
  apply scalarPointwiseGammaProductMap_rv_congr c F.map hc F.map_nonzero p q (hRV p q hTags)
  exact (F.leadingTerm p).trans
    ((congrFun (F.tagged p.val p.property.1 q.val q.property.1 hTags) F.coordinate).trans (F.leadingTerm q).symm)

def variableActiveRadius (F : FullFocusGraphData (G := G) A)
    (c : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)) :=
  gammaFibreValue (F.variableCutoffMap c)

theorem variableActiveRadius_value (F : FullFocusGraphData (G := G) A)
    (c : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hc : ∀ p : focusActive A F.activeTags,(c p).val 0 ≠ 0)
    (hRV : ∀ p q : focusActive A F.activeTags,p.val.2=q.val.2 →
      rv M ((c p).val 0)=rv M ((c q).val 0)) (p : focusActive A F.activeTags) :
    (F.variableActiveRadius c p.val.2).val=vfValue ((c p).val 0*(F.map p).val 0) := by
  rw [variableActiveRadius,gammaFibreValue_at _ (F.variableCutoffMap_constant c hc hRV)]
  exact F.variableCutoffMap_value c hc p

theorem variableActiveRadius_named (hcModel : CanonicalStructure.IsCanonical (M := M))
    (F : FullFocusGraphData (G := G) A)
    (c : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hc : ∀ p : focusActive A F.activeTags,(c p).val 0 ≠ 0)
    (hRV : ∀ p q : focusActive A F.activeTags,p.val.2=q.val.2 →
      rv M ((c p).val 0)=rv M ((c q).val 0)) (u : Fin r → RVInfinity M) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {F.variableActiveRadius c u}} :=
  gammaFibreValue_named hcModel (F.variableCutoffMap c) (F.variableCutoffMap_constant c hc hRV) u

end DiamondIntegral.Section6.FullFocusGraphData
