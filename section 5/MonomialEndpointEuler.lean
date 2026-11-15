import «section 5».MonomialEndpointSupports
import «section 5».GammaLastCylinderEuler
import «section 5».CylindricalFibreSyntax

/-! Original-ground Gamma supports for cylindrical endpoint families on
monomial pieces. All endpoint parameters remain quantified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}


theorem GroundMonomialPiece.freeValueReconstruction_has_source (P : GroundMonomialPiece X)
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) (hη : η ∈ P.gamma.carrier) :
    ∃ x, x ∈ P.source.carrier ∧ rvUnitTupleValues x = P.freeValueReconstruction η := by
  obtain ⟨r, hr⟩ := P.residue_nonempty
  obtain ⟨z, hz⟩ := rvUnitTupleValues_surjective P.split.freeArity η
  let e := P.cell.coordinateEquiv P.split
  let u := e.symm (r,z)
  have heu : e u = (r,z) := e.apply_symm_apply _
  have hu : u ∈ P.source.carrier := by
    apply (P.coordinate_mem_iff u).mp
    change e u ∈ _
    rw [heu]
    exact ⟨hr, by change rvUnitTupleValues z ∈ P.gamma.carrier; rwa [hz]⟩
  refine ⟨u, hu, ?_⟩
  have hv := P.freeValueReconstruction_coordinate u hu
  change P.freeValueReconstruction (rvUnitTupleValues (e u).2) = _ at hv
  rw [heu, hz] at hv
  exact hv.symm

theorem GroundMonomialPiece.endpointGammaSupport_describes (P : GroundMonomialPiece X)
    (shape : CylinderFibreKind)
    (D : Fin shape.endpoints → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hfun : ∀ j α, α ∈ (D j).carrier → ∀ β ∈ (D j).carrier,
      Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (hends : ∀ x ∈ P.source.carrier, ∃ a : Fin shape.endpoints → Values.Gamma (M := M),
      shape.ordered a ∧ ∀ j, Fin.snoc (rvUnitTupleValues x) (a j) ∈ (D j).carrier)
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) (hη : η ∈ P.gamma.carrier) :
    shape.Describes (fun γ : Values.Gamma (M := M) => Fin.snoc η γ ∈ (P.endpointGammaSupport shape D).carrier) := by
  obtain ⟨x, hx, hvalue⟩ := P.freeValueReconstruction_has_source η hη
  obtain ⟨a, ha, hDa⟩ := hends x hx
  have hag : ∀ j, Fin.snoc η (a j) ∈ (P.reconstructedGammaGraph (D j)).carrier := by
    intro j
    apply (P.reconstructedGammaGraph_row (D j) η (a j)).mpr
    exact ⟨hη, hvalue ▸ hDa j⟩
  refine ⟨a, ha, fun γ => ?_⟩
  refine (P.endpointGammaSupport_row shape D η γ).trans ?_
  constructor
  · rintro ⟨_, b, hb, hcond⟩
    have he : b = a := funext (fun j => P.reconstructedGammaGraph_unique (D j) (hfun j) η _ _ (hb j) (hag j))
    exact he ▸ hcond
  · intro hcond
    exact ⟨hη, a, hag, hcond⟩

theorem GroundMonomialPiece.endpointGammaSupport_euler
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (P : GroundMonomialPiece X) (shape : CylinderFibreKind)
    (D : Fin shape.endpoints → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hfun : ∀ j α, α ∈ (D j).carrier → ∀ β ∈ (D j).carrier,
      Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (hends : ∀ x ∈ P.source.carrier, ∃ a : Fin shape.endpoints → Values.Gamma (M := M),
      shape.ordered a ∧ ∀ j, Fin.snoc (rvUnitTupleValues x) (a j) ∈ (D j).carrier) :
    GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind (P.split.freeArity+1)
      (GammaIndicators.indicatorFamily B (P.endpointGammaSupport shape D).carrier
        (DiamondIntegral.Section4.Section3GammaChartBridge.chart (P.endpointGammaSupport shape D)).support_definable) =
    shape.eulerFactor kind * GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind P.split.freeArity
      (GammaIndicators.indicatorFamily B P.gamma.carrier
        (DiamondIntegral.Section4.Section3GammaChartBridge.chart P.gamma).support_definable) := by
  exact gamma_last_cylinder_euler h00 linear hκ hs hr hγ hΓ kind shape P.gamma
    (P.endpointGammaSupport shape D)
    (fun η γ h => ((P.endpointGammaSupport_row shape D η γ).mp h).1)
    (P.endpointGammaSupport_describes shape D hfun hends)

end DiamondIntegral.Section5
