import «section 5».MonomialEndpointEuler
import «section 5».MonomialExtraCoordinates
import «section 5».EndpointFamilyLifts

/-! Native values of the five cylindrical Gamma fibre shapes on an
adapted monomial chart, retaining every RV output representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

theorem GroundMonomialPiece.endpointGammaSupport_at_coordinate (P : GroundMonomialPiece X)
    (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap P.source (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (D : Fin shape.endpoints → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hrow : ∀ j (x : P.source) γ, (f j x).val = γ ↔ Fin.snoc (rvUnitTupleValues x.val) γ ∈ (D j).carrier)
    (x : P.source) (γ : Values.Gamma (M := M)) :
    Fin.snoc (rvUnitTupleValues (P.cell.coordinateEquiv P.split x.val).2) γ ∈
      (P.endpointGammaSupport shape D).carrier ↔
        shape.condition (Γ := Values.Gamma (M := M)) (fun j => (f j x).val) γ := by
  let η := rvUnitTupleValues (P.cell.coordinateEquiv P.split x.val).2
  have hη : η ∈ P.gamma.carrier := ((P.coordinate_mem_iff x.val).mpr x.property).2
  have hg (j : Fin shape.endpoints) (δ : Values.Gamma (M := M)) :
      Fin.snoc η δ ∈ (P.reconstructedGammaGraph (D j)).carrier ↔ (f j x).val = δ := by
    refine (P.reconstructedGammaGraph_row (D j) η δ).trans ?_
    rw [P.freeValueReconstruction_coordinate x.val x.property]
    exact ⟨fun h => (hrow j x δ).mpr h.2, fun h => ⟨hη,(hrow j x δ).mp h⟩⟩
  refine (P.endpointGammaSupport_row shape D η γ).trans ?_
  constructor
  · rintro ⟨_, a, ha, hc⟩
    have he : (fun j => (f j x).val) = a := funext (fun j => (hg j (a j)).mp (ha j))
    exact he.symm ▸ hc
  · intro hc
    exact ⟨hη, (fun j => (f j x).val), (fun j => (hg j _).mpr rfl), hc⟩

theorem GroundMonomialPiece.extraGammaDomain_cylinderLift (P : GroundMonomialPiece X)
    (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap P.source (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (D : Fin shape.endpoints → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hrow : ∀ j (x : P.source) γ, (f j x).val = γ ↔ Fin.snoc (rvUnitTupleValues x.val) γ ∈ (D j).carrier) :
    (P.extraGammaDomain (P.endpointGammaSupport shape D)).carrier = (groundGammaCylinderLift shape f).carrier := by
  ext u
  change u ∈ (gammaGroundRVUnitTupleProductMap (P.extraGammaSource (P.endpointGammaSupport shape D))).image.carrier ↔ _
  rw [unitTupleLastProduct_mem, P.extraGammaSource_mem]
  constructor
  · rintro ⟨hx, hK⟩
    exact ⟨⟨Fin.init u,hx⟩,rfl,(P.endpointGammaSupport_at_coordinate shape f D hrow ⟨Fin.init u,hx⟩ _).mp hK⟩
  · rintro ⟨x, hx, hc⟩
    refine ⟨hx ▸ x.property, ?_⟩
    have hK := (P.endpointGammaSupport_at_coordinate shape f D hrow x _).mpr hc
    rwa [hx] at hK

theorem GroundMonomialPiece.cylinder_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (P : GroundMonomialPiece X) (shape : CylinderFibreKind)
    (f : Fin shape.endpoints → GammaGroundMap P.source (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (hordered : ∀ x : P.source, shape.ordered (Γ := Values.Gamma (M := M)) (fun j => (f j x).val))
    (D : Fin shape.endpoints → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hfun : ∀ j α, α ∈ (D j).carrier → ∀ β ∈ (D j).carrier,
      Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (hrow : ∀ j (x : P.source) γ, (f j x).val = γ ↔ Fin.snoc (rvUnitTupleValues x.val) γ ∈ (D j).carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (groundGammaCylinderLift shape f) =
      (shape.eulerFactor kind : RESDimensionFreeReduction.Ring B) * nativeTorusClass B *
        nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind P.source := by
  have hends : ∀ x ∈ P.source.carrier, ∃ a : Fin shape.endpoints → Values.Gamma (M := M),
      shape.ordered a ∧ ∀ j, Fin.snoc (rvUnitTupleValues x) (a j) ∈ (D j).carrier := by
    intro x hx
    exact ⟨(fun j => (f j ⟨x,hx⟩).val), hordered ⟨x,hx⟩, (fun j => (hrow j ⟨x,hx⟩ _).mp rfl)⟩
  have he := P.extraGamma_value h00 linear hκ hs hr hγ hΓ kind (P.endpointGammaSupport shape D)
    (fun η γ h => ((P.endpointGammaSupport_row shape D η γ).mp h).1)
  rw [P.endpointGammaSupport_euler h00 linear hκ hs hr hγ hΓ kind shape D hfun hends] at he
  have hb := P.native_unit_value h00 linear hκ hs hr hγ hΓ kind
  have hcarrier := P.extraGammaDomain_cylinderLift shape f D hrow
  have hval := nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (GammaGroundBijection.ofCarrierEq hcarrier.symm)
  rw [hval, he, hb, Int.cast_mul, pow_succ]
  ring

end DiamondIntegral.Section5
