import «section 5».MonomialTorsorEvaluation
import «section 5».ScalarGammaParameterControl

/-! A literal value-torsor graph on a monomial piece has bounded native
value equal to one residue-torus factor times its actual base value. -/
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

theorem GroundMonomialPiece.reconstructedTorsorDomain_graphLift (P : GroundMonomialPiece X)
    (f : GammaGroundMap P.source (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hrow : ∀ (x : P.source) γ, (f x).val = γ ↔ Fin.snoc (rvUnitTupleValues x.val) γ ∈ D.carrier) :
    (P.reconstructedTorsorDomain D).carrier = (groundGammaFunctionGraphLift f).carrier := by
  ext u
  change u ∈ (gammaGroundRVUnitTupleProductMap (P.reconstructedTorsorSource D)).image.carrier ↔ _
  rw [unitTupleLastProduct_mem, P.reconstructedTorsorSource_mem]
  constructor
  · rintro ⟨hx, hD⟩
    exact ⟨⟨Fin.init u, hx⟩, rfl, (hrow ⟨Fin.init u, hx⟩ _).mpr hD⟩
  · rintro ⟨x, hx, hf⟩
    refine ⟨hx ▸ x.property, ?_⟩
    have hD := (hrow x _).mp hf
    rwa [hx] at hD

theorem GroundMonomialPiece.function_torsor_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (P : GroundMonomialPiece X)
    (f : GammaGroundMap P.source (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hD : ∀ α ∈ D.carrier, ∀ β ∈ D.carrier, Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (hrow : ∀ (x : P.source) γ, (f x).val = γ ↔ Fin.snoc (rvUnitTupleValues x.val) γ ∈ D.carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (groundGammaFunctionGraphLift f) =
      nativeTorusClass B * nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind P.source := by
  have hcomplete : ∀ x ∈ P.source.carrier, ∃ γ, Fin.snoc (rvUnitTupleValues x) γ ∈ D.carrier := by
    intro x hx
    exact ⟨(f ⟨x,hx⟩).val, (hrow ⟨x,hx⟩ _).mp rfl⟩
  exact (nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (GammaGroundBijection.ofCarrierEq (P.reconstructedTorsorDomain_graphLift f D hrow).symm)).trans
      (P.reconstructedTorsor_value h00 linear hκ hs hr hγ hΓ kind D hD hcomplete)

end DiamondIntegral.Section5
