import «section 5».MonomialTorsorEvaluation

/-! An additional RV coordinate is retained literally under a monomial
coordinate change on the base. Arbitrary reconstructed Gamma supports
therefore give actual original-ground product bijections. -/
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

def GroundMonomialPiece.extraGammaSource (P : GroundMonomialPiece X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1)))) :=
  P.torsorCoordinateBijection.inverseImage (P.residue.prod (gammaGroundRVUnitGammaPreimage K))

theorem GroundMonomialPiece.extraGammaTarget_subset (P : GroundMonomialPiece X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1))))
    (hproj : ∀ η γ, Fin.snoc η γ ∈ K.carrier → η ∈ P.gamma.carrier) :
    (P.residue.prod (gammaGroundRVUnitGammaPreimage K)).carrier ⊆
      (P.residue.prod (unitTupleLastCylinder (gammaGroundRVUnitGammaPreimage P.gamma))).carrier := by
  intro a ha
  refine ⟨ha.1, (unitTupleLastCylinder_mem _ a.2).mpr ?_⟩
  apply hproj (rvUnitTupleValues (Fin.init a.2)) (rvUnitValueHom (a.2 (Fin.last P.split.freeArity)))
  have he : Fin.snoc (rvUnitTupleValues (Fin.init a.2)) (rvUnitValueHom (a.2 (Fin.last P.split.freeArity))) = rvUnitTupleValues a.2 := by
    rw [← rvUnitTupleValues_snoc, Fin.snoc_init_self]
  exact he.symm ▸ ha.2

def GroundMonomialPiece.extraGammaBijection (P : GroundMonomialPiece X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1))))
    (hproj : ∀ η γ, Fin.snoc η γ ∈ K.carrier → η ∈ P.gamma.carrier) :
    GammaGroundBijection (P.extraGammaSource K) (P.residue.prod (gammaGroundRVUnitGammaPreimage K)) :=
  P.torsorCoordinateBijection.restrictTarget _ (P.extraGammaTarget_subset K hproj)

theorem GroundMonomialPiece.extraGammaSource_mem (P : GroundMonomialPiece X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1))))
    (p : (Fin n → (CanonicalRV.RVSort M)ˣ) × (Fin 1 → (CanonicalRV.RVSort M)ˣ)) :
    p ∈ (P.extraGammaSource K).carrier ↔ p.1 ∈ P.source.carrier ∧
      Fin.snoc (rvUnitTupleValues (P.cell.coordinateEquiv P.split p.1).2) (rvUnitValueHom (p.2 0)) ∈ K.carrier := by
  constructor
  · rintro ⟨a, ha, hz⟩
    subst p
    rw [P.torsorCoordinateBijection_value a] at hz
    have ht : rvUnitTupleValues (Fin.snoc
        (α := fun _ : Fin (P.split.freeArity+1) => (CanonicalRV.RVSort M)ˣ)
        (P.cell.coordinateEquiv P.split a.val.1).2 (a.val.2 0)) ∈ K.carrier := hz.2
    rw [rvUnitTupleValues_snoc] at ht
    exact ⟨a.property.1, ht⟩
  · rintro ⟨hx, hK⟩
    let a : P.source.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1)) := ⟨p,hx,Set.mem_univ _⟩
    refine ⟨a,rfl,?_⟩
    rw [P.torsorCoordinateBijection_value a]
    refine ⟨((P.coordinate_mem_iff p.1).mpr hx).1, ?_⟩
    change rvUnitTupleValues (Fin.snoc
      (α := fun _ : Fin (P.split.freeArity+1) => (CanonicalRV.RVSort M)ˣ)
      (P.cell.coordinateEquiv P.split p.1).2 (p.2 0)) ∈ K.carrier
    rw [rvUnitTupleValues_snoc]
    exact hK

def GroundMonomialPiece.extraGammaDomain (P : GroundMonomialPiece X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1)))) :=
  (gammaGroundRVUnitTupleProductMap (P.extraGammaSource K)).image

def GroundMonomialPiece.extraGammaProductBijection (P : GroundMonomialPiece X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1))))
    (hproj : ∀ η γ, Fin.snoc η γ ∈ K.carrier → η ∈ P.gamma.carrier) :
    GammaGroundBijection (P.extraGammaDomain K)
      (gammaGroundRVUnitTupleProductMap (P.residue.prod (gammaGroundRVUnitGammaPreimage K))).image :=
  (gammaGroundRVUnitTupleProductBijection _).comp
    ((P.extraGammaBijection K hproj).comp (gammaGroundRVUnitTupleProductBijection _).symm)

theorem GroundMonomialPiece.extraGamma_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (P : GroundMonomialPiece X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1))))
    (hproj : ∀ η γ, Fin.snoc η γ ∈ K.carrier → η ∈ P.gamma.carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (P.extraGammaDomain K) =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind P.residue *
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind (P.split.freeArity+1)
        (GammaIndicators.indicatorFamily B K.carrier (Section3GammaChartBridge.chart K).support_definable) :
          RESDimensionFreeReduction.Ring B) * nativeTorusClass B ^ (P.split.freeArity+1) := by
  rw [nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (P.extraGammaProductBijection K hproj), nativeUnitRVSetValue_product, nativeUnitRVSetValue_gamma]
  ring

end DiamondIntegral.Section5
