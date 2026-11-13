import «section 3».RVNormalizedMapRelations
import «section 3».AlgebraicallyClosedCharacters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}
variable {A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
variable {D : GammaGroundDefSet hc B (rawRVSpace (M := M) m)}

theorem rvNormalizedMapRelation_character_invariant (f : GammaGroundMap A D)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (b : Fin m → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) (y : Fin m → ModelResidue M)
    (hxy : Sum.elim x y ∈ rvNormalizedMapRelation f a b)
    (ψ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ) :
    Sum.elim (fun i => (rvCharacterResidueScalar B ψ (a i) : ModelResidue M) * x i)
      (fun j => (rvCharacterResidueScalar B ψ (b j) : ModelResidue M) * y j) ∈
        rvNormalizedMapRelation f a b := by
  obtain ⟨u,hu,hf⟩ := hxy
  obtain ⟨v,hv,hvf⟩ := gammaGroundRVMap_character_equivariant B ψ A D f u
  refine ⟨v,?_,?_⟩
  · rw [hu] at hv
    exact hv.trans (funext fun i => rvOriginalGroundCharacterTwistZero_normalized B ψ (a i) (x i))
  · rw [hf] at hvf
    exact hvf.trans (funext fun j => rvOriginalGroundCharacterTwistZero_normalized B ψ (b j) (y j))

/-- A character of the finitely generated weight group extends to the
actual original-ground value quotient and therefore preserves the actual
normalized RV graph with precisely the prescribed residue scalars. -/
theorem rvNormalizedMapRelation_weight_character_invariant
    {W : Type*} [AddCommGroup W] (E : Subfield (ModelResidue M))
    (ι : Multiplicative W →* (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B))
    (hι : Function.Injective ι) (f : GammaGroundMap A D)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (b : Fin m → (CanonicalRV.RVSort M)ˣ)
    (w : Fin n → W) (z : Fin m → W)
    (ha : ∀ i, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (a i)) = ι (Multiplicative.ofAdd (w i)))
    (hb : ∀ j, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom (b j)) = ι (Multiplicative.ofAdd (z j)))
    (x : Fin n → ModelResidue M) (y : Fin m → ModelResidue M)
    (hxy : Sum.elim x y ∈ rvNormalizedMapRelation f a b)
    (χ : Multiplicative W →* Eˣ) :
    Sum.elim (fun i => (((χ (Multiplicative.ofAdd (w i)) : E) : ModelResidue M) * x i))
      (fun j => (((χ (Multiplicative.ofAdd (z j)) : E) : ModelResidue M) * y j)) ∈
        rvNormalizedMapRelation f a b := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let ρ : Eˣ →* (ModelResidue M)ˣ := Units.map E.subtype.toMonoidHom
  obtain ⟨ψ,hψ⟩ := algebraicallyClosed_character_extends ι hι (ρ.comp χ)
  have hs (u : (CanonicalRV.RVSort M)ˣ) (v : W)
      (hv : QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom u) = ι (Multiplicative.ofAdd v)) :
      (rvCharacterResidueScalar B ψ u : ModelResidue M) = ((χ (Multiplicative.ofAdd v) : E) : ModelResidue M) := by
    change (ψ (QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom u)) : ModelResidue M) = _
    rw [hv]
    exact congrArg Units.val (DFunLike.congr_fun hψ (Multiplicative.ofAdd v))
  have h := rvNormalizedMapRelation_character_invariant f a b x y hxy ψ
  simpa only [hs _ _ (ha _),hs _ _ (hb _)] using h

end DiamondIntegral.Section3
