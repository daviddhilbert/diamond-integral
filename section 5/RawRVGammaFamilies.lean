import «section 5».RVGammaFamilyLifts
import «section 5».NativeRVSetValues
import «section 3».RVNonzeroTupleCoding
import «section 3».GammaGroundRVProductLaws

/-! Zero entries of an RV base are encoded by the proved original-ground
nonzero tuple coding. Every Gamma coordinate and its fibre are retained. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def rawRVGammaBaseCode (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :=
  (gammaGroundRVNonzeroTupleCodeMap X).image

def rawRVGammaFamilyCodeMap (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :=
  (gammaGroundRVNonzeroTupleCodeBijection h00 X).symm.prodMap
    (GammaGroundBijection.id (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))))

def rawRVGammaFamilyCode (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :=
  (rawRVGammaFamilyCodeMap (n := n) h00 X).inverseImage T

theorem rawRVGammaFamilyCode_row (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : rawRVGammaBaseCode X) (γ : Fin n → Values.Gamma (M := M)) :
    (x.val,γ) ∈ (rawRVGammaFamilyCode h00 X T).carrier ↔
      (((gammaGroundRVNonzeroTupleCodeBijection h00 X).symm.map x).val,γ) ∈ T.carrier := by
  let a : (rawRVGammaBaseCode X).prod (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))) :=
    ⟨(x.val,γ),x.property,Set.mem_univ _⟩
  constructor
  · rintro ⟨b,hb,ht⟩
    have he : b = a := Subtype.ext hb
    rw [he] at ht
    exact ht
  · intro ht
    exact ⟨a,rfl,ht⟩

theorem rawRVGammaFamilyCode_projection (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin (p*2) → (CanonicalRV.RVSort M)ˣ) (γ : Fin n → Values.Gamma (M := M))
    (h : (x,γ) ∈ (rawRVGammaFamilyCode h00 X T).carrier) : x ∈ (rawRVGammaBaseCode X).carrier := by
  obtain ⟨a,ha,_⟩ := h
  have hx : a.val.1 = x := congrArg Prod.fst ha
  exact hx ▸ a.property.1

def rawRVGammaLift (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :=
  rvGammaFamilyLift (rawRVGammaFamilyCode h00 X T)

theorem nativeRVSetValue_nonzero_code
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rawRVGammaBaseCode X) := by
  exact nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    ((gammaGroundRVUnitPresentationBijection (rawRVGammaBaseCode X)).comp
      (gammaGroundRVNonzeroTupleCodeBijection h00 X))

end DiamondIntegral.Section5
