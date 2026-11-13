import «section 3».GammaGroundMonomialFibreDescent
import «section 3».RVUnitRectangularMonomials
import «section 3».GammaGroundGammaSemiring
import «section 3».UnimodularMonomialFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- The Gamma image of an integral monomial is defined from the actual
RV map, retaining all value representatives and the original ground. -/
def gammaGroundMonomialValueImage (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) : GammaGroundGammaPiece hc B n :=
  ((GammaGroundMap.ofGlobal (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))
    (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp
      (gammaGroundRVUnitRectangularMonomialMap (gammaGroundRVUnitGammaPreimage G) A)).image

theorem gammaGroundMonomialValueImage_mem (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) (η : Fin n → Values.Gamma (M := M)) :
    η ∈ (gammaGroundMonomialValueImage G A).carrier ↔
      ∃ γ : Fin n → Values.Gamma (M := M), γ ∈ G.carrier ∧ integerMonomialMap A γ = η := by
  constructor
  · rintro ⟨u,hu⟩
    change rvUnitTupleValues (integerMonomialMap A u.val) = η at hu
    have hv : rvUnitTupleValues (integerMonomialMap A u.val) =
        integerMonomialMap A (rvUnitTupleValues u.val) := monomial_map_value (rvUnitValueHom (M := M)) A u.val
    exact ⟨rvUnitTupleValues u.val,u.property,hv.symm.trans hu⟩
  · rintro ⟨γ,hγ,hη⟩
    obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective n γ
    have huG : u ∈ (gammaGroundRVUnitGammaPreimage G).carrier := by
      change rvUnitTupleValues u ∈ G.carrier
      exact hu.symm ▸ hγ
    refine ⟨⟨u,huG⟩,?_⟩
    change rvUnitTupleValues (integerMonomialMap A u) = η
    have hv : rvUnitTupleValues (integerMonomialMap A u) = integerMonomialMap A (rvUnitTupleValues u) :=
      monomial_map_value (rvUnitValueHom (M := M)) A u
    exact hv.trans ((congrArg (integerMonomialMap A) hu).trans hη)

def gammaGroundIntegralMonomialMap (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    GammaGroundMap (gammaGroundRVUnitGammaPreimage G)
      (gammaGroundRVUnitGammaPreimage (gammaGroundMonomialValueImage G A)) :=
  (gammaGroundRVUnitRectangularMonomialMap (gammaGroundRVUnitGammaPreimage G) A).corestrict
    (fun u => ⟨u,rfl⟩)

@[simp] theorem gammaGroundIntegralMonomialMap_value (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) (u : gammaGroundRVUnitGammaPreimage G) :
    (gammaGroundIntegralMonomialMap G A u).val = integerMonomialMap A u.val := rfl

theorem gammaGroundIntegralMonomialMap_bijective (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det) :
    Function.Bijective (gammaGroundIntegralMonomialMap G A) := by
  constructor
  · intro u v he
    have hh := congrArg Subtype.val he
    change integerMonomialMap A u.val = integerMonomialMap A v.val at hh
    have hi := congrArg (integerMonomialMap (G := (CanonicalRV.RVSort M)ˣ) A⁻¹) hh
    apply Subtype.ext
    simpa only [integerMonomialMap_comp,Matrix.nonsing_inv_mul A hA,integerMonomialMap_one] using hi
  · intro v
    obtain ⟨u,hu⟩ := v.property
    change rvUnitTupleValues (integerMonomialMap A u.val) = rvUnitTupleValues v.val at hu
    have hv : (fun i => rvUnitValueHom (v.val i)) =
        fun i => rvUnitValueHom (((1 : Fin n → (CanonicalRV.RVSort M)ˣ) * integerMonomialMap A u.val) i) := by
      simp only [one_mul]
      change rvUnitTupleValues v.val = rvUnitTupleValues (integerMonomialMap A u.val)
      exact hu.symm
    obtain ⟨w,hwval,hwe⟩ := affineMonomial_full_value_fibre_solve (rvUnitValueHom (M := M)) A hA 1 u.val v.val hv
    change rvUnitTupleValues w = rvUnitTupleValues u.val at hwval
    rw [one_mul] at hwe
    have hw : w ∈ (gammaGroundRVUnitGammaPreimage G).carrier := by
      change rvUnitTupleValues w ∈ G.carrier
      rw [hwval]
      exact u.property
    exact ⟨⟨w,hw⟩,Subtype.ext hwe⟩

/-- Pure unimodular monomials give the actual same-ground Gamma morphism,
including its RV code lift. No coefficient RV point is selected. -/
def gammaGroundGammaSingleMonomialHom (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det) :
    GammaGroundGammaHom (GammaGroundGammaObject.single G)
      (GammaGroundGammaObject.single (gammaGroundMonomialValueImage G A)) :=
  gammaGroundGammaSingleHomOfAffineMonomial G (gammaGroundMonomialValueImage G A)
    ⟨gammaGroundIntegralMonomialMap G A,gammaGroundIntegralMonomialMap_bijective G A hA⟩ A hA 1
      (fun u => by rw [one_mul]; rfl)

theorem gammaGroundGammaSemiringClass_monomial_image (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundMonomialValueImage G A)) :=
  gammaGroundGammaSemiringClass_iso (asIso (show _ ⟶ _ from gammaGroundGammaSingleMonomialHom G A hA))
end DiamondIntegral.Section3
