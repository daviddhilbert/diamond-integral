import «section 3».GammaNativeTranslations
import «section 3».GammaGroundMapPreimages
import «section 3».GammaGroundIntegralMonomialImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaAffineValue (C : Matrix (Fin n) (Fin n) ℤ) (δ γ : Fin n → Values.Gamma (M := M)) :
    Fin n → Values.Gamma (M := M) := fun i => δ i * integerMonomialMap C γ i

/-- Native affine Gamma preimages use only the original definable value
constants and do not select coefficient RV points. -/
def gammaGroundGammaAffinePreimage (V : GammaGroundGammaPiece hc B n)
    (C : Matrix (Fin n) (Fin n) ℤ) (δ : Fin n → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) : GammaGroundGammaPiece hc B n := by
  let f := fun i (γ : Fin n → Values.Gamma (M := M)) => gammaAffineValue C δ γ i
  have hf : ∀ i, FullGammaFunction (integrationGammaBase B) (f i) := by
    intro i
    apply (FullGammaFunction.constant (δ i) (integrationGammaDefinable (hδ i))).mul
    exact FullGammaFunction.prod Finset.univ
      (fun j (γ : Fin n → Values.Gamma (M := M)) => γ j ^ C i j)
      (fun j _ => (FullGammaFunction.proj (integrationGammaBase B) j).zpow (C i j))
  have hV := (gammaGroundGammaPower_definable_iff V.carrier).mp V.definable
  exact ⟨{γ | gammaAffineValue C δ γ ∈ V.carrier},
    gammaGroundGammaPower_predicate_definable _ (FullGammaFunction.substitute hV f hf)⟩

/-- The existing monomial image and value translation give precisely
the set-theoretic native affine image. -/
theorem gammaGroundGammaAffineImage_mem (G : GammaGroundGammaPiece hc B n)
    (C : Matrix (Fin n) (Fin n) ℤ) (δ : Fin n → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) (η : Fin n → Values.Gamma (M := M)) :
    η ∈ (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ).carrier ↔
      ∃ γ : Fin n → Values.Gamma (M := M), γ ∈ G.carrier ∧ gammaAffineValue C δ γ = η := by
  constructor
  · intro hη
    change (fun i => (δ i)⁻¹ * η i) ∈ (gammaGroundMonomialValueImage G C).carrier at hη
    obtain ⟨γ,hγ,hC⟩ := (gammaGroundMonomialValueImage_mem G C _).mp hη
    refine ⟨γ,hγ,?_⟩
    funext i
    change δ i * integerMonomialMap C γ i = η i
    rw [congrFun hC i]
    exact mul_inv_cancel_left _ _
  · rintro ⟨γ,hγ,hφ⟩
    have hmono : integerMonomialMap C γ ∈ (gammaGroundMonomialValueImage G C).carrier :=
      (gammaGroundMonomialValueImage_mem G C _).mpr ⟨γ,hγ,rfl⟩
    have hs := (gammaGroundGammaTranslate_shift (gammaGroundMonomialValueImage G C) δ hδ
      (integerMonomialMap C γ)).mp hmono
    change gammaAffineValue C δ γ ∈ (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ).carrier at hs
    exact hφ ▸ hs

/-- Cutting the target of a native affine image is the image of an
original-ground product-factor preimage. Empty pieces are retained. -/
theorem gammaGroundGammaAffineImage_restrict_target
    (G V : GammaGroundGammaPiece hc B n)
    (C : Matrix (Fin n) (Fin n) ℤ) (δ : Fin n → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hV : V.carrier ⊆ (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ).carrier) :
    gammaGroundGammaTranslate
      (gammaGroundMonomialValueImage (G.inter (gammaGroundGammaAffinePreimage V C δ hδ)) C) δ hδ = V := by
  apply gammaGroundDefSet_eq_of_carrier_eq
  ext η
  change Fin n → Values.Gamma (M := M) at η
  rw [gammaGroundGammaAffineImage_mem]
  constructor
  · rintro ⟨γ,hγ,hφ⟩
    exact hφ ▸ hγ.2
  · intro hη
    obtain ⟨γ,hγ,hφ⟩ := (gammaGroundGammaAffineImage_mem G C δ hδ η).mp (hV hη)
    have hpre : gammaAffineValue C δ γ ∈ V.carrier := hφ.symm ▸ hη
    exact ⟨γ,⟨hγ,hpre⟩,hφ⟩

/-- Cutting the target of a definable partial map pulls back to its
actual source and has exactly the prescribed image. -/
theorem GammaGroundMap.image_restrict_preimage {Q V : Space LRV M}
    {D : GammaGroundDefSet hc B Q} {E : GammaGroundDefSet hc B V}
    (f : GammaGroundMap D E) (Z : GammaGroundDefSet hc B V) (hZ : Z.carrier ⊆ f.image.carrier) :
    (f.restrict (f.preimage_subset Z)).image = Z := by
  apply gammaGroundDefSet_eq_of_carrier_eq
  ext z
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨a0,ha0,hfZ⟩ := a.property
    have he : (⟨a.val,f.preimage_subset Z a.property⟩ : D) = a0 := Subtype.ext ha0.symm
    change (f ⟨a.val,f.preimage_subset Z a.property⟩).val = z at ha
    rw [he] at ha
    exact ha ▸ hfZ
  · intro hz
    obtain ⟨a,ha⟩ := hZ hz
    change (f a).val = z at ha
    have haZ : (f a).val ∈ Z.carrier := ha.symm ▸ hz
    let b : f.preimage Z := ⟨a.val,a,rfl,haZ⟩
    exact ⟨b,ha⟩
end DiamondIntegral.Section3
