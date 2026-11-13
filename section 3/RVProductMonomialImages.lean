import «section 3».AffineProductResidueInjection
import «section 3».RVCoefficientTranslations
import «section 3».GammaGroundIntegralMonomialImages
import «section 3».GammaNativeTranslations
import «section 3».GammaGroundBijectionProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m p : ℕ}

/-- The actual image chart for a unimodular affine product formula.
The coefficient remains a function of the retained RES parameter. -/
def gammaGroundRVUnitAffineProductBijection
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : GammaGroundGammaPiece hc B m)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : IsUnit C.det)
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
    (s : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace p)))
    (hs : Function.Injective s)
    (δ : Fin m → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hcval : ∀ a : A, rvUnitTupleValues (c a).val = δ) :
    GammaGroundBijection (A.prod (gammaGroundRVUnitGammaPreimage G))
      (s.image.prod (gammaGroundRVUnitGammaPreimage
        (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ))) := by
  let mono : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G)
      (gammaGroundRVUnitGammaPreimage (gammaGroundMonomialValueImage G C)) :=
    ⟨gammaGroundIntegralMonomialMap G C,gammaGroundIntegralMonomialMap_bijective G C hC⟩
  let E1 := (GammaGroundBijection.id A).prodMap mono
  let E2 := gammaGroundRVUnitCoefficientTranslation A (gammaGroundMonomialValueImage G C)
    (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ) c δ hcval
    (gammaGroundGammaTranslate_shift _ δ hδ)
  let es : GammaGroundBijection A s.image := ⟨s.toImage,s.toImage_bijective hs⟩
  let E3 := es.prodMap (GammaGroundBijection.id (gammaGroundRVUnitGammaPreimage
    (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ)))
  exact E3.comp (E2.comp E1)

@[simp] theorem gammaGroundRVUnitAffineProductBijection_value
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : GammaGroundGammaPiece hc B m)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : IsUnit C.det)
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
    (s : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace p)))
    (hs : Function.Injective s)
    (δ : Fin m → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hcval : ∀ a : A, rvUnitTupleValues (c a).val = δ)
    (z : A.prod (gammaGroundRVUnitGammaPreimage G)) :
    ((gammaGroundRVUnitAffineProductBijection A G C hC c s hs δ hδ hcval).map z).val =
      ((s ⟨z.val.1,z.property.1⟩).val,
        fun i => (c ⟨z.val.1,z.property.1⟩).val i * integerMonomialMap C z.val.2 i) := rfl

/-- The product neighbourhood maps onto its entire stated product image.
In particular the target Gamma domain is not merely a containing set. -/
theorem gammaGroundRVProduct_monomial_rectangle_image
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : GammaGroundGammaPiece hc B m) (hG : G.carrier.Nonempty)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : IsUnit C.det)
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
    (s : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace p)))
    (δ : Fin m → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hcval : ∀ a : A, rvUnitTupleValues (c a).val = δ)
    (hformula : ∀ a : A, ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u ∈ G.carrier → ∃ t : T, t.val = (u,a.val) ∧
        (f t).val = (fun i => (c a).val i * integerMonomialMap C u i) ∧ (g t).val = (s a).val)
    (b : Fin p → (CanonicalRV.RVSort M)ˣ) (v : Fin m → (CanonicalRV.RVSort M)ˣ) :
    (b ∈ s.image.carrier ∧ v ∈ (gammaGroundRVUnitGammaPreimage
      (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ)).carrier) ↔
    ∃ t : T, t.val.2 ∈ A.carrier ∧ rvUnitTupleValues t.val.1 ∈ G.carrier ∧
      (g t).val = b ∧ (f t).val = v := by
  have hs := gammaGroundRVProduct_residue_output_injective A G hG T D S f g hjoint C hC c s δ hcval hformula
  let E := gammaGroundRVUnitAffineProductBijection A G C hC c s hs δ hδ hcval
  constructor
  · intro hb
    obtain ⟨z,hz⟩ := E.bijective.2 ⟨(b,v),hb⟩
    let a : A := ⟨z.val.1,z.property.1⟩
    obtain ⟨t,ht,hf,hg⟩ := hformula a z.val.2 z.property.2
    have he := congrArg Subtype.val hz
    change ((s a).val,fun i => (c a).val i * integerMonomialMap C z.val.2 i) = (b,v) at he
    refine ⟨t,?_,?_,hg.trans (congrArg Prod.fst he),hf.trans (congrArg Prod.snd he)⟩
    · rw [ht]
      exact a.property
    · rw [ht]
      exact z.property.2
  · rintro ⟨t,ha,hu,hg,hf⟩
    let a : A := ⟨t.val.2,ha⟩
    obtain ⟨t',ht',hf',hg'⟩ := hformula a t.val.1 hu
    have htt : t' = t := Subtype.ext (ht'.trans (Prod.eta t.val))
    subst t'
    let z : A.prod (gammaGroundRVUnitGammaPreimage G) := ⟨(a.val,t.val.1),a.property,hu⟩
    have he : (E.map z).val = (b,v) := by
      change ((s a).val,fun i => (c a).val i * integerMonomialMap C t.val.1 i) = (b,v)
      exact Prod.ext (hg'.symm.trans hg) (hf'.symm.trans hf)
    change (b,v) ∈ (s.image.prod (gammaGroundRVUnitGammaPreimage
      (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ))).carrier
    rw [← he]
    exact (E.map z).property

/-- The actual RES image inherits finite value support from the target
RES domain; no new residue closure assumption is added. -/
theorem gammaGroundRVProduct_monomial_residue_image_finite
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : GammaGroundGammaPiece hc B m) (hG : G.carrier.Nonempty)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (hS : (rvUnitTupleValues '' S.carrier).Finite)
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (C : Matrix (Fin m) (Fin m) ℤ)
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
    (s : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace p)))
    (hformula : ∀ a : A, ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u ∈ G.carrier → ∃ t : T, t.val = (u,a.val) ∧
        (f t).val = (fun i => (c a).val i * integerMonomialMap C u i) ∧ (g t).val = (s a).val) :
    (rvUnitTupleValues '' s.image.carrier).Finite := by
  obtain ⟨γ,hγ⟩ := hG
  obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective m γ
  have huG : rvUnitTupleValues u ∈ G.carrier := hu.symm ▸ hγ
  apply hS.subset (Set.image_mono ?_)
  rintro b ⟨a,hab⟩
  obtain ⟨t,_,_,hg⟩ := hformula a u huG
  exact (hg.trans hab) ▸ (g t).property
end DiamondIntegral.Section3
