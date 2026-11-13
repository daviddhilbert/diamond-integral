import «section 3».UnimodularMonomialFibres
import «section 3».RVProductMonomialNeighborhoods
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3

/-- When every free fibre is mapped onto the same target fibre, joint
injectivity forces injectivity of the retained parameter map. -/
theorem affineMonomial_parameter_injective
    {ι G Γ R S : Type} [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]
    (v : G →* Γ) (C : Matrix ι ι ℤ) (hC : IsUnit C.det)
    (c : R → ι → G) (s : R → S) (U : Set (ι → Γ))
    (hcval : ∀ a b i, v (c a i) = v (c b i))
    (x : ι → G) (hx : (fun i => v (x i)) ∈ U)
    (hjoint : ∀ a b u w, (fun i => v (u i)) ∈ U → (fun i => v (w i)) ∈ U →
      s a = s b → c a * integerMonomialMap C u = c b * integerMonomialMap C w → a = b) :
    Function.Injective s := by
  intro a b hab
  let y := c a * integerMonomialMap C x
  have hvalue : (fun i => v (y i)) = fun i => v ((c b * integerMonomialMap C x) i) := by
    funext i
    change v (c a i * integerMonomialMap C x i) = v (c b i * integerMonomialMap C x i)
    rw [map_mul,map_mul,hcval a b i]
  obtain ⟨u,hu,hcu⟩ := affineMonomial_full_value_fibre_solve v C hC (c b) x y hvalue
  exact hjoint a b x u hx (hu.symm ▸ hx) hab hcu.symm

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m p : ℕ}

/-- On an actual product rectangle with the checked unimodular formula,
the residue output is injective. This constructs the RES isomorphism
onto its image without cancelling any semiring class. -/
theorem gammaGroundRVProduct_residue_output_injective
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (hG : G.carrier.Nonempty)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : IsUnit C.det)
    (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
    (s : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace p)))
    (δ : Fin m → Values.Gamma (M := M))
    (hcval : ∀ a : A, rvUnitTupleValues (c a).val = δ)
    (hformula : ∀ a : A, ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u ∈ G.carrier → ∃ t : T, t.val = (u,a.val) ∧
        (f t).val = (fun i => (c a).val i * integerMonomialMap C u i) ∧ (g t).val = (s a).val) :
    Function.Injective s := by
  obtain ⟨γ,hγ⟩ := hG
  obtain ⟨x,hx⟩ := rvUnitTupleValues_surjective m γ
  let coeff (a : A) : Fin m → (CanonicalRV.RVSort M)ˣ := (c a).val
  have hxG : (fun i => rvUnitValueHom (x i)) ∈ G.carrier := by
    change rvUnitTupleValues x ∈ G.carrier
    exact hx.symm ▸ hγ
  apply affineMonomial_parameter_injective (rvUnitValueHom (M := M)) C hC coeff s G.carrier
    (fun a b i => (congrFun (hcval a) i).trans (congrFun (hcval b) i).symm) x hxG
  intro a b u w hu hw hab hfree
  obtain ⟨ta,hta,hfa,hga⟩ := hformula a u hu
  obtain ⟨tb,htb,hfb,hgb⟩ := hformula b w hw
  have hg : g ta = g tb := by
    apply Subtype.ext
    exact hga.trans ((congrArg Subtype.val hab).trans hgb.symm)
  have hf : f ta = f tb := by
    apply Subtype.ext
    exact hfa.trans (hfree.trans hfb.symm)
  have he := congrArg (fun t : T => t.val.2) (hjoint ta tb hg hf)
  apply Subtype.ext
  exact (congrArg Prod.snd hta).symm.trans (he.trans (congrArg Prod.snd htb))
end DiamondIntegral.Section3
