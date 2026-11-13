import «section 3».ResidueGammaProductNeighborhoods
import «section 3».RVUnitRectangularMonomials
import «section 3».RVUnitTupleOperations
import «section 3».GammaGroundMapPreimages
import «section 3».NamedBijections
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

/-- A definable product formula valid on an entire value fibre extends
to an original-ground RES/Gamma product neighbourhood. Domain membership
and both output formulas are preserved together. -/
theorem gammaGroundRVProduct_formula_neighborhood {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (C : Matrix (Fin m) (Fin m) ℤ)
    (c : GammaGroundMap R (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
    (s : GammaGroundMap R (GammaGroundDefSet.univ hc B (rawRVUnitSpace p)))
    (r : R) (γ : Fin m → Values.Gamma (M := M))
    (hfull : ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues u = γ →
      ∃ t : T, t.val = (u,r.val) ∧ (f t).val = (fun i => (c r).val i * integerMonomialMap C u i) ∧ (g t).val = (s r).val) :
    ∃ (A : GammaGroundDefSet hc B (rawRVUnitSpace n))
      (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
      (hsub : A.carrier ⊆ R.carrier), r.val ∈ A.carrier ∧ γ ∈ G.carrier ∧
      ∀ a : A, ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues u ∈ G.carrier →
        ∃ t : T, t.val = (u,a.val) ∧
          (f t).val = (fun i => (c ⟨a.val,hsub a.property⟩).val i * integerMonomialMap C u i) ∧
          (g t).val = (s ⟨a.val,hsub a.property⟩).val := by
  let U := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)
  let K := R.prod U
  let proj := GammaGroundMap.prodFst R U
  let mon := (gammaGroundRVUnitRectangularMonomialMap U C).comp (GammaGroundMap.prodSnd R U)
  let cf := c.comp proj
  let free := (gammaGroundRVUnitTupleMulMap (U.prod U)).comp (cf.pair mon)
  let res := s.comp proj
  let source := GammaGroundMap.ofGlobal K
    (GammaGroundDefSet.univ hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (universalProductSwap (rawRVUnitSpace n) (rawRVUnitSpace m) B.real) (fun _ => Set.mem_univ _)
  let guess := (source.pair (free.pair res).toUniv).toUniv
  let J : GammaGroundDefSet hc B
      (((rawRVUnitSpace m).prod (rawRVUnitSpace n)).prod ((rawRVUnitSpace m).prod (rawRVUnitSpace p))) :=
    ⟨{z | ∃ t : T, t.val = z.1 ∧ ((f.pair g) t).val = z.2},(f.pair g).graph_definable⟩
  let Good := guess.preimage J
  let Bad := K.sdiff Good
  have hNoBad : ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = γ → (r.val,u) ∉ Bad.carrier := by
    intro u hu hbad
    obtain ⟨t,ht,hf,hg⟩ := hfull u hu
    apply hbad.2
    let a : K := ⟨(r.val,u),r.property,Set.mem_univ _⟩
    refine ⟨a,rfl,t,ht,?_⟩
    exact Prod.ext hf hg
  obtain ⟨A,G,hAR,hrA,hγG,havoid⟩ := gammaGroundRES_full_fibre_avoidance_neighborhood
    hκ hs h00 hsmall hγsmall hΓ R hR Bad r γ hNoBad
  refine ⟨A,G,hAR,hrA,hγG,?_⟩
  intro a u hu
  have hGood : (a.val,u) ∈ Good.carrier := by
    by_contra hnot
    exact havoid a.val a.property u hu ⟨⟨hAR a.property,Set.mem_univ _⟩,hnot⟩
  obtain ⟨q,hq,hqJ⟩ := hGood
  have he : q = (⟨(a.val,u),hAR a.property,Set.mem_univ _⟩ : K) := Subtype.ext hq
  rw [he] at hqJ
  change ∃ t : T, t.val = (u,a.val) ∧
    ((f t).val,(g t).val) =
      ((fun i => (c ⟨a.val,hAR a.property⟩).val i * integerMonomialMap C u i),(s ⟨a.val,hAR a.property⟩).val) at hqJ
  obtain ⟨t,ht,hfg⟩ := hqJ
  exact ⟨t,ht,congrArg Prod.fst hfg,congrArg Prod.snd hfg⟩
end DiamondIntegral.Section3
