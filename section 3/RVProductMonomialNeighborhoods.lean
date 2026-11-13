import «section 3».RVProductFibreMonomials
import «section 3».RVProductFormulaNeighborhoods
import «section 3».RESCoefficientNeighborhoods
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

/-- An actual jointly injective product map has an original-ground
unimodular monomial formula near every Gamma-independent fibre, with
RES-dependent coefficients and a constant original-ground value tuple. -/
theorem gammaGroundRVProduct_monomial_neighborhood {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (hS : (rvUnitTupleValues '' S.carrier).Finite)
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) (r : R)
    (x : gammaGroundRealPointFibre T ⟨rvUnitValues r.val,Set.mem_range_self _⟩)
    (hxg : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) :
    ∃ (C : Matrix (Fin m) (Fin m) ℤ) (_hC : IsUnit C.det)
      (A : GammaGroundDefSet hc B (rawRVUnitSpace n))
      (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
      (_hsub : A.carrier ⊆ R.carrier)
      (c : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m)))
      (s : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace p)))
      (δ : Fin m → Values.Gamma (M := M)),
      r.val ∈ A.carrier ∧ rvUnitTupleValues x.val ∈ G.carrier ∧
      (∀ j, GammaDefinableClosureAtBase B (δ j)) ∧
      (∀ a : A, rvUnitTupleValues (c a).val = δ) ∧
      ∀ a : A, ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues u ∈ G.carrier →
        ∃ t : T, t.val = (u,a.val) ∧
          (f t).val = (fun i => (c a).val i * integerMonomialMap C u i) ∧ (g t).val = (s a).val := by
  obtain ⟨C,hC,c0,s0,hc0,hs0,hformula⟩ := gammaGroundRVProduct_generic_fibre_monomial
    hκ hs h00 hsmall hγsmall hΓ R hR T D S hS f g hjoint r x hxg
  obtain ⟨Rc,hRc,hrc,c,hcc,hδ,hcval⟩ := gammaGroundRES_coefficient_constant_value_neighborhood
    hκ hs h00 hsmall R hR r c0 hc0
  obtain ⟨Rs,hrs,s,hss⟩ := gammaGroundRVUnitCoefficient_function r.val s0 hs0
  let R0 := Rc.inter Rs
  let r0 : R0 := ⟨r.val,hrc,hrs⟩
  let c1 := c.restrict (show R0.carrier ⊆ Rc.carrier from fun _ h => h.1)
  let s1 := s.restrict (show R0.carrier ⊆ Rs.carrier from fun _ h => h.2)
  have hR0 : R0.carrier ⊆ R.carrier := fun _ h => hRc h.1
  have hfin : (rvUnitTupleValues '' R0.carrier).Finite := hR.subset (Set.image_mono hR0)
  let cr : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
  let A0 := gammaGroundRealPointFibre T cr
  have hsmallC : Cardinal.mk (adjoinRVUnitTuple B r.val).real < κ :=
    small_union_range hκ B.real hsmall (rvUnitValues r.val)
  have hxC : GammaTupleIndependentOver (adjoinRVUnitTuple B r.val) (rvUnitTupleValues x.val) :=
    (gammaGroundRVUnit_residue_gamma_independent_iff hκ hs h00 hsmall R hR r _).mpr hxg
  have hfull : ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = rvUnitTupleValues x.val →
      ∃ t : T, t.val = (u,r0.val) ∧
        (f t).val = (fun i => (c1 r0).val i * integerMonomialMap C u i) ∧ (g t).val = (s1 r0).val := by
    intro u hu
    have huA := gammaGroundRVUnit_generic_value_fibre_invariant hκ hs h00 hsmallC A0 x hxC u hu.symm
    let y : A0 := ⟨u,huA⟩
    have hsrc : (u,r.val) ∈ T.carrier := by
      change (u,(rawRVUnitSpace n).decode cr) ∈ T.carrier at huA
      rw [show (rawRVUnitSpace n).decode cr = r.val from decode_rvUnitValues r.val] at huA
      exact huA
    let t : T := ⟨(u,r.val),hsrc⟩
    have hyT : (⟨(y.val,(rawRVUnitSpace n).decode cr),y.property⟩ : T) = t := by
      apply Subtype.ext
      exact Prod.ext rfl (decode_rvUnitValues r.val)
    obtain ⟨hf,hg⟩ := hformula y hu
    rw [GammaGroundMap.fibreSource_value,hyT] at hf hg
    refine ⟨t,rfl,?_,?_⟩
    · rw [show (c1 r0).val = c0 from hcc]
      exact hf
    · rw [show (s1 r0).val = s0 from hss]
      exact hg
  obtain ⟨A,G,hA,hrA,hxG,hrect⟩ := gammaGroundRVProduct_formula_neighborhood
    hκ hs h00 hsmall hγsmall hΓ R0 hfin T D S f g C c1 s1 r0 (rvUnitTupleValues x.val) hfull
  let cf := c1.restrict hA
  let sf := s1.restrict hA
  refine ⟨C,hC,A,G,hA.trans hR0,cf,sf,rvUnitTupleValues c0,hrA,hxG,hδ,?_,?_⟩
  · intro a
    exact hcval ⟨a.val,(hA a.property).1⟩
  · intro a u hu
    exact hrect a u hu
end DiamondIntegral.Section3
