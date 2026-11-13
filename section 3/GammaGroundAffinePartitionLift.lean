import «section 3».GammaGroundAffineFiniteCover
import «section 3».GammaGroundMapFiniteGluing
import «section 3».GammaGroundUnitFibreDescent
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- Finitely many actual old-ground unimodular formulas glue to a
bijection on the entire RV preimages, contracting to the given Gamma
bijection on every point. -/
theorem gammaGroundAffine_partition_full_lift {N : ℕ}
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (h : GammaGroundBijection G J) (F : Fin N → OriginalGroundAffineRVFormula hc B n)
    (P : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (hP : ∀ i, (P i).carrier ⊆ G.carrier)
    (hcover : ∀ γ : G, ∃! i, γ.val ∈ (P i).carrier)
    (hformula : ∀ i (γ : G), γ.val ∈ (P i).carrier →
      (h.map γ).val = rvUnitTupleValues (F i).coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) (F i).matrix γ.val) :
    ∃ L : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J),
      ∀ u, gammaGroundFullPreimageValueMap J (L.map u) = h.map (gammaGroundFullPreimageValueMap G u) := by
  let A := gammaGroundRVUnitGammaPreimage G
  let D := gammaGroundRVUnitGammaPreimage J
  let U := fun i => gammaGroundRVUnitGammaPreimage (P i)
  have hU : ∀ i, (U i).carrier ⊆ A.carrier := fun i _ hu => hP i hu
  have hUc : ∀ a : A, ∃! i, a.val ∈ (U i).carrier :=
    fun a => hcover (gammaGroundFullPreimageValueMap G a)
  let fi (i : Fin N) := gammaGroundRVUnitAffineMap (U i) (F i).matrix (F i).coefficient (F i).coefficient_definable
  have hval (i : Fin N) (u : U i) : rvUnitTupleValues (fi i u).val =
      (h.map ⟨rvUnitTupleValues u.val,hP i u.property⟩).val := by
    let γ : G := ⟨rvUnitTupleValues u.val,hP i u.property⟩
    have hmem : γ.val ∈ (P i).carrier := u.property
    exact (gammaGroundRVUnitAffineMap_values (U i) (F i).matrix (F i).coefficient
      (F i).coefficient_definable u).trans (hformula i γ hmem).symm
  have hin (i : Fin N) (u : U i) : (fi i u).val ∈ D.carrier := by
    change rvUnitTupleValues (fi i u).val ∈ J.carrier
    rw [hval]
    exact (h.map ⟨rvUnitTupleValues u.val,hP i u.property⟩).property
  let f := fun i => (fi i).corestrict (hin i)
  obtain ⟨L,hL⟩ := gammaGroundMap_of_finite_partition A D U hU hUc f
  have hLv (u : A) : gammaGroundFullPreimageValueMap J (L u) =
      h.map (gammaGroundFullPreimageValueMap G u) := by
    obtain ⟨i,hi,_⟩ := hUc u
    apply Subtype.ext
    rw [hL i u hi]
    exact hval i ⟨u.val,hi⟩
  have hLin : Function.Injective L := by
    intro u v huv
    have hv : gammaGroundFullPreimageValueMap G u = gammaGroundFullPreimageValueMap G v :=
      h.bijective.1 ((hLv u).symm.trans ((congrArg (gammaGroundFullPreimageValueMap J) huv).trans (hLv v)))
    have hvalues : rvUnitTupleValues u.val = rvUnitTupleValues v.val := congrArg Subtype.val hv
    obtain ⟨i,hi,_⟩ := hUc u
    have hvi : v.val ∈ (U i).carrier := by
      change rvUnitTupleValues v.val ∈ (P i).carrier
      have hui : rvUnitTupleValues u.val ∈ (P i).carrier := hi
      exact hvalues ▸ hui
    have he := congrArg Subtype.val huv
    rw [hL i u hi,hL i v hvi] at he
    change (F i).coefficient * integerMonomialMap (F i).matrix u.val =
      (F i).coefficient * integerMonomialMap (F i).matrix v.val at he
    have hm := mul_left_cancel he
    have hback := congrArg (integerMonomialMap (G := (CanonicalRV.RVSort M)ˣ) (F i).matrix⁻¹) hm
    apply Subtype.ext
    simpa only [integerMonomialMap_comp,Matrix.nonsing_inv_mul _ (F i).det_unit,integerMonomialMap_one] using hback
  have hLsur : Function.Surjective L := by
    intro v
    obtain ⟨γ,hγ⟩ := h.bijective.2 (gammaGroundFullPreimageValueMap J v)
    obtain ⟨i,hi,_⟩ := hcover γ
    obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective (M := M) n γ.val
    have hvalformula : rvUnitTupleValues v.val = rvUnitTupleValues (F i).coefficient *
        integerMonomialMap (F i).matrix (rvUnitTupleValues u) := by
      rw [hu]
      exact (congrArg Subtype.val hγ).symm.trans (hformula i γ hi)
    have hrawvalue : (fun j => rvUnitValueHom (v.val j)) =
        fun j => rvUnitValueHom (((F i).coefficient * integerMonomialMap (F i).matrix u) j) := by
      change rvUnitTupleValues v.val = rvUnitTupleValues ((F i).coefficient * integerMonomialMap (F i).matrix u)
      rw [hvalformula]
      exact (gammaGroundRVUnitAffineMap_values
        (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n))
        (F i).matrix (F i).coefficient (F i).coefficient_definable ⟨u,Set.mem_univ _⟩).symm
    obtain ⟨w,hwval,hwe⟩ := affineMonomial_full_value_fibre_solve (rvUnitValueHom (M := M))
      (F i).matrix (F i).det_unit (F i).coefficient u v.val hrawvalue
    have hwγ : rvUnitTupleValues w = γ.val := hwval.trans hu
    have hwA : w ∈ A.carrier := by
      change rvUnitTupleValues w ∈ G.carrier
      exact hwγ.symm ▸ γ.property
    have hwU : w ∈ (U i).carrier := by
      change rvUnitTupleValues w ∈ (P i).carrier
      exact hwγ.symm ▸ hi
    refine ⟨⟨w,hwA⟩,?_⟩
    rw [hL i ⟨w,hwA⟩ hwU]
    exact Subtype.ext hwe
  exact ⟨⟨L,hLin,hLsur⟩,hLv⟩

end DiamondIntegral.Section3
