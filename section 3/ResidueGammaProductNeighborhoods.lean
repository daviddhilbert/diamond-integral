import «section 3».GammaGroundRVUnitProducts
import «section 3».GammaGroundMapProducts
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- Every point of an original-ground definable RES/Gamma relation lies
in an original-ground definable product rectangle in that relation. -/
theorem gammaGroundResidueGamma_product_neighborhood {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace n).prod ((volumeGammaSpace hc).power (Fin m))))
    (hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ R.carrier)
    (r : R) (γ : Fin m → Values.Gamma (M := M)) (hrγ : (r.val,γ) ∈ T.carrier) :
    ∃ (A : GammaGroundDefSet hc B (rawRVUnitSpace n))
      (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))),
      A.carrier ⊆ R.carrier ∧ r.val ∈ A.carrier ∧ γ ∈ G.carrier ∧
      ∀ x ∈ A.carrier, ∀ η ∈ G.carrier, (x,η) ∈ T.carrier := by
  obtain ⟨N,A,G,_,_,hcov⟩ := gammaGroundRVUnitMixed_definable_products
    hκ hs h00 hsmall hγsmall hΓ T R hR hsub
  obtain ⟨i,hri,hγi⟩ := (hcov r.val γ).mp hrγ
  refine ⟨A i,G i,?_,hri,hγi,?_⟩
  · intro x hx
    exact hsub x γ ((hcov x γ).mpr ⟨i,hx,hγi⟩)
  · intro x hx η hη
    exact (hcov x η).mpr ⟨i,hx,hη⟩

/-- Excluding a definable bad set on one entire value fibre extends to
a definable RES/Gamma product neighbourhood, over the original base. -/
theorem gammaGroundRES_full_fibre_avoidance_neighborhood {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (Bad : GammaGroundDefSet hc B ((rawRVUnitSpace n).prod (rawRVUnitSpace m)))
    (r : R) (γ : Fin m → Values.Gamma (M := M))
    (hNoBad : ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = γ → (r.val,u) ∉ Bad.carrier) :
    ∃ (A : GammaGroundDefSet hc B (rawRVUnitSpace n))
      (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))),
      A.carrier ⊆ R.carrier ∧ r.val ∈ A.carrier ∧ γ ∈ G.carrier ∧
      ∀ x ∈ A.carrier, ∀ u : Fin m → (CanonicalRV.RVSort M)ˣ,
        rvUnitTupleValues u ∈ G.carrier → (x,u) ∉ Bad.carrier := by
  let V : Map (DefSet.univ ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace m)) B.real)
      (DefSet.univ ((rawRVUnitSpace n).prod ((volumeGammaSpace hc).power (Fin m))) B.real) :=
    ((Map.prodMap (Map.id (DefSet.univ (rawRVUnitSpace (M := M) n) B.real))
      (rvUnitGammaMap hc B.real m)).toUniv).restrict
        (fun _ _ => ⟨Set.mem_univ _,Set.mem_univ _⟩)
  let D : GammaGroundDefSet hc B ((rawRVUnitSpace n).prod ((volumeGammaSpace hc).power (Fin m))) :=
    ⟨{z | ∃ p ∈ Bad.carrier, (V ⟨p,Set.mem_univ _⟩).val = z},Bad.definable.image V⟩
  let T := (R.prod (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).sdiff D
  have hsub : ∀ x η, (x,η) ∈ T.carrier → x ∈ R.carrier := fun _ _ h => h.1.1
  have hp : (r.val,γ) ∈ T.carrier := by
    refine ⟨⟨r.property,Set.mem_univ _⟩,?_⟩
    rintro ⟨p,hp,he⟩
    have hpr : p.1 = r.val := congrArg Prod.fst he
    have hpγ : rvUnitTupleValues p.2 = γ := congrArg Prod.snd he
    have hpe : p = (r.val,p.2) := Prod.ext hpr rfl
    exact hNoBad p.2 hpγ (hpe ▸ hp)
  obtain ⟨A,G,hAR,hrA,hγG,hrect⟩ := gammaGroundResidueGamma_product_neighborhood
    hκ hs h00 hsmall hγsmall hΓ R hR T hsub r γ hp
  refine ⟨A,G,hAR,hrA,hγG,?_⟩
  intro x hx u hu hbad
  have hgood := (hrect x hx (rvUnitTupleValues u) hu).2
  apply hgood
  exact ⟨(x,u),hbad,rfl⟩
end DiamondIntegral.Section3
