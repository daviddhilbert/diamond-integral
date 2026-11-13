import «section 3».GammaGroundAffineAgreement
import «section 3».GammaGroundCompactness
import «section 3».GammaGroundOrderedCoverPartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- Pointwise old-ground unimodular formulas have a finite definable
partition, with one of the same formulas on every part. -/
theorem gammaGroundAffine_finite_partition {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (h : GammaGroundMap G J)
    (hpoint : ∀ γ : G, ∃ F : OriginalGroundAffineRVFormula hc B n,
      (h γ).val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.val) :
    ∃ N : ℕ, ∃ F : Fin N → OriginalGroundAffineRVFormula hc B n,
      ∃ P : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)),
        (∀ i, (P i).carrier ⊆ G.carrier) ∧
        (∀ γ : G, ∃! i, γ.val ∈ (P i).carrier) ∧
        ∀ i (γ : G), γ.val ∈ (P i).carrier →
          (h γ).val = rvUnitTupleValues (F i).coefficient *
            integerMonomialMap (G := Values.Gamma (M := M)) (F i).matrix γ.val := by
  let C := Set.range (fun F : OriginalGroundAffineRVFormula hc B n =>
    (gammaGroundAffineAgreement G J h F).carrier)
  have hC : ∀ U ∈ C, GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin n)) U := by
    rintro U ⟨F,rfl⟩
    exact (gammaGroundAffineAgreement G J h F).definable
  have hcover : ∀ γ ∈ G.carrier, ∃ U ∈ C, γ ∈ U := by
    intro γ hγ
    obtain ⟨F,hF⟩ := hpoint ⟨γ,hγ⟩
    exact ⟨_,⟨F,rfl⟩,(gammaGroundAffineAgreement_mem G J h F ⟨γ,hγ⟩).mpr hF⟩
  obtain ⟨D,hD,hDC,hcoverD⟩ := gammaGround_definable_finite_subcover hκ hs hsmall hγsmall G C hC hcover
  letI : Fintype D := hD.fintype
  let N := Fintype.card D
  let e : Fin N ≃ D := (Fintype.equivFin D).symm
  choose g hg using fun d : D => hDC d.property
  let F := fun i : Fin N => g (e i)
  let E := fun i => gammaGroundAffineAgreement G J h (F i)
  have hEc : ∀ γ : G, ∃ i, γ.val ∈ (E i).carrier := by
    intro γ
    obtain ⟨U,hU,hγU⟩ := hcoverD γ.val γ.property
    obtain ⟨i,hi⟩ := e.surjective ⟨U,hU⟩
    refine ⟨i,?_⟩
    change γ.val ∈ (gammaGroundAffineAgreement G J h (g (e i))).carrier
    have he : (gammaGroundAffineAgreement G J h (g (e i))).carrier = U :=
      (hg (e i)).trans (congrArg Subtype.val hi)
    exact he.symm ▸ hγU
  obtain ⟨P,hP,hpart⟩ := gammaGround_ordered_cover_partition G E hEc
  refine ⟨N,F,P,fun i => (hP i).1,hpart,?_⟩
  intro i γ hγ
  exact (gammaGroundAffineAgreement_mem G J h (F i) γ).mp ((hP i).2 hγ)

end DiamondIntegral.Section3
