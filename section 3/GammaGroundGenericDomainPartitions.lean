import «section 3».GammaGroundRVGenericValueImage
import «section 3».RVGenericSupport
import «section 3».GammaGroundRVUnitProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {κ : Cardinal} {hc : CanonicalStructure.IsCanonical (M := M)}
variable (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
variable (hsmall : Cardinal.mk B.real < κ) {n : ℕ}

/-- Taking generic value fibres creates no new Gamma point. -/
theorem gammaGroundRVGenericValueImage_subset_values
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    (gammaGroundRVGenericValueImage hs h00 B hsmall A).carrier ⊆ rvUnitTupleValues '' A.carrier := by
  rintro γ ⟨u,hu⟩
  obtain ⟨v,hv,w,hw,hraw⟩ := rvFullFibreGeneric_support (rvUnitValues '' A.carrier) u.val u.property
  have hwv : w = v := rvUnitValues_injective hraw
  subst w
  exact ⟨v,hw,hv.symm.trans hu⟩

/-- A finite definable RV partition over full Gamma preimages induces a
canonical finite definable partition of the original Gamma domain. -/
theorem gammaGroundRVGenericValueImage_partition (hκ : Cardinal.aleph0 < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n))) {N : ℕ}
    (Q : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hsub : ∀ j, (Q j).carrier ⊆ (gammaGroundRVUnitGammaPreimage G).carrier)
    (hpart : ∀ u : gammaGroundRVUnitGammaPreimage G, ∃! j, u.val ∈ (Q j).carrier) :
    (∀ j, (gammaGroundRVGenericValueImage hs h00 B hsmall (Q j)).carrier ⊆ G.carrier) ∧
      ∀ γ ∈ G.carrier, ∃! j, γ ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall (Q j)).carrier := by
  constructor
  · intro j γ hγ
    obtain ⟨u,hu,hval⟩ := gammaGroundRVGenericValueImage_subset_values hs h00 B hsmall (Q j) hγ
    exact hval ▸ hsub j hu
  · intro γ hγ
    obtain ⟨a,ha⟩ := rvUnitTupleValues_surjective (M := M) n γ
    have hnative (j : Fin N) := (gammaGroundRVUnit_definable_iff (Q j).carrier).mp (Q j).definable
    have hrawpart : ∀ u : Fin n → (CanonicalRV.RVSort M)ˣ,
        rvUnitTupleValues u = rvUnitTupleValues a → ∃! j, rvUnitValues u ∈ rvUnitValues '' (Q j).carrier := by
      intro u hu
      have huG : u ∈ (gammaGroundRVUnitGammaPreimage G).carrier := by
        change rvUnitTupleValues u ∈ G.carrier
        rw [hu,ha]
        exact hγ
      obtain ⟨j,hj,huniq⟩ := hpart ⟨u,huG⟩
      refine ⟨j,⟨u,hj,rfl⟩,?_⟩
      rintro k ⟨v,hv,he⟩
      exact huniq k (rvUnitValues_injective he ▸ hv)
    obtain ⟨j,hj,huniq⟩ := rvFullFibreGeneric_partition hc hκ hs h00 B hsmall
      (fun j => rvUnitValues '' (Q j).carrier) hnative a hrawpart
    refine ⟨j,?_,?_⟩
    · have hj' := (gammaGroundRVGenericValueImage_mem_iff hs h00 B hsmall (Q j) a).mpr (hj a rfl)
      exact ha ▸ hj'
    · intro k hk
      apply huniq k
      intro u hu
      apply (gammaGroundRVGenericValueImage_mem_iff hs h00 B hsmall (Q k) u).mp
      exact (hu.trans ha).symm ▸ hk

end DiamondIntegral.Section3
