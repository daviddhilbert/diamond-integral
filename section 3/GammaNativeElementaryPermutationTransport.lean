import «section 3».GammaNativeMeasuredVolumePermutations
import «section 3».GammaNativeElementaryLocalComparison
import «section 3».GammaGroundBijectionProducts

/-! Coordinate reindexing keeps original-base admissibility. The checked
product charts transport an elementary step along a measured RV map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaCoordinateBase_reindex (S : Set M) (t : Fin (n+1) → RV (M := M))
    (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    coordinateBase S i (t ∘ σ) = coordinateBase S (σ i) t := by
  ext x
  constructor
  · rintro (hx | ⟨j,hj,hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨σ j,fun he => hj (σ.injective he),hx⟩
  · rintro (hx | ⟨j,hj,hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨σ.symm j,fun he => hj ((σ.apply_symm_apply j).symm.trans (congrArg σ he)),
        (congrArg (fun j => (t j).val) (σ.apply_symm_apply j)).trans hx⟩

theorem gammaNativeReindex_admissible (U : GammaObjectAt B Set.univ (n+1))
    (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (σ i)) :
    GammaAdmissible (U.reindexVolume σ).toGamma.toGammaRVObject i := by
  constructor
  · intro u
    exact hAd.nonzero u
  · intro u
    have h := hAd.algebraic u
    change AlgebraicAtBase ⟨coordinateBase B.real i (gammaVolumeValue U.toGamma.toGammaRVObject u ∘ σ),B.gamma⟩
      .rv (gammaVolumeValue U.toGamma.toGammaRVObject u (σ i)).val
    rw [gammaCoordinateBase_reindex]
    exact h

theorem gammaNativeReindex_full (U : GammaObjectAt B Set.univ (n+1))
    (hU : GammaFullWeightAt U) (σ : Equiv.Perm (Fin (n+1))) : GammaFullWeightAt (U.reindexVolume σ) := by
  apply (gammaFullWeightAt_iff_nonzero _).mpr
  intro u j
  exact (gammaFullWeightAt_iff_nonzero U).mp hU u (σ j)

theorem gammaNativeElementary_transport_measured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U V : GammaObjectAt B Set.univ (n+1)) (hU : GammaFullWeightAt U) (hV : GammaFullWeightAt V)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (i j : Fin (n+1)) (hAdU : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hAdV : GammaAdmissible V.toGamma.toGammaRVObject j)
    (e : GammaGroundMeasuredRVHom
      (⟨Section5.nativeRVGroundObject U hU,ω⟩ : GammaGroundMeasuredRVObject hc B (n+1))
      (⟨Section5.nativeRVGroundObject V hV,π⟩ : GammaGroundMeasuredRVObject hc B (n+1))) :
    Nonempty (GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U i hAdU)
        (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAdU)))
      (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr V j hAdV)
        (π.comp (gammaNativeElementaryOldLabel hκ hs h00 hr V j hAdV)))) := by
  let CU := gammaNativeElementaryChart (hc := hc) hκ hs h00 hr U hU i hAdU
  let CV := gammaNativeElementaryChart (hc := hc) hκ hs h00 hr V hV j hAdV
  let EP := e.bijection.prodMap (GammaGroundBijection.id (gammaGroundMeasuredRVPositive hc B).underlying.domain)
  let F := CV.symm.comp (EP.comp CU)
  refine ⟨⟨F,fun w => ?_⟩⟩
  have hSquare : CV.map (F.map w) = EP.map (CU.map w) := CV.map.apply_inverse CV.bijective _
  have hSource := gammaNativeElementary_weight hκ hs h00 hr U hU ω i hAdU w
  have hTarget := gammaNativeElementary_weight hκ hs h00 hr V hV π j hAdV (F.map w)
  change _ = (⟨Section5.nativeRVGroundObject V hV,π⟩ : GammaGroundMeasuredRVObject hc B (n+1)).combinedWeight
      ⟨(CV.map (F.map w)).val.1,(CV.map (F.map w)).property.1⟩ *
    (gammaGroundMeasuredRVPositive hc B).combinedWeight
      ⟨(CV.map (F.map w)).val.2,(CV.map (F.map w)).property.2⟩ at hTarget
  rw [hSquare] at hTarget
  exact hSource.trans ((congrArg (fun z => z * (gammaGroundMeasuredRVPositive hc B).combinedWeight
    ⟨(CU.map w).val.2,(CU.map w).property.2⟩)
      (e.preserves ⟨(CU.map w).val.1,(CU.map w).property.1⟩)).trans hTarget.symm)

end DiamondIntegral.Section3
