import «section 6».CoordinateObstacles
import «section 6».GammaCodeLocus

/-! A single bounded original-base coordinate-root family controls every
Gamma level. The checked obstacle theorem permits independent RV arities
for its ambient and predicate: the extra Gamma code is never a parameter
of the root family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_coordinate_gamma_controlling_roots
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (ω : Mixed M (n+1) r → Gamma M)
    (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω)) :
    ∃ R : CoordinateRootFamily A, ∃ N : ℕ, R.Bound N ∧
      ∀ γ : Gamma M, CoordinateRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ} := by
  let e := lastHeadIndices n
  let A' := toOrdinarySet hc (reindexedVFSet A e)
  let P := gammaCodeLocus A ω hGraph
  let P' := toOrdinarySet hc (reindexedVFSet P e)
  have hA' : SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier A') :=
    (ordinary_pullback_iff _).mpr (reindexedVFSet_rvPullback A e hARV)
  obtain ⟨R,N,hN,hControl⟩ := SpecialTransformations.Section5.uniformVerticalObstacles hs hsmall Valued.v hv n P' A' hA'
  refine ⟨CoordinateRootFamily.fromHead hc R,N+1,CoordinateRootFamily.fromHead_bound hc R N hN,?_⟩
  intro γ b u a ρ hAmbient hAvoid x hx y hy
  have hAmbient' (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) :
      SpecialTransformations.Section5.insertHead z (b,u) ∈ SpecialTransformations.Section5.carrier A' := by
    apply (mem_reindexedVFSet A e _).mpr
    change reindexVFPoint e.symm (Fin.cons z b,u) ∈ A.carrier
    rw [← reindexVFPoint_lastHead_snoc,reindexVFPoint_inverse]
    exact hAmbient z hz
  have hAvoid' (z : VF M) (hz : z ∈ R.fibre (b,u)) : z ∉ Balls.openDisc Valued.v a ρ :=
    hAvoid z (by rw [CoordinateRootFamily.fromHead_fibre]; exact hz)
  obtain ⟨t,ht,htγ⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
  let τ : RVInfinity M := ⟨t,ht.1⟩
  have hMem (z : VF M) :
      ((SpecialTransformations.Section5.insertHead z (b,u)).1,Fin.cons τ u) ∈ SpecialTransformations.Section5.carrier P' ↔
        (Fin.snoc b z,u) ∈ A.carrier ∧ ω (Fin.snoc b z,u) = γ := by
    change (Fin.cons z b,Fin.cons τ u) ∈ (reindexedVFSet P e).carrier ↔ _
    rw [mem_reindexedVFSet]
    rw [← reindexVFPoint_lastHead_snoc,reindexVFPoint_inverse]
    rw [gammaCodeLocus_at]
    exact ⟨fun h => ⟨h.1,h.2.2.symm.trans htγ⟩,
      fun h => ⟨h.1,ht,htγ.trans h.2.symm⟩⟩
  exact (hMem x).symm.trans ((hControl (b,u) a ρ hAmbient' hAvoid' x hx y hy (Fin.cons τ u)).trans (hMem y))

end DiamondIntegral.Section6
