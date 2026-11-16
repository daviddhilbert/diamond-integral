import «section 6».VFReindexedSynchronizedChains
import «section 6».CoveredJointPreparation

/-! Preparation in permuted VF coordinates yields a literal permitted
chain in the original coordinates. No permutation is inserted into the
special chain, and all protected images are the actual full images. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem reindexedVFSet_inverse (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Fin n ≃ Fin n) : reindexedVFSet (reindexedVFSet A e) e.symm=A := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [mem_reindexedVFSet,mem_reindexedVFSet]
  simp only [Equiv.symm_symm,reindexVFPoint_inverse]

def VFReindexRefinementFrame.conjugation
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) :
    VFReindexRefinementFrame (reindexedVFSet A e) e.symm := by
  refine ⟨⟨r,A,id,hA,hD,fun u => Or.inr ?_⟩⟩
  rw [reindexedVFSet_inverse]
  rfl

theorem VFReindexRefinementFrame.conjugation_piece
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier) :
    (conjugation A e hA hD).selectedPiece (reindexedVFSet P e)=P := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [mem_selectedPiece,mem_reindexedVFSet]
  change (p ∈ A.carrier ∧ reindexVFPoint e.symm (reindexVFPoint e p) ∈ P.carrier) ↔ p ∈ P.carrier
  rw [reindexVFPoint_inverse]
  exact ⟨And.right,fun hp => ⟨hPA hp,hp⟩⟩

theorem PreparedSynchronizedFamily.conjugate_vf_coordinates
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (e : Fin n ≃ Fin n) (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (F : PreparedSynchronizedFamily (G := G) (reindexedVFSet A e)
      (fun i => reindexedVFSet (P i) e) (fun i q hq =>
        (mem_reindexedVFSet A e q).mpr (hPA i ((mem_reindexedVFSet (P i) e q).mp hq)))) :
    Nonempty (PreparedSynchronizedFamily (G := G) A P hPA) := by
  obtain ⟨K⟩ := F.refine_vf_coordinates h00 hc hκ hs hv
    (VFReindexRefinementFrame.conjugation A e hA hD)
  exact ⟨K.changePieces (fun i =>
    VFReindexRefinementFrame.conjugation_piece A e hA hD (P i) (hPA i))⟩

end DiamondIntegral.Section6
