import «section 6».PromotedCentripetalPrograms

/-! The terminal first-order preparation test is equivalent to
preparation of the literal protected images of a realized program.
Actual prepared chains promote to that test over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramRealization.prepared_iff
    {T : CentripetalProgramTemplate (M := M) S p n r s}
    {A : MixedSetParameterTemplate (M := M) S p n r}
    {P : Fin k → MixedSetParameterTemplate (M := M) S p n r} {a : Fin p → M}
    (F : CentripetalProgramRealization (G := G) T A P a) (ha : a ∈ T.good A P)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier) :
    a ∈ T.preparedGood A P ↔ ∀ i,IsRVPullback (F.map.restrict (hPA i)).image.carrier := by
  change (a ∈ T.good A P ∧ a ∈ ⋂ i,rvPullbackParameterLocus (T.pieceTarget A (P i)).typedGraph) ↔ _
  simp only [Set.mem_iInter]
  constructor
  · intro h i
    have hRV := (mem_rvPullbackParameterLocus_iff (T.pieceTarget A (P i)).typedGraph a
      ((T.pieceTarget A (P i)).fibre a) ((T.pieceTarget A (P i)).fibre_code a).symm).mp (h.2 i)
    rwa [F.pieces i (hPA i)] at hRV
  · intro h
    refine ⟨ha,fun i => ?_⟩
    apply (mem_rvPullbackParameterLocus_iff (T.pieceTarget A (P i)).typedGraph a
      ((T.pieceTarget A (P i)).fibre a) ((T.pieceTarget A (P i)).fibre_code a).symm).mpr
    rw [F.pieces i (hPA i)]
    exact h i

theorem exists_promoted_prepared_centripetal_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (a : Fin p → M) (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} {f : Map (A.fibre a) B}
    (h : SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a))
    (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hPA i)).image.carrier) :
    ∃ T : CentripetalProgramTemplate (M := M) S p n r s,a ∈ T.preparedGood A P ∧
      {z | Sum.elim a z ∈ (T.transition A).graph}=
        (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  obtain ⟨T,ha,hGraph⟩ := exists_promoted_centripetal_program h00 hc linear hκ hs hv a hsmall hΓ h
    A P rfl (fun _ => rfl) hARV
  refine ⟨T,⟨ha,Set.mem_iInter.mpr (fun i => ?_)⟩,hGraph⟩
  apply (mem_rvPullbackParameterLocus_iff (T.pieceTarget A (P i)).typedGraph a
    ((T.pieceTarget A (P i)).fibre a) ((T.pieceTarget A (P i)).fibre_code a).symm).mpr
  have hPiece : (T.pieceTarget A (P i)).fibre a=(f.restrict (hPA i)).image :=
    mixedRelationImageTemplate_at_restriction (P i) (T.transition A).graph (T.transition A).definable
      a f (hPA i) hGraph
  rw [hPiece]
  exact hPrepared i

end DiamondIntegral.Section6
