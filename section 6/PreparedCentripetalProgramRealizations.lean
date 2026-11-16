import «section 6».FinitePreparedCentripetalPrograms
import «section 6».PreparedSynchronizedFamilies

/-! Admissible prepared programs give complete synchronized preparation
witnesses, with actual maps and original-base geometric certificates. -/

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

theorem CentripetalProgramTemplate.exists_prepared_realization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.preparedGood A P) (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier) (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier) :
    Nonempty (PreparedSynchronizedFamily (G := G) (A.fibre a) (fun i => (P i).fibre a) hPA) := by
  obtain ⟨F⟩ := T.exists_realization h00 hc hκ hs hv A P a ha.1 hA hAD hPA hP
  exact ⟨⟨s,(T.target A).fibre a,F.map,F.chain,
    F.chain.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv,
    F.chain.toChain.toSpecial.target_vfDoublyBounded hAD,
    F.chain.toChain.target_rvPullback h00 hARV,(F.prepared_iff ha.1 hPA).mp ha⟩⟩

end DiamondIntegral.Section6
