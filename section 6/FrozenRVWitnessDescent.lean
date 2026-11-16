import «section 6».MeasuredFrozenUnaryRVTemplatePreparation
import «section 6».FrozenParameterPrograms
import «section 6».UnaryRVRowDefinability
import «section 6».DefinableRVRowDescent
import «section 6».UnaryParameterFreezing
import «section 6».GammaFormFreezing

/-! Complete frozen RV witness graphs descend over the unchanged base.
No bound on the witness row is required. Actual protected-domain and
Gamma-level identities justify replacement of the whole witness at a
freezing centre. Instantiation by finite blowup words is separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r q m k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {j : Fin m} {X : UnaryPreparationContext A j}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S}
variable {V : RVSetParameterTemplate (M := M) S 1 q}
variable {θ : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S)}
namespace MeasuredUnaryRVTemplateFreezeCertificate
variable (F : MeasuredUnaryRVTemplateFreezeCertificate (G := G) A C hCA X P V θ)

def witnessSubstitution : DefinableParameterSubstitution (M := M) S 1 1 :=
  FMT.freezingParameterSubstitution F.freezing.balls F.freezing.centers F.freezing.separated
    F.freezing.balls_definable F.freezing.centers_definable

def witnessQuotient : Map A (pureRVTagDomain F.target) :=
  (pureRVTagQuotient F.target).comp F.map

def frozenWitnessRow (p : Mixed M 1 r) (u : Fin q → RVInfinity M) : Prop :=
  unaryRVRowRelation (r := r) (V.substitute F.witnessSubstitution) p u

def descendedWitnessRelation := descendedRVRowRelation F.witnessQuotient F.frozenWitnessRow

theorem witnessQuotient_surjective (h00 : M ⊨ Axioms.ACVF00) :
    Function.Surjective F.witnessQuotient :=
  (pureRVTagQuotient_surjective F.target).comp (F.chain.toChain.toSpecial.bijective h00).surjective

theorem frozenWitnessRow_definable :
    (rawMixedSpace 1 r).RelationDefinable (rawRVSpace q) S F.frozenWitnessRow :=
  unaryRVRowRelation_definable (r := r) (V.substitute F.witnessSubstitution)

theorem descendedWitnessRelation_definable :
    (rawRVSpace F.arity).RelationDefinable (rawRVSpace q) S F.descendedWitnessRelation :=
  descendedRVRowRelation_definable F.witnessQuotient F.frozenWitnessRow F.frozenWitnessRow_definable

theorem frozenWitnessRow_constant (p z : A)
    (he : (F.witnessQuotient p).val=(F.witnessQuotient z).val) :
    ∀ u,F.frozenWitnessRow p.val u ↔ F.frozenWitnessRow z.val u := by
  intro u
  exact Set.ext_iff.mp (F.data p z he) u

theorem descendedWitnessRelation_at (p : A) :
    {u | F.descendedWitnessRelation (F.witnessQuotient p).val u}=
      (V.fibre (F.witnessSubstitution.value (fun _ => (p.val.1 0).val))).carrier := by
  exact descendedRVRowRelation_at F.witnessQuotient F.frozenWitnessRow F.frozenWitnessRow_constant p

theorem protected_membership_freeze (i : Fin l) (p : Mixed M m X.arity) :
    FMT.mixedFamilyFreeze F.freezing.balls F.freezing.centers j p ∈ (P i).carrier ↔ p ∈ (P i).carrier :=
  FMT.mixedFamilyFreeze_mem_iff F.freezing.balls F.freezing.centers j F.freezing.separated
    (P i).carrier (F.protectedProducts i) p

theorem form_value_freeze (p : X.source) :
    gammaFormExtension θ (FMT.mixedFamilyFreeze F.freezing.balls F.freezing.centers j p.val)=(θ p).val :=
  FMT.gammaFormExtension_freeze F.freezing.balls F.freezing.centers j F.freezing.separated θ F.formProducts p

theorem complete_witness_validity {T : Type*}
    (problem : A → T) (valid : T → Set (Fin q → RVInfinity M) → Prop)
    (hOriginal : ∀ p : A,valid (problem p) (V.fibre (fun _ => (p.val.1 0).val)).carrier)
    (hPreserved : ∀ p : A,
      problem (F.freezing.unaryBaseFreeze F.freezing.product_domain p)=problem p)
    (p : A) : valid (problem p)
      {u | F.descendedWitnessRelation (F.witnessQuotient p).val u} := by
  rw [F.descendedWitnessRelation_at]
  have h := hOriginal (F.freezing.unaryBaseFreeze F.freezing.product_domain p)
  rw [hPreserved p] at h
  exact h

end MeasuredUnaryRVTemplateFreezeCertificate
end DiamondIntegral.Section6
