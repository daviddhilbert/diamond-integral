import «section 6».UnaryStandardContractionStages
import «section 6».ContractionMapTransports
import «section 6».CarriedExceptionalSets
import «section 6».ZeroArityPreparation
import «section 6».OrderedProgramLiftRelation

/-! Every actual ordered contraction program has its full definable
lift. Later stages carry the earlier contracted coordinate as its full
retained-label RV disc. The whole lift is a proper homeomorphism with
generic total determinant one and exact recovery from its final labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure OrderedStandardContractionLift
    {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (T : OrderedStandardContractionProgram (G := G) S A U) where
  target : DefSet (rawMixedSpace (M := M) n q) S
  map : Map A target
  ordered : IsOrderedProgramLift S T map
  home : ProperCovariantHomeomorphism map
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  pullback : IsRVPullback target.carrier
  recover : ∀ p : Mixed M n q,p ∈ target.carrier ↔
    (Fin.elim0,p.2) ∈ U.carrier ∧ ∀ i,rv M (p.1 i)=p.2 (T.volumeIndex i)
  labels : ∀ p : A,(map p).val.2=(T.toMap p).val.2
  genericUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt map p

namespace OrderedStandardContractionLift

def zero
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) 0 r) S) (hA : ProperInvariant S A.carrier) :
    OrderedStandardContractionLift (G := G) (.zero A) := {
  target := A
  map := Map.id A
  ordered := .zero A
  home := identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ hA
  proper := hA
  doublyBounded := ⟨1,fun _ _ i => i.elim0⟩
  pullback := zero_arity_rvPullback A.carrier
  recover := by
    intro p
    have he : (Fin.elim0,p.2)=p := Prod.ext (Subsingleton.elim _ _) rfl
    rw [he]
    simp only [Fin.forall_fin_zero,and_true]
  labels := fun _ => rfl
  genericUnit := fun p _ => identity_unit_derivative hA p }

def step
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (T : StandardContractionStage (G := G) A)
    (tail : OrderedStandardContractionProgram (G := G) S T.contracted U)
    (V : OrderedStandardContractionLift tail) : OrderedStandardContractionLift (.step T tail) := by
  let l := tail.oldLabels T.leading
  have hLabels (p : T.contracted) : (V.map p).val.2 l=p.val.2 T.leading :=
    (congrFun (V.labels p) l).trans (tail.retained p T.leading)
  have hTarget : T.target=rvCoordinateBundle T.contracted T.leading := defSet_eq_of_carrier_eq T.bundle
  let g := changeMapTarget T.lift hTarget
  let F := carryLastMap V.map T.leading l hLabels
  let W := rvCoordinateBundle V.target l
  have hBase (p : A) : bundleProjection T.contracted T.leading (g p)=T.contraction p := by
    apply Subtype.ext
    rw [bundleProjection_value,changeMapTarget_value]
    rfl
  refine {
    target := W
    map := F.comp g
    ordered := .step T tail V.ordered hLabels hTarget
    home := lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ (T.home.changeMapTarget hTarget)
      (carryLastMap_properHomeomorphism V.map T.leading l hLabels h00 hc linear hκ hs hv hsmall hΓ V.home)
    proper := rvCoordinateBundle_properInvariant h00 hc hκ hs hv V.target l V.proper
    doublyBounded := rvCoordinateBundle_doublyBounded V.target l V.doublyBounded V.proper.rvBounded
    pullback := rvCoordinateBundle_pullback V.target l V.pullback
    recover := ?_
    labels := ?_
    genericUnit := ?_ }
  · intro p
    change ((Fin.init p.1,p.2) ∈ V.target.carrier ∧ rv M (p.1 (Fin.last n))=p.2 l) ↔ _
    rw [V.recover]
    constructor
    · rintro ⟨⟨hp,hVolume⟩,hLast⟩
      refine ⟨hp,?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [OrderedStandardContractionProgram.volumeIndex_step_last] using hLast
      · simpa only [OrderedStandardContractionProgram.volumeIndex_step_castSucc,Fin.init] using hVolume j
    · rintro ⟨hp,hVolume⟩
      refine ⟨⟨hp,fun i => ?_⟩,?_⟩
      · simpa only [OrderedStandardContractionProgram.volumeIndex_step_castSucc,Fin.init] using hVolume i.castSucc
      · simpa only [OrderedStandardContractionProgram.volumeIndex_step_last] using hVolume (Fin.last n)
  · intro p
    change (carryLastMap V.map T.leading l hLabels (g p)).val.2=(tail.toMap (T.contraction p)).val.2
    rw [carryLastMap_value,hBase]
    exact V.labels (T.contraction p)
  · intro p hp
    have hHead : AlgebraicIndependent (vfParameterField S) (T.contraction p).val.1 := by
      rw [T.contraction_fixes_complement]
      exact hp.comp Fin.castSucc (Fin.castSucc_injective n)
    have hVUnit := V.genericUnit (T.contraction p) hHead
    have hCarry : HasMixedUnitDerivativeAt F (g p) :=
      carryLastMap_unit_derivative h00 hc hκ hs hv V.map T.contracted_proper T.leading l hLabels (g p)
        (hBase p ▸ hVUnit)
    have hTUnit := T.unitDerivative p
      (not_mem_small_set_of_independent hc T.exceptional T.exceptional_dim p.val hp)
    exact hCarry.comp (hTUnit.changeMapTarget hTarget)

end OrderedStandardContractionLift

theorem exists_ordered_standard_contraction_lift
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (T : OrderedStandardContractionProgram (G := G) S A U) :
    ProperInvariant S A.carrier → Nonempty (OrderedStandardContractionLift T) := by
  induction T with
  | zero A =>
    intro hA
    exact ⟨OrderedStandardContractionLift.zero h00 hc linear hκ hs hv hsmall hΓ A hA⟩
  | step T tail ih =>
    intro hA
    obtain ⟨V⟩ := ih T.contracted_proper
    exact ⟨OrderedStandardContractionLift.step h00 hc linear hκ hs hv hsmall hΓ T tail V⟩

end DiamondIntegral.Section6
