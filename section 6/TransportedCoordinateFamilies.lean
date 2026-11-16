import «section 6».FrozenProgramChoiceBranches
import «section 6».TaggedPullbackRefinements
import «section 6».UnaryContextInverseCoordinates

/-! Exact identification of transported ambient points with the joint
families at their old frozen parameters. This keeps every old RV label
and the full current unary labels, even when some are duplicates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
namespace FrozenCoordinateProgramData

def transportedLabels (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) :
    Fin (F.unary.arity+X.arity) → Fin U.target.arity :=
  Fin.addCases U.target.labels U.retainedLabels

def transportedJointPoint (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (q : Mixed M (n+1) U.target.arity) :
    Mixed M (n+1) (F.unary.arity+X.arity) := (q.1,q.2 ∘ F.transportedLabels U)

theorem transportedBase_at (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (q : U.target.source) :
    unaryFamilyBasePoint (F.transportedJointPoint U q.val)=(U.target.projection q).val := by
  rw [U.target.projection_value]
  apply Prod.ext
  · rfl
  · funext i
    simp only [unaryFamilyBasePoint,transportedJointPoint,transportedLabels,Function.comp_apply,Fin.addCases_left]

theorem transportedParameter_at_inverse (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (q : U.target.source) :
    unaryFamilyParameter (F.oldParameterMap h00) (U.target.projection q)=
      F.substitution.value (fun _ =>
        ((U.map.inverse (U.chain.toChain.toSpecial.bijective h00) q).val.1 0).val) := by
  have hHead := congrArg (fun a : A => a.val.1 0)
    (U.inverse_projection h00 (F.unary.chain.toChain.toSpecial.bijective h00) q)
  rw [X.projection_value] at hHead
  exact (F.oldParameterMap_value h00 (U.target.projection q)).trans
    (congrArg F.substitution.value (funext (fun _ => (congrArg Subtype.val hHead).symm)))

theorem transportedTail_at_inverse (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (q : U.target.source) :
    (Fin.tail (F.transportedJointPoint U q.val).1,
      (F.transportedJointPoint U q.val).2 ∘ Fin.natAdd F.unary.arity)=
      (Fin.tail (U.map.inverse (U.chain.toChain.toSpecial.bijective h00) q).val.1,
        (U.map.inverse (U.chain.toChain.toSpecial.bijective h00) q).val.2) := by
  apply Prod.ext
  · funext i
    exact (U.inverse_inactive h00 q i.succ (Fin.succ_ne_zero i)).symm
  · funext i
    simp only [transportedJointPoint,transportedLabels,Function.comp_apply,Fin.addCases_right]
    exact (U.inverse_retained h00 q i).symm

theorem transportedJoint_mem_iff (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P)
    (Q : DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (hPreserved : ((headFibreTemplate Q).substitute F.substitution).uncurry=Q)
    (q : U.target.source) :
    F.transportedJointPoint U q.val ∈
        (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate Q)).carrier ↔
      (U.map.inverse (U.chain.toChain.toSpecial.bijective h00) q).val ∈ Q.carrier := by
  have hLeft : F.transportedJointPoint U q.val ∈
      (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate Q)).carrier ↔
      (Fin.tail (F.transportedJointPoint U q.val).1,
        (F.transportedJointPoint U q.val).2 ∘ Fin.natAdd F.unary.arity) ∈
        ((headFibreTemplate Q).fibre
          (unaryFamilyParameter (F.oldParameterMap h00) (U.target.projection q))).carrier := by
    rw [mem_unaryIndexedMixedFamily]
    constructor
    · rintro ⟨b,hb,hT⟩
      have he : b=U.target.projection q := Subtype.ext (hb.symm.trans (F.transportedBase_at U q))
      exact he ▸ hT
    · intro hT
      exact ⟨U.target.projection q,F.transportedBase_at U q,hT⟩
  have hAt := ((headFibreTemplate Q).substitute F.substitution).mem_uncurry_iff
    (U.map.inverse (U.chain.toChain.toSpecial.bijective h00) q).val
  rw [hPreserved,MixedSetParameterTemplate.substitute_carrier] at hAt
  apply hLeft.trans
  rw [F.transportedTail_at_inverse h00 U q,F.transportedParameter_at_inverse h00 U q]
  exact hAt.symm

def ambientRefinementFrame (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P)
    (hTag : ∀ p ∈ (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate X.source)).carrier,
      ∀ q ∈ (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate X.source)).carrier,
        p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    RVRefinementFrame (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate X.source)) :=
  RVRefinementFrame.of_tagged_pullback _ U.target.source (F.transportedLabels U)
    U.target.proper U.target.doublyBounded U.target.pullback hTag
    (fun p hp => (F.transportedJoint_mem_iff h00 U X.source F.sources_preserved.1 ⟨p,hp⟩).mpr
      (U.map.inverse (U.chain.toChain.toSpecial.bijective h00) ⟨p,hp⟩).property)

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
