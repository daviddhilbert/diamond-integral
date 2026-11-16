import «section 6».OrderedStandardContractionLifts

/-! Full actual ordered lifts recover their exact contracted target,
retain all original labels and have the approved total Jacobian outside
a same-base lower-dimensional set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {T : OrderedStandardContractionProgram (G := G) S A U}
namespace OrderedStandardContractionLift

theorem retained (V : OrderedStandardContractionLift T) (p : A) (i : Fin r) :
    (V.map p).val.2 (T.oldLabels i)=p.val.2 i :=
  (congrFun (V.labels p) (T.oldLabels i)).trans (T.retained p i)

theorem target_tagged (V : OrderedStandardContractionLift T) :
    ∀ p ∈ V.target.carrier,∀ z ∈ V.target.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
  intro p hp z hz hTags
  have hpLeading := ((V.recover p).mp hp).2
  have hzLeading := ((V.recover z).mp hz).2
  funext i
  exact (hpLeading i).trans ((congrFun hTags (T.volumeIndex i)).trans (hzLeading i).symm)

theorem projection_image_eq (V : OrderedStandardContractionLift T) : (rvProjection V.map).image=U := by
  apply defSet_eq_of_carrier_eq
  ext u
  constructor
  · rintro ⟨p,hp⟩
    have h := ((V.recover (V.map p).val).mp (V.map p).property).1
    exact hp ▸ h
  · intro hu
    obtain ⟨p,hp⟩ := T.surjective ⟨u,hu⟩
    refine ⟨p,?_⟩
    change (rvProjection V.map p).val = u
    rw [rvProjection_apply]
    exact Prod.ext (Subsingleton.elim _ _) ((V.labels p).trans (congrArg (fun z : U => z.val.2) hp))

theorem inverse_rv_contractible (V : OrderedStandardContractionLift T)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (p z : V.target) (hTags : p.val.2=z.val.2) :
    rvCoordinates M (V.map.inverse V.home.bijective p).val=
      rvCoordinates M (V.map.inverse V.home.bijective z).val := by
  let x := V.map.inverse V.home.bijective p
  let y := V.map.inverse V.home.bijective z
  have hOld : x.val.2=y.val.2 := by
    funext i
    rw [← V.retained x i,← V.retained y i,Map.apply_inverse,Map.apply_inverse]
    exact congrFun hTags (T.oldLabels i)
  exact Prod.ext (hTag x.val x.property y.val y.property hOld) hOld

theorem unit_derivative_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hn : 0 < n) (V : OrderedStandardContractionLift T) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt V.map p :=
  exists_mixed_unit_derivative_exception hc hs hsmall hn V.map V.genericUnit

end OrderedStandardContractionLift

theorem ordered_standard_lift_of_doublyBounded_pullback
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S A U,Nonempty (OrderedStandardContractionLift T) := by
  obtain ⟨q,U,⟨T⟩⟩ := ordered_standard_program_of_doublyBounded_pullback h00 hc linear hκ hs hv S hsmall hΓ n r A hA hD hRP
  exact ⟨q,U,T,exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ T hA⟩

end DiamondIntegral.Section6
