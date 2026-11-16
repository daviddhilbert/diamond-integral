import «section 6».FrozenMeasuredChoiceFamilies

/-! The complete source form after the actual preliminary unary lift
agrees with the head-fibre forms at the frozen parameters. Simultaneous
products for all original Gamma levels discharge the freezing equality. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FrozenMeasuredCoordinateProgramData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S)}

def liftedGammaForm (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) :
    Map F.unary.lift.target.source (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  ω.comp (F.unary.lift.map.inverse (F.unary.lift.chain.toChain.toSpecial.bijective h00))

theorem liftedGammaForm_transport (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) (p : X.source) :
    (F.liftedGammaForm h00 (F.unary.lift.map p)).val=(ω p).val := by
  change (ω (F.unary.lift.map.inverse _ (F.unary.lift.map p))).val=(ω p).val
  rw [Map.inverse_apply]

theorem initial_source_form
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) :
    ∀ q : F.unary.lift.target.source,
      gammaFormExtension (headGammaFormMap ω
        ((((F.forget h00).oldParameterMap h00)
          (((F.forget h00).initialProgramContext h00 hc hκ hs hv F.unary.lift hPX).baseMap q)).val 0))
        (Fin.tail q.val.1,q.val.2 ∘ F.unary.lift.retainedLabels)=(F.liftedGammaForm h00 q).val := by
  intro q
  let E := F.forget h00
  let U := F.unary.lift
  let Y := E.initialProgramContext h00 hc hκ hs hv U hPX
  let p := U.map.inverse (U.chain.toChain.toSpecial.bijective h00) q
  let a := FMT.vfFamilyFreeze F.unary.freezing.balls F.unary.freezing.centers (p.val.1 0)
  have hBase : Y.baseMap q=U.target.projection q := by
    apply Subtype.ext
    rw [Y.baseMap_value,U.target.projection_value]
    rfl
  have hHead : ((E.oldParameterMap h00) (Y.baseMap q)).val 0=a := by
    rw [hBase]
    apply Subtype.ext
    exact congrFun (E.transportedParameter_at_inverse h00 U q) 0
  have hTail : (Fin.tail q.val.1,q.val.2 ∘ U.retainedLabels)=(Fin.tail p.val.1,p.val.2) := by
    have h := E.transportedTail_at_inverse h00 U q
    simpa only [FrozenCoordinateProgramData.transportedJointPoint,FrozenCoordinateProgramData.transportedLabels,
      Function.comp_def,Fin.addCases_right] using h
  have hMem := FMT.mixedFamilyFreeze_mapsTo F.unary.freezing.balls F.unary.freezing.centers (0 : Fin (n+2))
    X.source.carrier F.unary.freezing.separated F.unary.ambientProduct p.property
  have hPoint : (Fin.cons a (Fin.tail p.val.1),p.val.2)=
      FMT.mixedFamilyFreeze F.unary.freezing.balls F.unary.freezing.centers 0 p.val := by
    apply Prod.ext
    · funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · simp only [Fin.cons_succ,FMT.mixedFamilyFreeze,Function.update_of_ne (Fin.succ_ne_zero i)]
        rfl
    · rfl
  let x : (headFibreTemplate X.source).fibre (fun _ => a.val) :=
    ⟨(Fin.tail p.val.1,p.val.2),(mem_headFibreTemplate_iff X.source a _).mpr (hPoint.symm ▸ hMem)⟩
  have hFrozen := FMT.gammaFormExtension_freeze F.unary.freezing.balls F.unary.freezing.centers
    (0 : Fin (n+2)) F.unary.freezing.separated ω F.unary.formProducts p
  rw [hHead,hTail]
  exact (headGammaFormExtension_at ω a x).trans ((congrArg (gammaFormExtension ω) hPoint).trans hFrozen)

theorem choice_source_form
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) (i : Fin F.programs.count) :
    ∀ q : focusActive F.unary.lift.target.source ((F.forget h00).choiceTags h00 F.unary.lift i),
      gammaFormExtension (headGammaFormMap ω
        ((((F.forget h00).choiceParameterMap h00 i)
          (((F.forget h00).choiceProgramContext h00 hc hκ hs hv F.unary.lift hPX i).baseMap q)).val 0))
        (Fin.tail q.val.1,q.val.2 ∘ F.unary.lift.retainedLabels)=
      ((F.liftedGammaForm h00).comp (Map.inclusion (fun p
        (hp : p ∈ (focusActive F.unary.lift.target.source ((F.forget h00).choiceTags h00 F.unary.lift i)).carrier) => hp.1)) q).val := by
  intro q
  let E := F.forget h00
  let Y := E.choiceProgramContext h00 hc hκ hs hv F.unary.lift hPX i
  let Z := E.initialProgramContext h00 hc hκ hs hv F.unary.lift hPX
  let p : F.unary.lift.target.source := ⟨q.val,q.property.1⟩
  have hBase : Map.inclusion (E.choiceDomain_subset h00 i) (Y.baseMap q)=Z.baseMap p := by
    apply Subtype.ext
    exact (Y.baseMap_value q).trans (Z.baseMap_value p).symm
  have hParam : (E.choiceParameterMap h00 i) (Y.baseMap q)=(E.oldParameterMap h00) (Z.baseMap p) :=
    congrArg (E.oldParameterMap h00) hBase
  rw [hParam]
  exact F.initial_source_form h00 hc hκ hs hv hPX p

end DiamondIntegral.Section6.FrozenMeasuredCoordinateProgramData
