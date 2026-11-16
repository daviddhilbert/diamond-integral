import «section 6».StageShearChartFamilies

/-! The extracted source indicator has the exact active full-disc
closure required by the branch constructor. Surjectivity and retention
recover the original source tuple of every replacement target point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.ShearContractionStage
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem indicatorFamily_full_disc
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (x : Fin (n+1) → VF M) (u : Fin r → RVInfinity M) (v : Fin T.stage.arity → RVInfinity M)
    (hv : T.indicatorFamily hc (Fin.append u v) x 0=1) (d : VF M) (hd : rv M d=v T.stage.leading) :
    T.indicatorFamily hc (Fin.append u v)
      (Function.update x (Fin.last n) (d-T.offsetFamily hc (Fin.append u v) (Fin.init x) 0)) 0=1 := by
  obtain ⟨y,p,hp,hfp⟩ := (T.indicatorFamily_eq_one_iff hc u v x).mp hv
  have hTarget : (y,v) ∈ T.stage.target.carrier := hfp ▸ (T.stage.lift p).property
  let y' := Function.update y (Fin.last n) d
  have hNew : (y',v) ∈ T.stage.target.carrier := by
    apply (T.stage.recover_target (y',v)).mpr
    constructor
    · change (Fin.init y',v) ∈ T.stage.contracted.carrier
      rw [show Fin.init y'=Fin.init y from init_update_last _ _]
      exact ((T.stage.recover_target (y,v)).mp hTarget).1
    · change rv M (y' (Fin.last n))=v T.stage.leading
      simpa only [y',Function.update_self] using hd
  obtain ⟨z,hfz⟩ := T.stage.home.bijective.surjective ⟨(y',v),hNew⟩
  have hZOut : (T.stage.lift z).val.2=v := congrArg (fun q : T.stage.target => q.val.2) hfz
  have hZVF : (T.stage.lift z).val.1=y' := congrArg (fun q : T.stage.target => q.val.1) hfz
  have hZValue : (T.stage.lift z).val=(y',v) := congrArg Subtype.val hfz
  have hOld : v ∘ T.stage.oldLabels=u := T.indicatorFamily_retained hc x u v hv
  have hZInput : z.val.2=u := by
    funext i
    have h := T.stage.retained z i
    rw [hZOut] at h
    exact h.symm.trans (congrFun hOld i)
  have hInit (a : A) : Fin.init (T.stage.lift a).val.1=Fin.init a.val.1 := funext (T.stage.relative a)
  have hPVF := congrArg Prod.fst hp
  have hFVF := congrArg Prod.fst hfp
  have hBase : Fin.init z.val.1=Fin.init x := by
    calc
      _=Fin.init (T.stage.lift z).val.1 := (hInit z).symm
      _=Fin.init y' := congrArg Fin.init hZVF
      _=Fin.init y := init_update_last _ _
      _=Fin.init (T.stage.lift p).val.1 := (congrArg Fin.init hFVF).symm
      _=Fin.init p.val.1 := hInit p
      _=Fin.init x := congrArg Fin.init hPVF
  have hGraphZ : graphFibre T.stage.lift u v z.val.1 y' := ⟨z,Prod.ext rfl hZInput,hZValue⟩
  have hOffset := T.offsetFamily_at_graph hc u v z.val.1 y' hGraphZ
  have hYLast : y' (Fin.last n)=d := by simp only [y',Function.update_self]
  rw [hBase,hYLast] at hOffset
  have hLast : z.val.1 (Fin.last n)=d-T.offsetFamily hc (Fin.append u v) (Fin.init x) 0 := by
    rw [hOffset]
    abel
  have hFields : z.val.1=Function.update x (Fin.last n)
      (d-T.offsetFamily hc (Fin.append u v) (Fin.init x) 0) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Function.update_self] using hLast
    · simpa only [Function.update_of_ne (Fin.castSucc_ne_last j),Fin.init] using congrFun hBase j
  apply (T.indicatorFamily_eq_one_iff hc u v _).mpr
  exact ⟨y',z,Prod.ext hFields hZInput,hZValue⟩

def toBranchedData
    (T : ShearContractionStage (G := G) A) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) : BranchedShearData (G := G) A where
  arity := T.stage.arity
  indicator := T.indicatorFamily hc
  offset := T.offsetFamily hc
  indicator_definable := graphChartSourceIndicator_family_definable hc T.stage.lift
  offset_definable := graphShearBaseDisplacement_family_definable hc T.stage.lift T.displacement
  indicator_continuous := graphChartSourceIndicator_continuous hc hv T.stage.lift T.stage.home
  offset_continuous := graphShearBaseDisplacement_continuous hc hv T.stage.lift T.stage.home T.displacement
  labels := T.stage.oldLabels
  labels_injective := T.stage.oldLabels_injective
  leading := T.stage.leading
  binary w x := by
    change totalFocusFibre (graphChartSourceIndicator hc T.stage.lift) w x 0=0 ∨
      totalFocusFibre (graphChartSourceIndicator hc T.stage.lift) w x 0=1
    rw [graphChartSourceIndicator_value]
    split_ifs <;> simp
  source := T.indicatorFamily_source hc
  unique := T.indicatorFamily_unique hc
  retained := T.indicatorFamily_retained hc
  nonzero := T.indicatorFamily_nonzero hc
  leading_value := T.indicatorFamily_leading hc
  full_disc := T.indicatorFamily_full_disc hc

end DiamondIntegral.Section6.ShearContractionStage
