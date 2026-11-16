import «section 6».BranchedShearGraphGeometry

/-! Continuous branched shear data construct a full actual standard
contraction stage. The full active RV disc, proper covariance, all
target bounds and the approved derivative exception are constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.BranchedShearData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem target_coordinate_replacement (T : BranchedShearData (G := G) A) (p : A) (d : VF M)
    (hRV : rv M d=rv M ((T.map p).val.1 (Fin.last n))) :
    (Function.update (T.map p).val.1 (Fin.last n) d,(T.map p).val.2) ∈ T.target.carrier := by
  let v := T.outputLabels p
  let δ := T.offset (Fin.append p.val.2 v) (Fin.init p.val.1) 0
  let x := Function.update p.val.1 (Fin.last n) (d-δ)
  have hLeading : rv M d=v T.leading := by
    have h := hRV.trans (T.map_leading p)
    rw [T.map_labels] at h
    exact h
  have hχ : T.indicator (Fin.append p.val.2 v) x 0=1 :=
    T.full_disc p.val.1 p.val.2 v (T.selected_indicator p) d hLeading
  have hx : (x,p.val.2) ∈ A.carrier := (T.source x p.val.2).mpr ⟨v,hχ⟩
  let q : A := ⟨(x,p.val.2),hx⟩
  have hLabels : T.outputLabels q=v := T.unique x p.val.2 _ v (T.selected_indicator q) hχ
  have hInit : Fin.init x=Fin.init p.val.1 := init_update_last _ _
  have hBase : Fin.init (T.map q).val.1=Fin.init (T.map p).val.1 := by
    rw [T.map_base,T.map_base]
    exact hInit
  have hActive : (T.map q).val.1 (Fin.last n)=d := by
    rw [T.map_last,hLabels]
    change x (Fin.last n)+T.offset (Fin.append p.val.2 v) (Fin.init x) 0=d
    rw [hInit]
    dsimp only [x]
    rw [Function.update_self]
    change (d-δ)+δ=d
    exact sub_add_cancel _ _
  have hFields : (T.map q).val.1=Function.update (T.map p).val.1 (Fin.last n) d := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Function.update_self] using hActive
    · simpa only [Function.update_of_ne (Fin.castSucc_ne_last j),Fin.init] using congrFun hBase j
  have hTags : (T.map q).val.2=(T.map p).val.2 := by
    rw [T.map_labels,T.map_labels,hLabels]
  have hPoint : (T.map q).val=(Function.update (T.map p).val.1 (Fin.last n) d,(T.map p).val.2) :=
    Prod.ext hFields hTags
  exact ⟨q,hPoint⟩

theorem target_bundle (T : BranchedShearData (G := G) A) :
    T.target.carrier=(rvCoordinateBundle (vfDropLast T.target).image T.leading).carrier := by
  apply coordinate_bundle_of_replacement T.target T.leading
  · intro q hq
    obtain ⟨p,hp⟩ := T.map_bijective.surjective ⟨q,hq⟩
    have hPoint : (T.map p).val=q := congrArg Subtype.val hp
    have h := T.map_leading p
    rw [hPoint] at h
    exact h
  · intro q hq d hRV
    obtain ⟨p,hp⟩ := T.map_bijective.surjective ⟨q,hq⟩
    have hPoint : (T.map p).val=q := congrArg Subtype.val hp
    have hRp : rv M d=rv M ((T.map p).val.1 (Fin.last n)) := by rw [hPoint]; exact hRV
    have h := T.target_coordinate_replacement p d hRp
    rwa [hPoint] at h

def toStage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : BranchedShearData (G := G) A) (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) :
    ShearContractionStage (G := G) A :=
  shear_contraction_stage_of_open_labels h00 hc linear hκ hs hv hsmall hΓ T.map T.map_bijective hA hAD
    T.map_relative T.map_shear_displacement T.labels T.labels_injective T.map_retained T.leading
    T.map_leading T.map_nonzero T.target_bundle T.map_continuous
    (fun u v => (T.graph_source_clopen u v).isOpen) T.graph_range_clopen

end DiamondIntegral.Section6.BranchedShearData
