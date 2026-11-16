import «section 6».EverywhereMeasuredLiftRestrictions

/-! Restrict an actual relatively unary lift to a whole label domain on
which its full derivative and measured identity hold. The inactive VF
coordinates and the exact values of the chosen lift are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_relative_measured_lift_restrict
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (f : Map (rvLift U.object) (rvLift V.object)) (hf : Function.Bijective f)
    (hlabel : ∀ p,e.iso.hom.map.graph p.val.2 (f p).val.2)
    (active : Fin n) (hUnary : VFUnaryRelativeAt f active)
    (A : DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hA : A.carrier ⊆ U.object.domain.carrier)
    (hGood : ∀ p : rvLift U.object,p.val.2 ∈ A.carrier →
      ∃ L,HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val) :
    ∃ F : EverywhereMeasuredRVLift (e.restrict A hA), VFUnaryRelativeAt F.map active ∧
      ∀ (p : rvLift (U.object.restrict A hA)) (q : rvLift U.object),p.val=q.val →
        (F.map p).val=(f q).val := by
  obtain ⟨g,hg,hagree⟩ := exists_restricted_actual_lift e.iso A hA f hf hlabel
  have hLabels (p : rvLift (U.object.restrict A hA)) :
      (e.restrict A hA).iso.hom.map.graph p.val.2 (g p).val.2 := by
    let q : rvLift U.object :=
      ⟨p.val,((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).1⟩
    obtain ⟨u,hu,hv⟩ := hlabel q
    have huA : u.val ∈ A.carrier := hu.symm ▸
      ((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).2
    exact ⟨⟨u.val,huA⟩,hu,hv.trans (congrArg Prod.snd (hagree p q rfl)).symm⟩
  have hMeasure (p : rvLift (U.object.restrict A hA)) :
      ∃ L,HasMixedVFDerivativeAt g p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue (U.restrict A hA).form (liftLabelMap _ p) /
          gammaMapValue (V.restrict (e.iso.hom.map.restrict hA).image
            (rvLabelImage_subset e.iso A hA)).form (liftLabelMap _ (g p))).val := by
    let q : rvLift U.object :=
      ⟨p.val,((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).1⟩
    obtain ⟨L,hL,hJ⟩ := hGood q
      ((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).2
    refine ⟨L,mixedDerivative_to_label_restriction A hA f g p q rfl hagree hL,?_⟩
    have hVal := congrArg Prod.snd (hagree p q rfl)
    change vfValue (LinearMap.toMatrix' L).det =
      (gammaMapValue U.form (liftLabelMap U.object q) /
        gammaMapValue V.form ⟨(g p).val.2,
          rvLabelImage_subset e.iso A hA (liftLabelMap _ (g p)).property⟩).val
    have he : (⟨(g p).val.2,
        rvLabelImage_subset e.iso A hA (liftLabelMap _ (g p)).property⟩ : V.object.domain) =
        liftLabelMap V.object (f q) := Subtype.ext hVal
    rw [he]
    exact hJ
  refine ⟨⟨g,hg,hLabels,hMeasure⟩,?_,hagree⟩
  intro p j hj
  let q : rvLift U.object :=
    ⟨p.val,((rvLift_restrict_mem_iff U.object A hA p.val).mp p.property).1⟩
  exact (congrArg (fun z : (rawMixedSpace (M := M) n V.object.arity).Carrier => z.1 j)
    (hagree p q rfl)).trans (hUnary q j hj)

end DiamondIntegral.Section6
