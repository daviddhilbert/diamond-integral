import «section 6».ExtendedMeasuredLiftMaps

/-! The extended actual VF map is a bijection. Full local-fibre
surjectivity and the exact prescribed label equation suffice even
when the injection of old labels is not onto the local label set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem extendedMeasuredLiftMap_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) :
    Function.Bijective (extendedMeasuredLiftMap hc U F D hD χ hχ) := by
  let W := measuredRVVolumeExtension hc U A D χ hχ
  let χ' := e.iso.hom.map.comp χ
  let hχ' : Function.Injective χ' := (rvIso_map_bijective e.iso).1.comp hχ
  let Z := measuredRVVolumeExtension hc U B D χ' hχ'
  let φ := extendedLiftPiecePullback hc U A D hD χ hχ
  constructor
  · intro p q hpq
    have hLabels : p.val.2 = q.val.2 :=
      congrArg (fun z : rvLift Z.object => z.val.2) hpq
    have hVF : (extendedLiftVFMap hc U F D hD χ hχ p).val =
        (extendedLiftVFMap hc U F D hD χ hχ q).val :=
      congrArg (fun z : rvLift Z.object => z.val.1) hpq
    by_cases hp : p.val.2 ∈ D.carrier
    · have hq : q.val.2 ∈ D.carrier := hLabels ▸ hp
      let p₀ : rvLift (W.object.restrict D hD) :=
        ⟨p.val,(rvLift_restrict_mem_iff W.object D hD _).mpr ⟨p.property,hp⟩⟩
      let q₀ : rvLift (W.object.restrict D hD) :=
        ⟨q.val,(rvLift_restrict_mem_iff W.object D hD _).mpr ⟨q.property,hq⟩⟩
      rw [extendedLiftVFMap_of_piece hc U F D hD χ hχ p p₀ rfl,
        extendedLiftVFMap_of_piece hc U F D hD χ hχ q q₀ rfl] at hVF
      have hSource : liftLabelMap A.object (φ p₀) = liftLabelMap A.object (φ q₀) := by
        rw [extendedLiftPiecePullback_label,extendedLiftPiecePullback_label]
        exact congrArg χ (Subtype.ext hLabels)
      have hTarget : liftLabelMap B.object (F.map (φ p₀)) = liftLabelMap B.object (F.map (φ q₀)) := by
        rw [liftLabelMap_target_of_graph e.iso.hom.map F.map F.labels,
          liftLabelMap_target_of_graph e.iso.hom.map F.map F.labels,hSource]
      have hF : F.map (φ p₀) = F.map (φ q₀) :=
        Subtype.ext (Prod.ext hVF (congrArg Subtype.val hTarget))
      have hφ := F.bijective.1 hF
      have hPQ := extendedLiftPiecePullback_injective hc U A D hD χ hχ hφ
      exact Subtype.ext (congrArg (fun r : rvLift (W.object.restrict D hD) => r.val) hPQ)
    · have hq : q.val.2 ∉ D.carrier := hLabels ▸ hp
      rw [extendedLiftVFMap_of_not_mem hc U F D hD χ hχ p hp,
        extendedLiftVFMap_of_not_mem hc U F D hD χ hχ q hq] at hVF
      exact Subtype.ext (Prod.ext hVF hLabels)
  · intro q
    let u := liftLabelMap Z.object q
    by_cases hu : u.val ∈ D.carrier
    · let uD : D := ⟨u.val,hu⟩
      have hBq : B.object.value (e.iso.hom.map (χ uD)) = tupleRV q.val.1 := by
        have hVol := liftLabelMap_volume Z.object q
        rw [measuredRVVolumeExtension_of_mem hc U B D χ' hχ' u hu] at hVol
        exact hVol
      let qB : rvLift B.object := ⟨(q.val.1,(e.iso.hom.map (χ uD)).val),e.iso.hom.map (χ uD),rfl,hBq⟩
      obtain ⟨a,ha⟩ := F.bijective.2 qB
      have hATag : liftLabelMap A.object a = χ uD := by
        apply (rvIso_map_bijective e.iso).1
        have h := liftLabelMap_target_of_graph e.iso.hom.map F.map F.labels a
        rw [ha] at h
        exact h.symm
      have hAp : W.object.value u = tupleRV a.val.1 := by
        rw [measuredRVVolumeExtension_of_mem hc U A D χ hχ u hu,← hATag]
        exact liftLabelMap_volume A.object a
      let p : rvLift W.object := ⟨(a.val.1,u.val),u,rfl,hAp⟩
      let p₀ : rvLift (W.object.restrict D hD) :=
        ⟨p.val,(rvLift_restrict_mem_iff W.object D hD _).mpr ⟨p.property,hu⟩⟩
      have hφ : φ p₀ = a := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (congrArg Subtype.val hATag).symm
      refine ⟨p,Subtype.ext ?_⟩
      rw [extendedMeasuredLiftMap_value,extendedLiftVFMap_of_piece hc U F D hD χ hχ p p₀ rfl]
      change ((F.map (φ p₀)).val.1,u.val) = q.val
      rw [hφ,ha]
      rfl
    · have hWq : W.object.value u = tupleRV q.val.1 := by
        rw [measuredRVVolumeExtension_of_not_mem hc U A D χ hχ u hu]
        have hVol := liftLabelMap_volume Z.object q
        rw [measuredRVVolumeExtension_of_not_mem hc U B D χ' hχ' u hu] at hVol
        exact hVol
      let p : rvLift W.object := ⟨q.val,u,rfl,hWq⟩
      refine ⟨p,Subtype.ext ?_⟩
      rw [extendedMeasuredLiftMap_value,extendedLiftVFMap_of_not_mem hc U F D hD χ hχ p hu]
      rfl

end DiamondIntegral.Section6
