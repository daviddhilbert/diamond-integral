import IntegrationSection4.BalancedBallClasses

/-! Exact vertical and horizontal translation normal forms for actual 2-cells.
These are geometric images on the unchanged VF and RV carriers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section4.BalancedFibres
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {D E : Set (VF (M := M))} {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

def cellVerticalTranslation (f : VF (M := M) → VF (M := M)) (p : VF (M := M) × VF (M := M)) :=
  (p.1,p.2-f p.1)

def cellHorizontalTranslation (g : VF (M := M) → VF (M := M)) (p : VF (M := M) × VF (M := M)) :=
  (p.1-g p.2,p.2)

theorem cell_vertical_translation_image (h : CellData R f t) :
    cellVerticalTranslation f '' R = first R ×ˢ {x : VF (M := M) | rv x = t} := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    have ha : q.1 ∈ first R := ⟨q,hq,rfl⟩
    exact ⟨ha,(Set.ext_iff.mp (h.fibres q.1 ha) q.2).mp hq⟩
  · rintro ⟨ha,hx⟩
    refine ⟨(p.1,p.2+f p.1),?_,?_⟩
    · change p.2+f p.1 ∈ fibre R p.1
      rw [h.fibres p.1 ha]
      simpa only [translatedRV,Set.mem_setOf_eq,add_sub_cancel_right] using hx
    · exact Prod.ext rfl (add_sub_cancel_right _ _)

def balancedPositionInverse (h : HasBalancedFibres D E R f r t) (b : VF (M := M)) : VF (M := M) :=
  if hb : b ∈ E then Classical.choose (h.bijective.surjOn hb) else 0

theorem balancedPositionInverse_mem (h : HasBalancedFibres D E R f r t) (b : VF (M := M)) (hb : b ∈ E) :
    balancedPositionInverse h b ∈ D := by
  rw [balancedPositionInverse,dif_pos hb]
  exact (Classical.choose_spec (h.bijective.surjOn hb)).1

theorem balancedPositionInverse_right (h : HasBalancedFibres D E R f r t) (b : VF (M := M)) (hb : b ∈ E) :
    f (balancedPositionInverse h b) = b := by
  rw [balancedPositionInverse,dif_pos hb]
  exact (Classical.choose_spec (h.bijective.surjOn hb)).2

theorem balancedPositionInverse_left (h : HasBalancedFibres D E R f r t) (a : VF (M := M)) (ha : a ∈ D) :
    balancedPositionInverse h (f a) = a :=
  h.bijective.injOn (balancedPositionInverse_mem h (f a) (h.bijective.mapsTo ha)) ha
    (balancedPositionInverse_right h (f a) (h.bijective.mapsTo ha))

theorem balanced_horizontal_fibre (h : HasBalancedFibres D E R f r t)
    (hD : IntegrationInACVF.Section3ACVF.PaperBalls.IsOpenBall (rawSet D))
    (b : VF (M := M)) (hb : b ∈ E) :
    {a : VF (M := M) | (a,b) ∈ R} = translatedRV r (balancedPositionInverse h b) := by
  let c := balancedPositionInverse h b
  have hc : c ∈ D := balancedPositionInverse_mem h b hb
  have hfc : f c = b := balancedPositionInverse_right h b hb
  ext a
  constructor
  · intro hab
    have ha := (h.subset hab).1
    have hm : c ∈ D ∩ f ⁻¹' fibre R a := by
      refine ⟨hc,?_⟩
      change (a,f c) ∈ R
      rw [hfc]
      exact hab
    exact (Set.ext_iff.mp (h.horizontal a ha) c).mp hm
  · intro har
    have ha : a ∈ D := BalancedBallClasses.positive_class_subset h hD c hc har
    have hm := (Set.ext_iff.mp (h.horizontal a ha) c).mpr har
    have hm' : (a,f c) ∈ R := hm.2
    rwa [hfc] at hm' 

theorem balanced_horizontal_translation_image (h : HasBalancedFibres D E R f r t)
    (hD : IntegrationInACVF.Section3ACVF.PaperBalls.IsOpenBall (rawSet D)) :
    cellHorizontalTranslation (balancedPositionInverse h) '' R =
      {x : VF (M := M) | rv x = r} ×ˢ E := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    have hb := (h.subset hq).2
    have hc := (Set.ext_iff.mp (balanced_horizontal_fibre h hD q.2 hb) q.1).mp hq
    exact ⟨hc,hb⟩
  · rintro ⟨hx,hb⟩
    refine ⟨(p.1+balancedPositionInverse h p.2,p.2),?_,?_⟩
    · apply (Set.ext_iff.mp (balanced_horizontal_fibre h hD p.2 hb) _).mpr
      simpa only [translatedRV,Set.mem_setOf_eq,add_sub_cancel_right] using hx
    · exact Prod.ext (add_sub_cancel_right _ _) rfl

theorem cell_position_constant_or_injective (h : CellData R f t) :
    (∀ a ∈ first R, ∀ b ∈ first R, f a = f b) ∨ Set.InjOn f (first R) := by
  rcases h.positioning with hc | ⟨hi,_⟩ | ⟨r,_,_,hBal,_⟩
  · exact Or.inl hc
  · exact Or.inr hi
  · exact Or.inr hBal.bijective.injOn

end IntegrationInACVF.Section5
