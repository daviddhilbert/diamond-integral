import «section 6».ProtectedUnaryValuePreparation

/-! Finite freezing of complete unary data. The exceptional balls
meet the actual obstacle set. Their row values need no boundedness
assumption, and one radius works for every RV label and output row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FMT
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ} {T : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

private theorem disc_difference_lt (a x y : VF M) (ρ : Balls.OpenRadius G)
    (hx : x ∈ Balls.openDisc Valued.v a ρ) (hy : y ∈ Balls.openDisc Valued.v a ρ) :
    Valued.v (x-y) < (OrderDual.ofDual ρ : Gˣ).val := by
  calc
    _ = Valued.v ((x-a)-(y-a)) := congrArg Valued.v (by abel)
    _ ≤ max (Valued.v (x-a)) (Valued.v (y-a)) := Valued.v.map_sub _ _
    _ < _ := max_lt hx hy

def frozenUnaryValue (balls : Set (OpenBallCodes.OpenBall M)) (c : balls → VF M)
    (ω : Mixed M 1 r → T) (p : Mixed M 1 r) : T :=
  ω ((fun _ : Fin 1 => vfFamilyFreeze balls c (p.1 0)),p.2)

theorem frozenUnaryValue_uniform_constancy
    (balls : Set (OpenBallCodes.OpenBall M)) (c : balls → VF M)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    (s : VF M) (hs0 : s ≠ 0) (hRadius : SameOpenRadius (G := G) balls s)
    (Q : Finset (VF M)) (hCover : ∀ z ∈ Q,∃ D : balls,z ∈ vfOpenBall D.val)
    (ω : Mixed M 1 r → T)
    (hControl : ∀ a ρ,(∀ z ∈ Q,z ∉ Balls.openDisc Valued.v a ρ) →
      ∀ x ∈ Balls.openDisc Valued.v a ρ,∀ y ∈ Balls.openDisc Valued.v a ρ,
      ∀ u,ω ((fun _ : Fin 1 => x),u)=ω ((fun _ : Fin 1 => y),u))
    (x y : VF M) (hClose : Valued.v (y-x)<Valued.v s) (u : Fin r → RVInfinity M) :
    frozenUnaryValue balls c ω ((fun _ : Fin 1 => x),u)=
      frozenUnaryValue balls c ω ((fun _ : Fin 1 => y),u) := by
  have hSame (D : balls) : x ∈ vfOpenBall D.val ↔ y ∈ vfOpenBall D.val := by
    obtain ⟨a,ha⟩ := hRadius D.val D.property
    rw [ha]
    constructor
    · intro hx
      exact (Balls.strictDisc_recenter_iff Valued.v a x y s hx).mp hClose
    · intro hy
      have hrev : Valued.v (x-y)<Valued.v s := (Valued.v.map_sub_swap x y).trans_lt hClose
      exact (Balls.strictDisc_recenter_iff Valued.v a y x s hy).mp hrev
  by_cases hx : ∃ D : balls,x ∈ vfOpenBall D.val
  · obtain ⟨D,hD⟩ := hx
    have hy := (hSame D).mp hD
    have hFx : vfFamilyFreeze balls c x=c D := by
      rw [vfFamilyFreeze_eq balls c hsep]
      exact familyFreeze_inside _ _ (fun D E z hz hE => hsep D E z.val hz hE) D x hD
    have hFy : vfFamilyFreeze balls c y=c D := by
      rw [vfFamilyFreeze_eq balls c hsep]
      exact familyFreeze_inside _ _ (fun D E z hz hE => hsep D E z.val hz hE) D y hy
    change ω ((fun _ : Fin 1 => vfFamilyFreeze balls c x),u)=ω ((fun _ : Fin 1 => vfFamilyFreeze balls c y),u)
    rw [hFx,hFy]
  · have hy : ∀ D : balls,y ∉ vfOpenBall D.val := fun D hD => hx ⟨D,(hSame D).mpr hD⟩
    have hx' := not_exists.mp hx
    let ρ := Balls.openRadius (Valued.v s) ((map_ne_zero (Valued.v : Valuation (VF M) G)).mpr hs0)
    have hAvoid (z : VF M) (hz : z ∈ Q) : z ∉ Balls.openDisc Valued.v x ρ := by
      intro hzx
      obtain ⟨D,hD⟩ := hCover z hz
      obtain ⟨a,ha⟩ := hRadius D.val D.property
      have hza : Valued.v (z-a)<Valued.v s := (Set.ext_iff.mp ha z).mp hD
      have hxz : Valued.v (x-z)<Valued.v s := (Valued.v.map_sub_swap x z).trans_lt hzx
      exact hx' D ((Set.ext_iff.mp ha x).mpr
        ((Balls.strictDisc_recenter_iff Valued.v a z x s hza).mp hxz))
    have h := hControl x ρ hAvoid x (Balls.centre_mem_openDisc Valued.v x ρ) y hClose u
    have hFx : vfFamilyFreeze balls c x=x := by
      rw [vfFamilyFreeze_eq balls c hsep]
      exact familyFreeze_outside _ _ x hx'
    have hFy : vfFamilyFreeze balls c y=y := by
      rw [vfFamilyFreeze_eq balls c hsep]
      exact familyFreeze_outside _ _ y hy
    change ω ((fun _ : Fin 1 => vfFamilyFreeze balls c x),u)=ω ((fun _ : Fin 1 => vfFamilyFreeze balls c y),u)
    rw [hFx,hFy]
    exact h

theorem frozenUnaryValue_obstacle_control
    (balls : Set (OpenBallCodes.OpenBall M)) (c : balls → VF M)
    (hsep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D=E)
    (s : VF M) (hs0 : s ≠ 0) (hRadius : SameOpenRadius (G := G) balls s)
    (Q : Finset (VF M)) (hCover : ∀ z ∈ Q,∃ D : balls,z ∈ vfOpenBall D.val)
    (hHit : ∀ D : balls,∃ z ∈ Q,z ∈ vfOpenBall D.val)
    (ω : Mixed M 1 r → T)
    (hControl : ∀ a ρ,(∀ z ∈ Q,z ∉ Balls.openDisc Valued.v a ρ) →
      ∀ x ∈ Balls.openDisc Valued.v a ρ,∀ y ∈ Balls.openDisc Valued.v a ρ,
      ∀ u,ω ((fun _ : Fin 1 => x),u)=ω ((fun _ : Fin 1 => y),u)) :
    ∀ a ρ,(∀ z ∈ Q,z ∉ Balls.openDisc Valued.v a ρ) →
      ∀ x ∈ Balls.openDisc Valued.v a ρ,∀ y ∈ Balls.openDisc Valued.v a ρ,
      ∀ u,frozenUnaryValue balls c ω ((fun _ : Fin 1 => x),u)=
        frozenUnaryValue balls c ω ((fun _ : Fin 1 => y),u) := by
  intro a ρ hAvoid x hx y hy u
  by_cases hSmall : (OrderDual.ofDual ρ : Gˣ).val ≤ Valued.v s
  · exact frozenUnaryValue_uniform_constancy balls c hsep s hs0 hRadius Q hCover ω hControl x y
      ((disc_difference_lt a y x ρ hy hx).trans_le hSmall) u
  · have hLarge : Valued.v s < (OrderDual.ofDual ρ : Gˣ).val := lt_of_not_ge hSmall
    have hOutside (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) :
        ∀ D : balls,z ∉ vfOpenBall D.val := by
      intro D hD
      obtain ⟨q,hq,hqD⟩ := hHit D
      obtain ⟨b,hb⟩ := hRadius D.val D.property
      have hzB : z ∈ Balls.openDisc Valued.v b
          (Balls.openRadius (Valued.v s) ((map_ne_zero (Valued.v : Valuation (VF M) G)).mpr hs0)) := (Set.ext_iff.mp hb z).mp hD
      have hqB : q ∈ Balls.openDisc Valued.v b
          (Balls.openRadius (Valued.v s) ((map_ne_zero (Valued.v : Valuation (VF M) G)).mpr hs0)) := (Set.ext_iff.mp hb q).mp hqD
      have hqz : Valued.v (q-z)<Valued.v s := disc_difference_lt b q z _ hqB hzB
      apply hAvoid q hq
      change Valued.v (q-a)<(OrderDual.ofDual ρ : Gˣ).val
      calc
        _ = Valued.v ((q-z)+(z-a)) := congrArg Valued.v (by abel)
        _ ≤ max (Valued.v (q-z)) (Valued.v (z-a)) := Valued.v.map_add _ _
        _ < _ := max_lt (hqz.trans hLarge) hz
    have hFx : vfFamilyFreeze balls c x=x := by
      rw [vfFamilyFreeze_eq balls c hsep]
      exact familyFreeze_outside _ _ x (hOutside x hx)
    have hFy : vfFamilyFreeze balls c y=y := by
      rw [vfFamilyFreeze_eq balls c hsep]
      exact familyFreeze_outside _ _ y (hOutside y hy)
    change ω ((fun _ : Fin 1 => vfFamilyFreeze balls c x),u)=ω ((fun _ : Fin 1 => vfFamilyFreeze balls c y),u)
    rw [hFx,hFy]
    exact hControl a ρ hAvoid x hx y hy u

end DiamondIntegral.Section6.FMT
