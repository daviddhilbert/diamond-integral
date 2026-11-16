import «section 6».RVIndexedEventualRadii
import Section9.AffineMixedDerivative

/-! Actual affine charts from centered open polydiscs to the unit open
polydisc. Scales and shifts are explicitly named in the working base;
the volume adapter will adjoin only these finitely many real parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n r : ℕ} {S : Set M}

theorem centered_polydisc_chart_projection
    (v : Valuation (VF M) G) (a d : Fin n → VF M) (hd : ∀ i, d i ≠ 0)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ∀ x : Fin n → VF M, (∃ p : A, p.val.1 = x) ↔ ∀ i, v (x i-a i) < v (d i))
    (hscale : ∀ i, ((d i)⁻¹).val ∈ S)
    (hshift : ∀ i, (-(d i)⁻¹*a i).val ∈ S) (x : Fin n → VF M) :
    (∃ p : (affineMixedMap A (fun i => (d i)⁻¹) (fun i => -(d i)⁻¹*a i) hscale hshift).image,
      p.val.1 = x) ↔ ∀ i, v (x i) < 1 := by
  let F := affineMixedMap A (fun i => (d i)⁻¹) (fun i => -(d i)⁻¹*a i) hscale hshift
  have hformula (p : A) (i : Fin n) :
      (F p).val.1 i = (d i)⁻¹*(p.val.1 i-a i) := by
    rw [affineMixedMap_apply]
    ring
  have hvalue (y : VF M) (i : Fin n) :
      v ((d i)⁻¹*(y-a i)) < 1 ↔ v (y-a i) < v (d i) := by
    rw [map_mul,map_inv₀,mul_comm,← div_eq_mul_inv]
    exact div_lt_one₀ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr (hd i)))
  constructor
  · rintro ⟨⟨_,p,rfl⟩,rfl⟩ i
    rw [hformula]
    exact (hvalue _ i).mpr ((hA p.val.1).mp ⟨p,rfl⟩ i)
  · intro hx
    let y : Fin n → VF M := fun i => d i*x i+a i
    have hy : ∀ i, v (y i-a i) < v (d i) := by
      intro i
      have he : (d i)⁻¹*(y i-a i) = x i := by
        dsimp [y]
        rw [add_sub_cancel_right,← mul_assoc,inv_mul_cancel₀ (hd i),one_mul]
      exact (hvalue (y i) i).mp (he.symm ▸ hx i)
    obtain ⟨p,hp⟩ := (hA y).mpr hy
    refine ⟨⟨(F p).val,Set.mem_range_self p⟩,funext fun i => ?_⟩
    change (F p).val.1 i = x i
    rw [hformula,congrFun hp i]
    dsimp [y]
    rw [add_sub_cancel_right,← mul_assoc,inv_mul_cancel₀ (hd i),one_mul]

theorem centered_polydisc_chart_inverse
    (A : DefSet (rawMixedSpace (M := M) n r) S) (a d : Fin n → VF M)
    (hscale : ∀ i, ((d i)⁻¹).val ∈ S) (hshift : ∀ i, (-(d i)⁻¹*a i).val ∈ S)
    (hd : ∀ i, d i ≠ 0)
    (p : (affineMixedMap A (fun i => (d i)⁻¹) (fun i => -(d i)⁻¹*a i) hscale hshift).image) :
    ((affineMixedImage A (fun i => (d i)⁻¹) (fun i => -(d i)⁻¹*a i) hscale hshift).inverse
      (affineMixedImage_bijective A _ _ hscale hshift (fun i => inv_ne_zero (hd i))) p).val =
      (fun i => d i*p.val.1 i+a i,p.val.2) := by
  rw [affineMixedImage_inverse_apply A _ _ hscale hshift (fun i => inv_ne_zero (hd i))]
  apply Prod.ext
  · funext i
    simp only [inv_inv,mul_neg,neg_mul,neg_neg]
    rw [← mul_assoc,mul_inv_cancel₀ (hd i),one_mul]
  · rfl

end DiamondIntegral.Section6
