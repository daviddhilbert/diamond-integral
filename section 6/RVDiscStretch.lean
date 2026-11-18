import «section 6».NamedUnaryOffsets
import «section 6».ApertureCore
import «section 6».NonzeroBranchTags
import «section 6».ScalarCodeAlgebra
import Section4.MapCorestrict

/-! Remark 6.32: if the RV-discs `t^♯`, `s^♯` contain definable points `a`,
`b`, then for every definable `c ∈ VF^×` with `v(c) = vrv(s/t)` the map
`x ↦ b + c(x - a)` is a definable bijection `t^♯ → s^♯` with derivative `c`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

/-- The RV-disc `rv(a)^♯ ⊆ VF`, definable when `a` is. -/
def rvDiscSet (a : VF M) (ha : S.Definable₁ LRV {a.val}) : DefSet (rawVFSpace (M := M) 1) S := by
  refine ⟨{x | rv M (x 0) = rv M a},?_⟩
  let P := rawVFSpace (M := M) 1
  have h₁ : S.DefinableFun LRV (fun z : Fin 1 → M => iRv (z 0)) :=
    rv_scalarCode_definable (Set.DefinableFun.proj LRV)
  have h₂ : S.DefinableFun LRV (fun _ : Fin 1 → M => iRv a.val) :=
    rv_scalarCode_definable (definable_named_constant a.val ha)
  change S.Definable LRV (P.preimage {x | rv M (x 0) = rv M a})
  convert (P.definable_domain S).inter (h₁.ofPred_eq h₂) using 1
  apply Set.ext
  intro (z : Fin 1 → M)
  constructor
  · rintro ⟨hz,hzA⟩
    refine ⟨hz,?_⟩
    have he : iRv ((P.decode ⟨z,hz⟩) 0).val = iRv a.val := congrArg Subtype.val hzA
    have hd : ((P.decode ⟨z,hz⟩) 0).val = z 0 := congrFun (vfValues_decode ⟨z,hz⟩) 0
    change iRv (z 0) = iRv a.val
    rw [← hd]
    exact he
  · rintro ⟨hz,hzA⟩
    refine ⟨hz,?_⟩
    apply Subtype.ext
    have hd : ((P.decode ⟨z,hz⟩) 0).val = z 0 := congrFun (vfValues_decode ⟨z,hz⟩) 0
    change iRv ((P.decode ⟨z,hz⟩) 0).val = iRv a.val
    rw [hd]
    exact hzA

/-- The affine map `x ↦ b + c(x - a)` on `VF`. -/
def namedAffineMap (a b c : VF M) (ha : S.Definable₁ LRV {a.val}) (hb : S.Definable₁ LRV {b.val})
    (hc : S.Definable₁ LRV {c.val}) :
    Map (DefSet.univ (rawVFSpace (M := M) 1) S) (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let P := rawVFSpace (M := M) 1
  let f (x : Fin 1 → VF M) : Fin 1 → VF M := fun i => b + c*(x i - a)
  let F (z : Fin 1 → M) : Fin 1 → M := fun i => iVFAdd b.val (iVFMul c.val (iVFAdd (z i) (iVFNeg a.val)))
  have hF : S.DefinableMap LRV F := fun _ => scalarAddCode_definable (definable_named_constant b.val hb)
    (scalarMulCode_definable (definable_named_constant c.val hc)
      (scalarSubCode_definable (Set.DefinableFun.proj LRV) (definable_named_constant a.val ha)))
  have hCode (z : P.domain) : vfValues (f (P.decode z)) = F z.val := by
    funext i
    have hz : (P.decode z i).val = z.val i := congrFun (vfValues_decode z) i
    change iVFAdd b.val (iVFMul c.val (iVFAdd (P.decode z i).val (iVFNeg a.val))) = F z.val i
    rw [hz]
  exact Map.ofCodes (DefSet.univ P S) f F hF (fun z => ⟨f (P.decode z),hCode z⟩)
    (fun z => vfValues_injective ((vfValues_decode _).trans (hCode z).symm))

theorem namedAffineMap_value (a b c : VF M) (ha : S.Definable₁ LRV {a.val}) (hb : S.Definable₁ LRV {b.val})
    (hc : S.Definable₁ LRV {c.val}) (p : DefSet.univ (rawVFSpace (M := M) 1) S) :
    (namedAffineMap a b c ha hb hc p).val 0 = b + c*(p.val 0 - a) := rfl

/-- Strict monotonicity of multiplication by a finite value. -/
theorem value_mul_lt_mul {c x y : VF M} (hc : c ≠ 0) (hxy : vfValue x < vfValue y) :
    vfValue (c*x) < vfValue (c*y) := by
  change Values.vfValueHom (c*x) < Values.vfValueHom (c*y)
  rw [map_mul,map_mul]
  change vfValue c*vfValue x < vfValue c*vfValue y
  by_contra h
  have h' := mul_le_mul' (le_refl (vfValue c⁻¹)) (le_of_not_gt h)
  rw [← mul_assoc,← mul_assoc] at h'
  have hinv : vfValue c⁻¹*vfValue c = 1 := by
    change Values.vfValueHom c⁻¹*Values.vfValueHom c = 1
    rw [← map_mul,inv_mul_cancel₀ hc,map_one]
  rw [hinv,one_mul,one_mul] at h'
  exact (not_le.mpr hxy) h'

/-- Remark 6.32. -/
theorem remark_6_32 (a b c : VF M) (ha : S.Definable₁ LRV {a.val}) (hb : S.Definable₁ LRV {b.val})
    (hc : S.Definable₁ LRV {c.val}) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hval : vfValue c*vfValue a = vfValue b) :
    ∃ f : Map (rvDiscSet a ha) (rvDiscSet b hb), Function.Bijective f ∧
      (∀ x, (f x).val 0 = b + c*(x.val 0 - a)) ∧
      ∀ x : rvDiscSet a ha, HasVFDerivativeAt (fun y => vfDiagonalLinear (fun _ : Fin 1 => c) y +
        (fun _ => b - c*a)) x.val (vfDiagonalLinear (fun _ : Fin 1 => c)) := by
  have hcb : vfValue (c*a) = vfValue b := by
    change Values.vfValueHom (c*a) = _
    rw [map_mul]
    exact hval
  have hmaps (x : rvDiscSet a ha) : b + c*(x.val 0 - a) ∈ {y : VF M | rv M y = rv M b} := by
    have hx : vfValue a < vfValue (x.val 0 - a) := (rv_eq_iff_value_close ha0).mp x.property
    apply (rv_eq_iff_value_close hb0).mpr
    rw [add_sub_cancel_left,← hcb]
    exact value_mul_lt_mul hc0 hx
  let g := namedAffineMap a b c ha hb hc
  let f : Map (rvDiscSet a ha) (rvDiscSet b hb) :=
    (g.restrict (fun _ _ => Set.mem_univ _)).corestrict (fun x => hmaps x)
  have hf (x : rvDiscSet a ha) : (f x).val 0 = b + c*(x.val 0 - a) := rfl
  refine ⟨f,⟨?_,?_⟩,hf,fun x => ?_⟩
  · intro x y hxy
    have h := congrArg (fun z : rvDiscSet b hb => z.val 0) hxy
    simp only [hf] at h
    have h' : x.val 0 = y.val 0 := by
      have := mul_left_cancel₀ hc0 (add_left_cancel h)
      exact sub_left_injective this
    apply Subtype.ext
    funext i
    fin_cases i
    exact h'
  · intro y
    let x : Fin 1 → VF M := fun _ => a + (y.val 0 - b)/c
    have hy : vfValue b < vfValue (y.val 0 - b) := (rv_eq_iff_value_close hb0).mp y.property
    have hx : x ∈ (rvDiscSet a ha).carrier := by
      apply (rv_eq_iff_value_close ha0).mpr
      change vfValue a < vfValue (a + (y.val 0 - b)/c - a)
      rw [add_sub_cancel_left]
      by_contra hn
      have h2 := mul_le_mul' (le_refl (vfValue c)) (le_of_not_gt hn)
      have hm : vfValue c*vfValue ((y.val 0 - b)/c) = vfValue (y.val 0 - b) := by
        change Values.vfValueHom c*Values.vfValueHom ((y.val 0 - b)/c) = Values.vfValueHom (y.val 0 - b)
        rw [← map_mul,mul_div_cancel₀ _ hc0]
      rw [hm,hval] at h2
      exact (not_le.mpr hy) h2
    refine ⟨⟨x,hx⟩,?_⟩
    apply Subtype.ext
    funext i
    fin_cases i
    change b + c*(a + (y.val 0 - b)/c - a) = y.val 0
    rw [add_sub_cancel_left,mul_div_cancel₀ _ hc0,add_sub_cancel]
  · exact hasVFDerivativeAt_affine (vfDiagonalLinear (fun _ : Fin 1 => c)) (fun _ => b - c*a) x.val

end DiamondIntegral.Section6
