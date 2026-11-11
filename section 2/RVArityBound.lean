import «section 2».RVMapGraphs

/-! RV-infinity coordinates have a finite-to-one map to the same number
of nonzero RV coordinates: send zero to one and keep every other value.
Each fibre is determined by its finite zero pattern. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def rvCollapseZero (t : RVInfinity M) : RV M :=
  ⟨⟨nonzeroRVCode t.val 0,(nonzeroRVCode_proper _ t.property 0).1⟩,
    fun h => (nonzeroRVCode_proper _ t.property 0).2 (congrArg Subtype.val h)⟩

noncomputable def rvCollapseTuple {m : ℕ} (u : Fin m → RVInfinity M) : Fin m → RV M :=
  fun i => rvCollapseZero (u i)

theorem rvCollapseTuple_finite_fibres {m : ℕ} (t : Fin m → RV M) :
    {u : Fin m → RVInfinity M | rvCollapseTuple u = t}.Finite := by
  classical
  let pattern (u : {u : Fin m → RVInfinity M | rvCollapseTuple u = t}) : Fin m → Bool :=
    fun i => decide ((u.val i).val = iRVZero)
  have hinj : Function.Injective pattern := by
    intro u v he
    apply Subtype.ext
    funext i
    apply Subtype.ext
    have hp := congrFun he i
    change decide ((u.val i).val = iRVZero) = decide ((v.val i).val = iRVZero) at hp
    have hg : nonzeroRVCode (u.val i).val 0 = nonzeroRVCode (v.val i).val 0 := by
      have h := congrFun (u.property.trans v.property.symm) i
      exact congrArg (fun z : RV M => z.val.val) h
    by_cases hu : (u.val i).val = iRVZero
    · have hv : (v.val i).val = iRVZero := of_decide_eq_true (hp.symm.trans (by simp [hu]))
      exact hu.trans hv.symm
    · have hv : (v.val i).val ≠ iRVZero := by
        intro h
        simp only [hu,h,decide_false,decide_true] at hp
        cases hp
      simpa only [nonzeroRVCode,ite_true,ite_eq_right hu,ite_eq_right hv] using hg
  exact Set.finite_coe_iff.mp (Finite.of_injective pattern hinj)

theorem rv_finite_map_to_arity (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {m : ℕ} (U : Set (Fin m → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) : RVHasFiniteMap S U m := by
  classical
  let g (u : U) := rvCollapseTuple u.val
  refine ⟨g,?_,?_⟩
  · intro t
    exact (rvCollapseTuple_finite_fibres t).preimage Subtype.val_injective.injOn
  · let F (z : Fin m → M) (i : Fin m) := nonzeroRVCode (z i) 0
    have hF : S.DefinableMap LRV F := fun i => nonzeroRVCode_definable S i 0
    exact rvMapGraph_definable_of_raw_map hc S U hU g F hF (fun _ => rfl)

theorem rvDimension_le_arity (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {m : ℕ} (U : Set (Fin m → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    rvDimension S U ≤ (m : WithBot ℕ) := by
  classical
  by_cases hne : U.Nonempty
  · simp only [rvDimension,ite_eq_left hne]
    exact_mod_cast Nat.sInf_le (rv_finite_map_to_arity hc S U hU)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,rvDimension_empty]
    exact bot_le

end DiamondIntegral.Section2
