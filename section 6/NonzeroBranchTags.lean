import «section 6».ScalarCodeExtension
import Section3.MeanInBalls

/-! Finite disjoint-union tags away from RV zero. Residue characteristic
zero separates the two constant unit tags, both definable over the empty
base. Thus tagging introduces neither unbounded values nor new names. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def branchTag (b : Bool) : RVInfinity M := if b then rv M (-1) else rv M 1

theorem branchTag_value (b : Bool) : Values.vrv (branchTag (M := M) b) = 1 := by
  cases b
  · exact Values.vf_value_one
  · change vfValue (- (1 : VF M)) = 1
    change Values.vfValueHom (- (1 : VF M)) = 1
    rw [vfValue_neg]
    exact Values.vf_value_one

theorem branchTag_nonzero (b : Bool) : branchTag (M := M) b ≠ rvZero M := by
  cases b
  · exact fun h => one_ne_zero ((rv_eq_zero_iff (1 : VF M)).mp h)
  · exact fun h => (neg_ne_zero.mpr one_ne_zero) ((rv_eq_zero_iff (- (1 : VF M))).mp h)

theorem branchTag_injective (h00 : M ⊨ Axioms.ACVF00) :
    Function.Injective (branchTag (M := M)) := by
  have hne : rv M (1 : VF M) ≠ rv M (-1) := by
    intro he
    have hneg : (- (1 : VF M)).val ≠ iVFZero := by
      intro hz
      exact (neg_ne_zero.mpr one_ne_zero) (show (- (1 : VF M)) = 0 from Subtype.ext hz)
    have hclose := (CanonicalRV.encoded_eq_iff_close (1 : VF M).property (- (1 : VF M)).property hneg).mp
      (congrArg Subtype.val he)
    change ¬ VFValued.predV (- (1 : VF M)) (1 - (-1)) at hclose
    apply hclose
    apply (Values.presentation_compatible _ _).mpr
    have htwo := Barycentre.natCast_value_one (Values.presentationValuation (M := M))
      Values.presentation_compatible h00 2 (by decide)
    have htwo' : Values.presentationValuation (2 : VF M) = 1 := by simpa using htwo
    rw [show (1 : VF M) - (-1) = 2 by ring,htwo']
    simp
  intro a b he
  cases a <;> cases b
  · rfl
  · exact False.elim (hne he)
  · exact False.elim (hne he.symm)
  · rfl

theorem rv_scalarCode_definable {I : Type} {S : Set M} {F : (I → M) → M}
    (hF : S.DefinableFun LRV F) : S.DefinableFun LRV (fun z => iRv (F z)) := by
  have harg : S.DefinableMap LRV (fun z : I → M =>
      (Sum.elim (fun _ : Fin 1 => F z) Fin.elim0 : Fin 1 ⊕ Fin 0 → M)) := by
    rintro (i | i)
    · exact hF
    · exact i.elim0
  have hr : S.DefinableFun LRV (fun z : Fin 1 ⊕ Fin 0 → M => iRv (z (.inl 0))) :=
    hullRVCode_definable (M := M) (n := 1) (m := 0) S (.inl 0)
  have hcomp := hr.comp harg
  exact hcomp

theorem branchTag_definable {I : Type} (S : Set M) (b : Bool) :
    S.DefinableFun LRV (fun _ : I → M => (branchTag (M := M) b).val) := by
  have hone : S.DefinableFun LRV (fun _ : I → M => iVFOne) :=
    (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfOne)).comp
      (show S.DefinableMap LRV (fun _ : I → M => Fin.elim0) from fun j => j.elim0)
  cases b
  · exact rv_scalarCode_definable hone
  · have hneg : S.DefinableFun LRV (fun _ : I → M => iVFNeg iVFOne) :=
      (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
        (show S.DefinableMap LRV (fun _ : I → M => ![iVFOne]) from by
          intro j
          fin_cases j
          exact hone)
    exact rv_scalarCode_definable hneg

end DiamondIntegral.Section6
