import «section 2».FiniteExceptionDiscs

/-! The curve-selection source is the maximal ideal with zero removed.
Its raw graph is parameter-free, it is open, and it accumulates at zero. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def curveSource : Set (Fin 1 → VF M) :=
  {c | vfValues c ∈ uniformBall (vfValues (0 : Fin 1 → VF M)) (1 : VF M).val ∧ c 0 ≠ 0}

theorem curveSource_definable (S : Set M) : S.Definable LRV (vfValues '' (curveSource (M := M))) := by
  have hz : S.DefinableFun LRV (fun _ : Fin 1 → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have ho : S.DefinableFun LRV (fun _ : Fin 1 → M => iVFOne) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  let box (z : Fin 1 → M) : Fin 3 → M := ![iVFZero,iVFOne,z 0]
  have hbox : S.DefinableMap LRV box := by
    intro i
    fin_cases i
    · exact hz
    · exact ho
    · exact Set.DefinableFun.proj LRV
  have hB : S.Definable LRV {z : Fin 1 → M | z 0 ∈ rawOpenBall iVFZero iVFOne} := by
    convert (OpenBallCodes.membership_raw_definable S).preimage_map hbox using 1
    ext z
    have hinit : Fin.init (box z) = ![iVFZero,iVFOne] := by
      funext i
      fin_cases i <;> rfl
    change z 0 ∈ rawOpenBall iVFZero iVFOne ↔
      box z (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init (box z))
    rw [hinit]
    rfl
  have hne := ((Set.DefinableFun.proj LRV (i := (0 : Fin 1))).ofPred_eq hz).compl
  convert hB.inter hne using 1
  ext z
  change (∃ c ∈ curveSource, vfValues c = z) ↔
    z 0 ∈ rawOpenBall iVFZero iVFOne ∧ z 0 ≠ iVFZero
  constructor
  · rintro ⟨c,⟨hc,hc0⟩,rfl⟩
    exact ⟨hc 0,fun he => hc0 (Subtype.ext he)⟩
  · rintro ⟨hzB,hz0⟩
    let c : Fin 1 → VF M := fun _ => ⟨z 0,hzB.2.1⟩
    refine ⟨c,⟨?_,?_⟩,?_⟩
    · intro i
      exact hzB
    · intro he
      exact hz0 (congrArg Subtype.val he)
    · funext i
      fin_cases i
      rfl

theorem curveSource_nonzero (c : Fin 1 → VF M) (hc : c ∈ curveSource) : c 0 ≠ 0 := hc.2

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem curveSource_iff_valuation
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (c : Fin 1 → VF M) : c ∈ curveSource ↔ c 0 ≠ 0 ∧ Valued.v (c 0) < 1 := by
  change ((∀ i : Fin 1, (c i).val ∈ rawOpenBall (0 : VF M).val (1 : VF M).val) ∧ c 0 ≠ 0) ↔ _
  rw [Fin.forall_fin_one, mem_rawOpenBall_iff Valued.v hv (0 : VF M) 1 (c 0) one_ne_zero]
  simp only [sub_zero,map_one,and_comm]

theorem curveSource_isOpen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    IsOpen (curveSource (M := M)) := by
  exact (origin_representative_ball_isClopen hv (1 : VF M) one_ne_zero).isOpen.inter
    (isClosed_singleton.isOpen_compl.preimage (continuous_apply (0 : Fin 1)))

theorem curveSource_accumulates
    (δ : Gamma M) : ∃ c ∈ curveSource \ {(0 : Fin 1 → VF M)}, c ∈ vfBall 0 δ := by
  let ε := finiteValue (1 : VF M) one_ne_zero
  obtain ⟨c,hc,hc0⟩ := exists_ne_mem_vfBall (0 : Fin 1 → VF M) (max δ ε) (by decide)
  have hc00 : c 0 ≠ 0 := by
    intro he
    apply hc0
    funext i
    fin_cases i
    exact he
  have hu := (mem_vfBall_iff_gammaUniformBall (0 : Fin 1 → VF M) c ε).mp
    (vfBall_anti (le_max_right _ _) hc)
  change vfValues c ∈ gammaUniformBall (vfValues (0 : Fin 1 → VF M)) ε at hu
  rw [gammaUniformBall_eq_uniformBall (vfValues (0 : Fin 1 → VF M)) ε
    (1 : VF M) one_ne_zero rfl] at hu
  exact ⟨c,⟨⟨hu,hc00⟩,hc0⟩,vfBall_anti (le_max_left _ _) hc⟩

end DiamondIntegral.Section2
