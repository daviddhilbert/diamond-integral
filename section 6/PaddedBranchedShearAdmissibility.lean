import «section 6».PaddedBranchedShearTemplates

/-! Padding preserves every branch-data admissibility condition on the
actual prescribed source, with one common retained-label selector and
one common leading coordinate for the entire finite family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k : ℕ}
variable {arity : Fin k → ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem paddedShearTemplate_good
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : (i : Fin k) → BranchedShearChartTemplate (M := M) S p n r (arity i)) (i : Fin k)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) (a : Fin p → M) (ha : a ∈ (T i).good A) :
    a ∈ (paddedShearTemplate T i).good A := by
  let P := paddedShearTemplate T i
  let D := (T i).toData hv A a ha
  have hF : a ∈ P.goodFunctions := paddedShearTemplate_goodFunctions hv T i a ha.1
  have hPos (u : Fin r → RVInfinity M) (v : Fin (packedBranchArity r arity) → RVInfinity M)
      (x : Fin (n+1) → VF M) :
      P.indicator.value a hF.1 (Fin.append u v) x 0=1 ↔
        v=packedBranchEncode arity (fun j => (T j).leading) i u (packedBranchDecode arity i v) ∧
          D.indicator (Fin.append u (packedBranchDecode arity i v)) x 0=1 :=
    paddedShearTemplate_indicator_one_iff hv T i a ha.1 hF u v x
  have hOff (u : Fin r → RVInfinity M) (v : Fin (packedBranchArity r arity) → RVInfinity M) (x : Fin n → VF M) :
      P.offset.value a hF.2 (Fin.append u v) x 0=D.offset (Fin.append u (packedBranchDecode arity i v)) x 0 := by
    rw [paddedShearTemplate_offset_value T i a ha.1 hF,packedBranchLocalIndex_append]
    rfl
  apply (P.good_iff_semantics hv A a hF).mpr
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w x
    rw [paddedShearTemplate_indicator_value hv T i a ha.1 hF]
    by_cases h : rvValues w ∈ packedBranchValidCode r arity (fun j => (T j).leading) i
    · rw [if_pos h]
      exact D.binary _ x
    · exact Or.inl (by rw [if_neg h])
  · intro x u
    rw [D.source x u]
    constructor
    · rintro ⟨v,hv⟩
      refine ⟨packedBranchEncode arity (fun j => (T j).leading) i u v,(hPos u _ x).mpr ?_⟩
      rw [packedBranchDecode_encode]
      exact ⟨rfl,hv⟩
    · rintro ⟨v,hv⟩
      exact ⟨packedBranchDecode arity i v,((hPos u v x).mp hv).2⟩
  · intro x u v w hv hw
    obtain ⟨hvCode,hvLocal⟩ := (hPos u v x).mp hv
    obtain ⟨hwCode,hwLocal⟩ := (hPos u w x).mp hw
    have hEq := D.unique x u _ _ hvLocal hwLocal
    exact hvCode.trans ((congrArg (packedBranchEncode arity (fun j => (T j).leading) i u) hEq).trans hwCode.symm)
  · intro x u v hv
    have hCode := ((hPos u v x).mp hv).1
    funext j
    have h := congrFun hCode (packedBranchOld r arity j)
    simpa only [P,paddedShearTemplate,Function.comp_apply,packedBranchEncode_old] using h
  · intro x u v hv
    obtain ⟨hCode,hLocal⟩ := (hPos u v x).mp hv
    have hRetain := D.retained x u _ hLocal
    have hNZ := D.nonzero x u _ hLocal
    have hu : ∀ j,(u j).val ≠ iRVZero := by
      intro j hj
      exact hNZ (D.labels j) ((congrArg Subtype.val (congrFun hRetain j)).trans hj)
    intro j
    rw [hCode]
    exact packedBranchEncode_nonzero arity (fun j => (T j).leading) i u _ hu hNZ j
  · intro x u v hv
    obtain ⟨hCode,hLocal⟩ := (hPos u v x).mp hv
    have hLead := congrFun hCode (packedBranchLeading r arity)
    rw [packedBranchEncode_leading] at hLead
    change rv M (x (Fin.last n)+P.offset.value a hF.2 (Fin.append u v) (Fin.init x) 0)=v (packedBranchLeading r arity)
    rw [hOff,hLead]
    exact D.leading_value x u _ hLocal
  · intro x u v hv d hd
    obtain ⟨hCode,hLocal⟩ := (hPos u v x).mp hv
    have hLead := congrFun hCode (packedBranchLeading r arity)
    rw [packedBranchEncode_leading] at hLead
    apply (hPos u v _).mpr
    refine ⟨hCode,?_⟩
    rw [hOff]
    exact D.full_disc x u _ hLocal d (hd.trans hLead)

end DiamondIntegral.Section6
