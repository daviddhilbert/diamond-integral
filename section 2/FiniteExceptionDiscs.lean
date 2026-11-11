import «section 2».AffineApproach
import «section 2».LimitGerms

/-!
# A same-base clopen neighbourhood avoiding finite nonzero exceptions

Intersect the origin discs whose radius representatives are the exceptional
points themselves. The family is finite and its universal membership
formula is definable over the given exceptional set. No scalar section of
the value group, and no choice of one exceptional point, is used.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def avoidFiniteVF (E : Set (Fin 1 → VF M)) : Set (Fin 1 → VF M) :=
  {c | ∀ e ∈ E, vfValues c ∈ uniformBall (vfValues (0 : Fin 1 → VF M)) (e 0).val}

theorem avoidFiniteVF_definable {S : Set M} (E : Set (Fin 1 → VF M))
    (hE : S.Definable LRV (vfValues '' E)) :
    S.Definable LRV (vfValues '' avoidFiniteVF E) := by
  let box (z : Fin 1 ⊕ Fin 1 → M) : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → M :=
    Sum.elim (Sum.elim (vfValues (0 : Fin 1 → VF M)) (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hzero : S.DefinableFun LRV (fun _ : Fin 1 ⊕ Fin 1 → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hbox : S.DefinableMap LRV box := by
    intro i
    cases i with
    | inl i =>
      cases i with
      | inl j => exact hzero
      | inr j => exact Set.DefinableFun.proj LRV
    | inr j => exact Set.DefinableFun.proj LRV
  have hB : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M |
      z ∘ Sum.inl ∈ uniformBall (vfValues (0 : Fin 1 → VF M)) (z (.inr 0))} :=
    (uniformBallRelation_definable S 1).preimage_map hbox
  have hBad := ((hE.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)).inter hB.compl).exists_of_finite
  convert (vfRawUniverse_definable S 1).inter hBad.compl using 1
  ext z
  change (∃ c ∈ avoidFiniteVF E, vfValues c = z) ↔
    (∀ i, iVF (z i)) ∧ ¬ ∃ e : Fin 1 → M, e ∈ vfValues '' E ∧
      z ∉ uniformBall (vfValues (0 : Fin 1 → VF M)) (e 0)
  constructor
  · rintro ⟨c,hc,rfl⟩
    refine ⟨fun i => (c i).property,?_⟩
    rintro ⟨e,⟨a,ha,rfl⟩,hno⟩
    exact hno (hc a ha)
  · rintro ⟨hs,hno⟩
    let c : Fin 1 → VF M := fun i => ⟨z i,hs i⟩
    refine ⟨c,?_,rfl⟩
    intro e he
    by_contra hbad
    exact hno ⟨vfValues e,⟨e,he,rfl⟩,hbad⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem origin_representative_ball_isClopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (r : VF M) (hr : r ≠ 0) :
    IsClopen {c : Fin 1 → VF M |
      vfValues c ∈ uniformBall (vfValues (0 : Fin 1 → VF M)) r.val} := by
  have he : {c : Fin 1 → VF M |
      vfValues c ∈ uniformBall (vfValues (0 : Fin 1 → VF M)) r.val} =
      (fun c : Fin 1 → VF M => c 0) ⁻¹'
        {x : VF M | Valued.v.restrict x < Valued.v.restrict r} := by
    ext c
    change (∀ i : Fin 1, (c i).val ∈ rawOpenBall (0 : VF M).val r.val) ↔ _
    rw [Fin.forall_fin_one, mem_rawOpenBall_iff Valued.v hv (0 : VF M) r (c 0) hr]
    simp only [sub_zero, Set.mem_preimage, Set.mem_ofPred_eq, Valuation.restrict_lt_iff]
  rw [he]
  exact (Valued.isClopen_ball (VF M) (Valued.v.restrict r)).preimage (continuous_apply 0)

theorem avoidFiniteVF_isClopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : Set (Fin 1 → VF M)) (hEf : E.Finite) (hE0 : ∀ e ∈ E, e 0 ≠ 0) :
    IsClopen (avoidFiniteVF E) := by
  haveI : Finite E := hEf.to_subtype
  have he : avoidFiniteVF E = ⋂ e : E,
      {c : Fin 1 → VF M | vfValues c ∈
        uniformBall (vfValues (0 : Fin 1 → VF M)) (e.val 0).val} := by
    ext c
    simp only [avoidFiniteVF, Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
  rw [he]
  exact isClopen_iInter_of_finite (fun e =>
    origin_representative_ball_isClopen hv (e.val 0) (hE0 e.val e.property))

theorem zero_mem_avoidFiniteVF
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : Set (Fin 1 → VF M)) (hE0 : ∀ e ∈ E, e 0 ≠ 0) :
    (0 : Fin 1 → VF M) ∈ avoidFiniteVF E := by
  intro e he i
  apply (mem_rawOpenBall_iff Valued.v hv (0 : VF M) (e 0) (0 : VF M) (hE0 e he)).mpr
  have hval : (Valued.v : Valuation (VF M) G) (e 0) ≠ 0 :=
    (map_ne_zero (Valued.v : Valuation (VF M) G)).mpr (hE0 e he)
  simpa only [sub_self, map_zero] using
    (pos_iff_ne_zero.mpr hval)

theorem avoidFiniteVF_disjoint
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : Set (Fin 1 → VF M)) (hE0 : ∀ e ∈ E, e 0 ≠ 0) :
    Disjoint (avoidFiniteVF E) E := by
  apply Set.disjoint_left.mpr
  intro c hc he
  have h := (mem_rawOpenBall_iff Valued.v hv (0 : VF M) (c 0) (c 0) (hE0 c he)).mp (hc c he 0)
  simpa only [sub_zero, lt_self_iff_false] using h

theorem avoidFiniteVF_mem_nhds_zero
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : Set (Fin 1 → VF M)) (hEf : E.Finite) (hE0 : ∀ e ∈ E, e 0 ≠ 0) :
    avoidFiniteVF E ∈ 𝓝 (0 : Fin 1 → VF M) :=
  (avoidFiniteVF_isClopen hv E hEf hE0).isOpen.mem_nhds (zero_mem_avoidFiniteVF hv E hE0)

end DiamondIntegral.Section2
