import «section 2».FibreProjectiveCharts
import «section 2».FibrewiseOpenness
import «section 2».ProjectiveChartClosedness

/-! A same-base finite exception makes a closed-fibre projective family
relatively closed. Both affine chart families are handled by Lemma 2.54. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem projective_family_closed_off_finite
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (F : (Fin 1 → VF M) → Set ((Fin n → VF M) × (Fin 1 → ProjectiveLine (VF M))))
    (hFclosed : ∀ a ∈ I, IsClosed (F a))
    (hFdef : ∀ b : Bool, S.Definable LRV
      (vfCorrespondenceGraph I (fun a => (projectiveFibreChart b) ⁻¹' F a))) :
    ∃ E ⊆ I, E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      IsClosed {p : ↥(I \ E) × ((Fin n → VF M) × (Fin 1 → ProjectiveLine (VF M))) |
        p.2 ∈ F p.1.val} := by
  classical
  let B (b : Bool) : Set ((Fin 1 → VF M) × (Fin (n+1) → VF M)) :=
    {p | p.1 ∈ I ∧ projectiveFibreChart b p.2 ∈ F p.1}
  have hBI (b : Bool) : B b ⊆ I ×ˢ Set.univ := fun p hp => ⟨hp.1,Set.mem_univ _⟩
  have hBdef (b : Bool) : S.Definable LRV (vfCorrespondenceGraph I (fun a => {z | (a,z) ∈ B b})) := by
    convert hFdef b using 1
    ext z
    constructor
    · rintro ⟨a,ha,x,⟨_,hx⟩,he⟩
      exact ⟨a,ha,x,hx,he⟩
    · rintro ⟨a,ha,x,hx,he⟩
      exact ⟨a,ha,x,⟨ha,hx⟩,he⟩
  have hBclosed (b : Bool) (a : Fin 1 → VF M) (ha : a ∈ I) : IsClosed {z | (a,z) ∈ B b} := by
    have he : {z | (a,z) ∈ B b} = (projectiveFibreChart b) ⁻¹' F a := by
      ext z
      exact and_iff_right ha
    rw [he]
    exact (hFclosed a ha).preimage (projectiveFibreChart_isOpenEmbedding b).continuous
  have hChoices (b : Bool) := lemma_2_54_closed h00 hc hκ hs hv I hI (B b) (hBI b) (hBdef b) (hBclosed b)
  choose E hEI hEf hEdef hEc using hChoices
  let Eall := E false ∪ E true
  have hSub (b : Bool) : E b ⊆ Eall := by
    cases b
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have hEall : S.Definable LRV (vfValues '' Eall) := by
    rw [Set.image_union]
    exact (hEdef false).union (hEdef true)
  refine ⟨Eall,Set.union_subset (hEI false) (hEI true),(hEf false).union (hEf true),hEall,?_⟩
  let X := ↥(I \ Eall) × (Fin n → VF M)
  let C : Set (X × (Fin 1 → ProjectiveLine (VF M))) := {p | (p.1.2,p.2) ∈ F p.1.1.val}
  let chart (b : Bool) (y : Fin 1 → VF M) :=
    if b then projectiveTupleChart (fun _ : Fin 1 => (none : LimitPoint M)) y else finiteProjectiveTuple y
  have hLocal (b : Bool) : IsClosed ((Prod.map id (chart b)) ⁻¹' C) := by
    let ι (a : ↥(I \ Eall)) : ↥(I \ E b) :=
      ⟨a.val,a.property.1,fun h => a.property.2 (hSub b h)⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    let ψ (p : X × (Fin 1 → VF M)) : ↥(I \ E b) × (Fin (n+1) → VF M) :=
      (ι p.1.1,vfPairHomeomorph n (p.2,p.1.2))
    have hψ : Continuous ψ :=
      (hι.comp (continuous_fst.comp continuous_fst)).prodMk
        ((vfPairHomeomorph n).continuous.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
    have he : (Prod.map id (chart b)) ⁻¹' C = ψ ⁻¹' {p | (p.1.val,p.2) ∈ B b} := by
      ext p
      change (p.1.2,chart b p.2) ∈ F p.1.1.val ↔
        p.1.1.val ∈ I ∧ projectiveFibreChart b (vfPairHomeomorph n (p.2,p.1.2)) ∈ F p.1.1.val
      rw [projectiveFibreChart_join]
      exact (and_iff_right p.1.1.property.1).symm
    rw [he]
    exact (hEc b).preimage hψ
  have hC : IsClosed C := isClosed_projective_unary_of_charts C (hLocal false) (hLocal true)
  let ρ (p : ↥(I \ Eall) × ((Fin n → VF M) × (Fin 1 → ProjectiveLine (VF M)))) :
      X × (Fin 1 → ProjectiveLine (VF M)) := ((p.1,p.2.1),p.2.2)
  have hρ : Continuous ρ :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)
  exact hC.preimage hρ

end DiamondIntegral.Section2
