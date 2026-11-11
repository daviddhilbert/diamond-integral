import «section 2».BadFibreChoice
import «section 2».ClosedBoundedImages

/-! The uniform-radius step of Lemma 2.54. A definable family of bad-locus
points whose fibre balls all work at one radius has finite unary projection.
Finite choice, a continuity point and the open rectangle are constructed. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem uniform_bad_fibre_projection_finite
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I D : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (T : (Fin 1 → VF M) → Set (Fin n → VF M)) (γ : Gamma M)
    {S : Set M} (hG : S.Definable LRV (vfCorrespondenceGraph D T))
    (hne : ∀ a ∈ D, (T a).Nonempty)
    (hT : ∀ a ∈ D, ∀ x ∈ T a,
      (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A ∧ ∀ y ∈ vfBall x γ, (a,y) ∈ A) : D.Finite := by
  classical
  have hD := vfCorrespondence_domain_definable D T hG hne
  by_contra hDfin
  have hInt : (interior D).Nonempty := by
    by_contra hn
    exact hDfin (unary_definable_finite_of_interior_empty_any_base hc hκ hs hv D hD
      (Set.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨a,haInt⟩ := hInt
  obtain ⟨δ,hδ⟩ := exists_vfBall_subset_nhds hv a (mem_interior_iff_mem_nhds.mp haInt)
  let U := vfBall a δ
  have hUop : IsOpen U := vfBall_isOpen hv a δ
  have hUne : U.Nonempty := ⟨a,mem_vfBall_self a δ⟩
  have hU : (Set.univ : Set M).Definable LRV (vfValues '' U) := vfBall_definable_univ hc a δ
  have hTU : (Set.univ : Set M).Definable LRV (vfCorrespondenceGraph U T) :=
    vfCorrespondence_restrict_definable D U hδ hU T (hG.mono (Set.subset_univ _))
  obtain ⟨C,hsmall,hUC,hTC,B,x,hx0,hxv⟩ :=
    exists_small_vf_generated_base_for_two_definable hv hκ (vfValues '' U) hU
      (vfCorrespondenceGraph U T) hTU
  let p0 : Fin 0 → VF M := Fin.elim0
  let V := vfFieldNames B.field ∪ Set.range (vfValues p0)
  let R : Set M := (C : Set M) ∪ Set.range (vfValues p0)
  obtain ⟨hV,hVR,hRV,hntV⟩ := VFGeneratedFieldBase.parameter_core Valued.v C.toSubstructure B
    ⟨x,hx0,ne_of_lt hxv⟩ p0
  have hRsmall : Cardinal.mk R < κ := small_union_range hκ.le (C : Set M) hsmall (vfValues p0)
  obtain ⟨F,hF,hfin,hsub,hFne⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V R hV hVR hRV
    hntV hRsmall U (hUC.mono Set.subset_union_left) T (hTC.mono Set.subset_union_left)
    (fun b hb => hne b (hδ hb))
  obtain ⟨E,hEU,hEf,hE,hcont⟩ := lemma_2_44_unary h00 hc hκ.le hs hRsmall hv U
    (hUC.mono Set.subset_union_left) F hF (fun b _ => hfin b)
  obtain ⟨b,hb⟩ := ((vf_open_nonempty_infinite hv (by decide : 0 < 1) U hUop hUne).sdiff hEf).nonempty
  exact no_finite_continuous_choice_in_uniform_bad_locus hc hκ hs hv I U hUop A F γ hF
    (fun c hcU y hy => hT c (hδ hcU) y (hsub c hy))
    (fun c hcU => (hFne c).mpr hcU) b hb.1 (hfin b) (hcont b hb).1

end DiamondIntegral.Section2
