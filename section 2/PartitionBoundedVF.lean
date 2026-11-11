import «section 2».PartitionEscape
import «section 2».ClosedBoundedImages

/-! The pure VF case of Lemma 2.53. Finite choices in escaping partition
fibres are constructed over a temporary small VF-generated base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem openDiscPartition_bddAbove_vf_core
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → VF M)) (hAcl : IsClosed A)
    (hAb : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i))
    (p : (Fin n → VF M) → Gamma M) (hp : IsOpenDiscPartition A p)
    (hpdef : S.Definable LRV (vfGammaGraph A p)) : BddAbove (p '' A) := by
  classical
  by_contra hbad
  let P := partitionEscape A p
  have hP : S.Definable LRV (vfCorrespondenceGraph curveSource P) :=
    partitionEscape_graph_definable curveSource (curveSource_definable S) curveSource_nonzero A p hpdef
  have hPne : ∀ c ∈ curveSource, (P c).Nonempty :=
    fun c hcU => partitionEscape_nonempty_of_unbounded A p hbad c (curveSource_nonzero c hcU)
  obtain ⟨F,hF,hfin,hsub,hne⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V S hV hVS hSV
    hnt hsmall curveSource (curveSource_definable S) P hP hPne
  have hFA : ∀ c ∈ curveSource, F c ⊆ A := fun c _ x hx => (hsub c hx).1
  obtain ⟨L,hLf,hLA,hL,hLdef⟩ := lemma_2_45 hc hs hsmall hv curveSource F A hAcl hAb hF
    (fun c _ => hfin c) hFA
  have hLne : L.Nonempty := hL.1.nonempty_of_frequent_values (by
    intro δ
    obtain ⟨c,hcU,hnear⟩ := curveSource_accumulates (M := M) δ
    exact ⟨c,hcU,hnear,(hne c).mpr hcU.1⟩)
  have hLempty := IsOpenDiscPartition.no_escape_limit hp curveSource F L hL hLA hFA
    (fun c _ x hx => (hsub c hx).2)
  exact Set.not_nonempty_empty (hLempty ▸ hLne)

/-- Lemma 2.53 with no RV coordinates. Both bounds are proved, including
the empty set and zero VF arity, over an arbitrary real parameter base. -/
theorem lemma_2_53_vf
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hAcl : IsClosed A) (hAb : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i))
    (p : (Fin n → VF M) → Gamma M) (hp : IsOpenDiscPartition A p)
    (hpdef : S.Definable LRV (vfGammaGraph A p)) : BddBelow (p '' A) ∧ BddAbove (p '' A) := by
  refine ⟨IsOpenDiscPartition.bddBelow hp hAb,?_⟩
  obtain ⟨C,hsmall,hAC,hpC,B,x,hx0,hxv⟩ :=
    exists_small_vf_generated_base_for_two_definable hv hκ (vfValues '' A) hA (vfGammaGraph A p) hpdef
  let p0 : Fin 0 → VF M := Fin.elim0
  obtain ⟨hV,hVT,hTV,hntV⟩ := VFGeneratedFieldBase.parameter_core Valued.v C.toSubstructure B
    ⟨x,hx0,ne_of_lt hxv⟩ p0
  exact openDiscPartition_bddAbove_vf_core h00 hc hs hv
    (vfFieldNames B.field ∪ Set.range (vfValues p0)) ((C : Set M) ∪ Set.range (vfValues p0))
    hV hVT hTV hntV (small_union_range hκ.le (C : Set M) hsmall (vfValues p0))
    A hAcl hAb p hp (hpC.mono Set.subset_union_left)

end DiamondIntegral.Section2
