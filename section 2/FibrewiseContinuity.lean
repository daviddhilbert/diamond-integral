import «section 2».ProjectiveFamilyClosedness

/-! Proposition 2.55. Fibrewise continuity gives joint continuity after
removing an original-base finite definable set of unary base points. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vfPairMapGraph_remove_base_definable {S : Set M}
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin m → VF M)
    (hf : S.Definable LRV (vfPairMapGraph A f))
    (E : Set (Fin 1 → VF M)) (hE : S.Definable LRV (vfValues '' E)) :
    S.Definable LRV (vfPairMapGraph {p ∈ A | p.1 ∉ E} f) := by
  let π : Fin 1 → (Fin 1 ⊕ Fin n) ⊕ Fin m := Sum.inl ∘ Sum.inl
  have h := hf.inter (hE.preimage_comp π).compl
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,⟨hp,hpE⟩,rfl⟩
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    rintro ⟨a,ha,he⟩
    have hap : a = p.1 := vfValues_injective he
    exact hpE (hap ▸ ha)
  · rintro ⟨⟨p,hp,he⟩,hno⟩
    refine ⟨p,⟨hp,?_⟩,he⟩
    intro hpE
    apply hno
    exact ⟨p.1,hpE,funext (fun i => congrFun he (.inl (.inl i)))⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Proposition 2.55 over a fixed definable unary base, allowing empty
domain fibres and zero tail arity. All finite exceptions and their full
definability are constructed over the original real base. -/
theorem proposition_2_55
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ)
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin 1 → VF M)
    (hf : S.Definable LRV (vfPairMapGraph A f))
    (hfibres : ∀ a ∈ I, ContinuousOn (fun x => f (a,x)) {x | (a,x) ∈ A}) :
    ∃ E ⊆ I, E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      ContinuousOn f {p ∈ A | p.1 ∉ E} := by
  classical
  let F (a : Fin 1 → VF M) := closure (projectiveFibreGraph A f a)
  have hFdef (b : Bool) : S.Definable LRV (vfCorrespondenceGraph I
      (fun a => (projectiveFibreChart b) ⁻¹' F a)) :=
    projectiveFibreChart_closure_graph_definable hv I hI A hAI f hf b
  obtain ⟨E,hEI,hEf,hE,hFclosed⟩ := projective_family_closed_off_finite h00 hc hκ hs hv I hI F
    (fun _ _ => isClosed_closure) hFdef
  have hfAll : ∀ a : Fin 1 → VF M, ContinuousOn (fun x => f (a,x)) {x | (a,x) ∈ A} := by
    intro a
    by_cases ha : a ∈ I
    · exact hfibres a ha
    · have he : {x | (a,x) ∈ A} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        exact fun x hx => ha (hAI hx).1
      rw [he]
      intro x hx
      exact hx.elim
  have hRecover := projectiveFibreClosure_graph_inter hv A (fun a x => f (a,x)) hfAll
  let D := {p ∈ A | p.1 ∉ E}
  let base (p : D) : ↥(I \ E) := ⟨p.val.1,(hAI p.property.1).1,p.property.2⟩
  have hbase : Continuous base := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  let ψ (q : D × (Fin 1 → ProjectiveLine (VF M))) :
      ↥(I \ E) × ((Fin n → VF M) × (Fin 1 → ProjectiveLine (VF M))) :=
    (base q.1,(q.1.val.2,q.2))
  have hψ : Continuous ψ :=
    (hbase.comp continuous_fst).prodMk
      (((continuous_snd.comp continuous_subtype_val).comp continuous_fst).prodMk continuous_snd)
  have hGraph : IsClosed (relativePairProjectiveGraph D f) := by
    have he : relativePairProjectiveGraph D f = ψ ⁻¹' {p | p.2 ∈ F p.1.val} := by
      ext q
      change q.2 = finiteProjectiveTuple (f q.1.val) ↔ (q.1.val.2,q.2) ∈ F q.1.val.1
      constructor
      · intro hq
        rw [hq]
        exact subset_closure ⟨q.1.property.1,rfl⟩
      · intro hq
        have hmem : (q.1.val.1,(q.1.val.2,q.2)) ∈
            fibreClosure (fibreGraph A (fun a x => finiteProjectiveTuple (f (a,x)))) ∩
              {p | (p.1,p.2.1) ∈ A} := ⟨hq,q.1.property.1⟩
        rw [hRecover] at hmem
        exact hmem.2
    rw [he]
    exact hFclosed.preimage hψ
  refine ⟨E,hEI,hEf,hE,?_⟩
  exact (continuousOn_pair_iff_projective_graph_isClosed h00 hc hκ hs hv D f
    (vfPairMapGraph_remove_base_definable A f hf E hE)).mpr hGraph

end DiamondIntegral.Section2
