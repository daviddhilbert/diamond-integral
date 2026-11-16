import «section 6».DefinableFiniteMeans

/-! A definable finitary RV family over full VF inputs has a finite
original-base VF family meeting all prescribed RV discs. Uniform bounds
are obtained from genuine saturation, rather than assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

private theorem finite_rv_family_hitting_tuple
    (C : Set M) (hC : C.Finite) (hRV : ∀ v ∈ C, iRV v)
    (N : ℕ) (hN : C.ncard ≤ N) :
    (HittingTuples {q : Fin 1 → M | q 0 ∈ C}
      (fun q x => iVF x ∧ iRv x = q 0) N).Nonempty := by
  let Q := hC.toFinset
  let e := Finset.equivFin Q
  have hcard : Q.card ≤ N := by
    rw [← Set.ncard_eq_toFinset_card C hC]
    exact hN
  let j (q : Q) : Fin N := (e q).castLE hcard
  have hj : Function.Injective j := by
    intro a b hab
    apply e.injective
    exact Fin.ext (congrArg (fun k : Fin N => k.val) hab)
  have hr (q : Q) : ∃ x : VF M, iRv x.val = q.val := by
    obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective
      (⟨q.val,hRV q.val (hC.mem_toFinset.mp q.property)⟩ : CanonicalRV.RVSort M)
    exact ⟨x,congrArg Subtype.val hx⟩
  let point (q : Q) : VF M := (hr q).choose
  let a : Fin N → VF M := Function.extend j point (fun _ => 0)
  refine ⟨a,?_⟩
  intro q hq
  let u : Q := ⟨q 0,hC.mem_toFinset.mpr hq⟩
  refine ⟨j u,(a (j u)).property,?_⟩
  have he : a (j u) = point u := hj.extend_apply point (fun _ => 0) u
  rw [he]
  exact (hr u).choose_spec

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_rv_hitting_sets
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (C : (Fin n → M) → Set M)
    (hC : S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ C (z ∘ Sum.inl)})
    (hFin : ∀ a, (C a).Finite) (hRV : ∀ a, ∀ v ∈ C a, iRV v) :
    ∃ E : (Fin n → VF M) → Set (VF M),
      S.Definable LRV (scalarFibreGraph A E) ∧ (∀ a, (E a).Finite) ∧
      ∀ a ∈ A, ∀ v ∈ C (vfValues a), ∃ x ∈ E a, iRv x.val = v := by
  obtain ⟨N,hN⟩ := uniform_finite_fibre_bound hs S hsmall {p | p.2 ∈ C p.1} hC hFin
  have hR : S.Definable LRV
      {z : Fin 1 ⊕ Fin 1 → M | iVF (z (.inr 0)) ∧ iRv (z (.inr 0)) = z (.inl 0)} := by
    have hrv : S.DefinableFun LRV (fun z : Fin 1 ⊕ Fin 1 → M => iRv (z (.inr 0))) :=
      (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
        (show S.DefinableMap LRV (fun z : Fin 1 ⊕ Fin 1 → M => ![z (.inr 0)]) from
          fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
    have heq := hrv.ofPred_eq
      (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1)))
    convert ((vfRawUniverse_definable S 1).preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)).inter heq using 1
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,vfRawUniverse,
      Function.comp_apply,Fin.forall_fin_one]
  obtain ⟨E,hE,hEf,hHit⟩ := exists_parametric_finite_hitting_sets hc h00 hs hv V S hV hVS hSV hnt hsmall
    A hA (fun a => {q : Fin 1 → M | q 0 ∈ C a}) hC
    (fun q x => iVF x ∧ iRv x = q 0) hR N
    (fun a _ => finite_rv_family_hitting_tuple (C (vfValues a)) (hFin _) (hRV _) N (hN _))
  refine ⟨E,hE,hEf,?_⟩
  intro a ha v hvC
  obtain ⟨x,hx,hR⟩ := hHit a ha (fun _ : Fin 1 => v) hvC
  exact ⟨x,hx,hR.2⟩

end DiamondIntegral.Section6
