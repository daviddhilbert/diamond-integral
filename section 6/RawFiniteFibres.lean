import «section 6».FiniteRVHittingSets

/-! Complete raw-code extension of a finite VF family over a definable
VF domain. Invalid codes and codes outside that domain have empty fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

def rawFiniteFibre (A : Set (Fin n → VF M)) (E : (Fin n → VF M) → Set (VF M))
    (hFin : ∀ a, (E a).Finite) (t : Fin n → M) : Finset (VF M) :=
  if h : ∃ a ∈ A, vfValues a = t then (hFin h.choose).toFinset else ∅

theorem rawFiniteFibre_at (A : Set (Fin n → VF M)) (E : (Fin n → VF M) → Set (VF M))
    (hFin : ∀ a, (E a).Finite) (a : Fin n → VF M) (ha : a ∈ A) :
    rawFiniteFibre A E hFin (vfValues a) = (hFin a).toFinset := by
  have h : ∃ b ∈ A, vfValues b = vfValues a := ⟨a,ha,rfl⟩
  rw [rawFiniteFibre,dite_eq_left h]
  have he : h.choose = a := vfValues_injective h.choose_spec.2
  apply Finset.ext
  intro x
  simpa only [Set.Finite.mem_toFinset] using Set.ext_iff.mp (congrArg E he) x

theorem rawFiniteFibre_definable (A : Set (Fin n → VF M))
    (E : (Fin n → VF M) → Set (VF M)) (hFin : ∀ a, (E a).Finite)
    (hE : S.Definable LRV (scalarFibreGraph A E)) :
    RawClosure.Tuple.RelationDefinable S (Barycentre.finiteFibreRelation (rawFiniteFibre A E hFin)) := by
  change S.Definable LRV {z : Fin n ⊕ Fin 1 → M |
    ∃ x ∈ rawFiniteFibre A E hFin (z ∘ Sum.inl), x.val = z (.inr 0)}
  convert hE using 1
  ext z
  constructor
  · rintro ⟨x,hx,hxz⟩
    have h : ∃ a ∈ A, vfValues a = z ∘ Sum.inl := by
      by_contra hn
      have hz : rawFiniteFibre A E hFin (z ∘ Sum.inl) = ∅ := dite_eq_right hn
      exact Finset.notMem_empty x (hz ▸ hx)
    obtain ⟨a,ha,he⟩ := h
    have hxE : x ∈ E a := by
      rw [← he,rawFiniteFibre_at A E hFin a ha] at hx
      exact (hFin a).mem_toFinset.mp hx
    refine ⟨a,ha,x,hxE,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun he i
    | inr i => fin_cases i; exact hxz
  · rintro ⟨a,ha,x,hx,he⟩
    have hleft : vfValues a = z ∘ Sum.inl := funext (fun i => congrFun he (.inl i))
    refine ⟨x,?_,congrFun he (.inr 0)⟩
    rw [← hleft,rawFiniteFibre_at A E hFin a ha]
    exact (hFin a).mem_toFinset.mpr hx

def rvFilteredFibre (F : (Fin n → M) → Finset (VF M)) (t : Fin (n+1) → M) : Finset (VF M) :=
  (F (Fin.init t)).filter (fun x => iRv x.val = t (Fin.last n))

theorem rvFilteredFibre_definable
    (F : (Fin n → M) → Finset (VF M))
    (hF : RawClosure.Tuple.RelationDefinable S (Barycentre.finiteFibreRelation F)) :
    RawClosure.Tuple.RelationDefinable S (Barycentre.finiteFibreRelation (rvFilteredFibre F)) := by
  let idx : Fin n ⊕ Fin 1 → Fin (n+1) ⊕ Fin 1 := Sum.elim (Sum.inl ∘ Fin.castSucc) Sum.inr
  have hBase := hF.preimage_comp idx
  have hrv : S.DefinableFun LRV (fun z : Fin (n+1) ⊕ Fin 1 → M => iRv (z (.inr 0))) :=
    (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : Fin (n+1) ⊕ Fin 1 → M => ![z (.inr 0)]) from
        fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  have heq := hrv.ofPred_eq
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl (Fin.last n) : Fin (n+1) ⊕ Fin 1)))
  change S.Definable LRV {z : Fin (n+1) ⊕ Fin 1 → M |
    ∃ x ∈ rvFilteredFibre F (z ∘ Sum.inl), x.val = z (.inr 0)}
  convert hBase.inter heq using 1
  ext z
  change (∃ x ∈ rvFilteredFibre F (z ∘ Sum.inl), x.val = z (.inr 0)) ↔
    (∃ x ∈ F (Fin.init (z ∘ Sum.inl)), x.val = z (.inr 0)) ∧
      iRv (z (.inr 0)) = z (.inl (Fin.last n))
  constructor
  · rintro ⟨x,hx,he⟩
    obtain ⟨hx,hRv⟩ := Finset.mem_filter.mp hx
    exact ⟨⟨x,hx,he⟩,by simpa only [he,Function.comp_apply] using hRv⟩
  · rintro ⟨⟨x,hx,he⟩,hRv⟩
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,by simpa only [he,Function.comp_apply] using hRv⟩,he⟩

end DiamondIntegral.Section6
