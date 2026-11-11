import «section 2».OpenDiscPartitions
import «section 2».InfinityApproach
import Section3.GammaFiniteOrder

/-! Full invariant RV-code graphs for Gamma-valued partitions and their
uniform escaping fibres. No section of the value-group quotient is chosen. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def vfGammaGraph (A : Set (Fin n → VF M)) (p : (Fin n → VF M) → Gamma M) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | GammaParameters.NonzeroRV (z (.inr 0)) ∧
    ∃ x ∈ A, vfValues x = z ∘ Sum.inl ∧ GammaParameters.codeValue (z (.inr 0)) = p x}

def partitionEscape (A : Set (Fin n → VF M)) (p : (Fin n → VF M) → Gamma M)
    (c : Fin 1 → VF M) : Set (Fin n → VF M) := {x ∈ A | vfValue (c 0) < (p x).val}

theorem codeValue_rv_finite (r : VF M) (hr : r ≠ 0) :
    GammaParameters.codeValue (iRv r.val) = finiteValue r hr := by
  have ht : GammaParameters.NonzeroRV (iRv r.val) :=
    ⟨(rv M r).property,fun h => hr ((rv_eq_zero_iff r).mp (Subtype.ext h))⟩
  rw [GammaParameters.codeValue,dite_eq_left ht]
  rfl

theorem partitionEscape_graph_definable {S : Set M}
    (U : Set (Fin 1 → VF M)) (hU : S.Definable LRV (vfValues '' U))
    (hU0 : ∀ c ∈ U, c 0 ≠ 0)
    (A : Set (Fin n → VF M)) (p : (Fin n → VF M) → Gamma M)
    (hp : S.Definable LRV (vfGammaGraph A p)) :
    S.Definable LRV (vfCorrespondenceGraph U (partitionEscape A p)) := by
  let e : Fin n ⊕ Fin 1 → (Fin 1 ⊕ Fin n) ⊕ Fin 1 :=
    Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
  have hrv : S.DefinableFun LRV (fun z : (Fin 1 ⊕ Fin n) ⊕ Fin 1 → M =>
      iRv (z (.inl (.inl 0)))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : (Fin 1 ⊕ Fin n) ⊕ Fin 1 → M =>
        ![z (.inl (.inl 0))]) from by
          intro i
          fin_cases i
          exact Set.DefinableFun.proj LRV)
  have hlt := ((GammaParameters.raw_le_definable S).preimage_map
    (show S.DefinableMap LRV (fun z : (Fin 1 ⊕ Fin n) ⊕ Fin 1 → M =>
      ![z (.inr 0),iRv (z (.inl (.inl 0)))]) from by
        intro i
        fin_cases i
        · exact Set.DefinableFun.proj LRV
        · exact hrv)).compl
  have h := (((hU.preimage_comp (fun i : Fin 1 => Sum.inl (Sum.inl i))).inter
    (hp.preimage_comp e)).inter hlt).exists_of_finite
  convert h using 1
  ext z
  change (∃ c ∈ U, ∃ x ∈ partitionEscape A p c, Sum.elim (vfValues c) (vfValues x) = z) ↔
    ∃ t : Fin 1 → M,
      (z ∘ Sum.inl ∈ vfValues '' U ∧ Sum.elim z t ∘ e ∈ vfGammaGraph A p) ∧
        ¬ iLe (t 0) (iRv (z (.inl 0)))
  constructor
  · rintro ⟨c,hc,x,⟨hx,hescape⟩,rfl⟩
    obtain ⟨t,ht,het⟩ := GammaParameters.EndpointLogic.codeValue_surjective (p x)
    have hrNZ : GammaParameters.NonzeroRV (iRv (c 0).val) :=
      ⟨(rv M (c 0)).property,fun h => hU0 c hc
        ((rv_eq_zero_iff (c 0)).mp (Subtype.ext h))⟩
    refine ⟨![t],⟨⟨c,hc,rfl⟩,ht,x,hx,rfl,het⟩,?_⟩
    change ¬ iLe t (iRv (c 0).val)
    rw [GammaParameters.original_le_codeValue_iff t _ ht hrNZ,het,
      codeValue_rv_finite (c 0) (hU0 c hc),not_le]
    exact hescape
  · rintro ⟨t,⟨⟨c,hc,hce⟩,ht,x,hx,hxe,het⟩,hno⟩
    change GammaParameters.NonzeroRV (t 0) at ht
    change GammaParameters.codeValue (t 0) = p x at het
    change vfValues x = z ∘ Sum.inr at hxe
    have hc0 : (c 0).val = z (.inl 0) := congrFun hce 0
    have hrNZ : GammaParameters.NonzeroRV (iRv (c 0).val) :=
      ⟨(rv M (c 0)).property,fun h => hU0 c hc
        ((rv_eq_zero_iff (c 0)).mp (Subtype.ext h))⟩
    have hescape : vfValue (c 0) < (p x).val := by
      rw [← hc0,GammaParameters.original_le_codeValue_iff (t 0) _ ht hrNZ,het,
        codeValue_rv_finite (c 0) (hU0 c hc),not_le] at hno
      exact hno
    refine ⟨c,hc,x,⟨hx,hescape⟩,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun hce i
    | inr i => exact congrFun hxe i

theorem partitionEscape_nonempty_of_unbounded
    (A : Set (Fin n → VF M)) (p : (Fin n → VF M) → Gamma M) (hp : ¬ BddAbove (p '' A))
    (c : Fin 1 → VF M) (hc : c 0 ≠ 0) : (partitionEscape A p c).Nonempty := by
  obtain ⟨γ,⟨x,hx,rfl⟩,hγ⟩ := not_bddAbove_iff.mp hp (finiteValue (c 0) hc)
  exact ⟨x,hx,hγ⟩

end DiamondIntegral.Section2
