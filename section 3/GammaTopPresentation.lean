import «section 3».GammaFormOperations
import «section 3».TupleRVMap

/-! The complete value-group-with-zero presentation and the actual
valuation map. Zero determinants remain visible in measure equations. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaTopSpace : Space LRV M where
  Carrier := Values.GammaTop (M := M)
  Index := Fin 1
  finiteIndex := inferInstance
  domain := {z | iRV (z 0)}
  domain_definable := (definableAt_sort (∅ : Set M) .rv).raw_definable
  decode c := Values.vrv ⟨c.val 0, c.property⟩
  onto γ := by
    obtain ⟨t, ht⟩ := Values.vrv_surjective γ
    exact ⟨⟨![t.val], t.property⟩, ht⟩
  diagonal_definable := by
    have hd := (definableAt_sort (∅ : Set M) .rv).raw_definable
    have hl := hd.preimage_comp (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
    have hr := hd.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    have hrel : (∅ : Set M).Definable LRV {z : Fin 2 → M | Structure.RelMap (L := LRV) Rel.rvLe z} :=
      Set.empty_definable_iff.mpr ⟨.rel Rel.rvLe (fun i => .var (.inl i)), rfl⟩
    have hle : (∅ : Set M).Definable LRV {z : Fin 1 ⊕ Fin 1 → M | iLe (z (.inl 0)) (z (.inr 0))} := by
      have h := hrel.preimage_comp (![.inl 0, .inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
      convert h using 1
      ext z
      change Structure.RelMap (L := LRV) Rel.rvLe ![z (.inl 0), z (.inr 0)] ↔
        Structure.RelMap (L := LRV) Rel.rvLe (z ∘ ![.inl 0, .inr 0])
      have he : z ∘ ![Sum.inl 0, Sum.inr 0] = ![z (.inl 0), z (.inr 0)] := by
        funext i
        fin_cases i <;> rfl
      rw [he]
    have hge := hle.preimage_comp (Sum.swap : Fin 1 ⊕ Fin 1 → Fin 1 ⊕ Fin 1)
    convert hl.inter (hr.inter (hle.inter hge)) using 1
    ext z
    constructor
    · rintro ⟨hx, hy, he⟩
      exact ⟨hx, hy, (Values.vrv_eq_iff _ _).mp he⟩
    · rintro ⟨hx, hy, he⟩
      exact ⟨hx, hy, (Values.vrv_eq_iff _ _).mpr he⟩

def rvGammaTopMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ gammaTopSpace S) := by
  have hdom (c : (rawRVSpace (M := M) 1).domain) : c.val ∈ gammaTopSpace.domain := by
    have h := ((rawRVSpace (M := M) 1).decode c 0).property
    change iRV (c.val (0 : Fin 1))
    rw [← congrFun (rvValues_decode c) 0]
    exact h
  refine Map.ofCodes _ (fun t => Values.vrv (t 0)) id (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply congrArg Values.vrv
  exact Subtype.ext (congrFun (rvValues_decode c) 0).symm

def gammaTopValuationMap (S : Set M) :
    Map (DefSet.univ (rawVFSpace (M := M) 1) S) (DefSet.univ gammaTopSpace S) :=
  (rvGammaTopMap S).comp (universalTupleRVMap S 1)

@[simp] theorem gammaTopValuationMap_value (S : Set M) (a : DefSet.univ (rawVFSpace (M := M) 1) S) :
    (gammaTopValuationMap S a).val = Values.vfValueHom (a.val 0) := rfl

def gammaIncludeTopMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    Map (DefSet.univ (volumeGammaSpace hc) S) (DefSet.univ gammaTopSpace S) := by
  refine Map.ofCodes _ (fun γ : Values.Gamma (M := M) => γ.val) id
    (fun _ => Set.DefinableFun.proj LRV) (fun c => c.property.1) ?_
  intro c
  rfl

def gammaTopMultiplyMap (S : Set M) :
    Map (DefSet.univ (gammaTopSpace.prod gammaTopSpace) S) (DefSet.univ gammaTopSpace S) := by
  let F (z : Fin 1 ⊕ Fin 1 → M) : Fin 1 → M := fun _ => iRVMul (z (.inl 0)) (z (.inr 0))
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun z : Fin 1 ⊕ Fin 1 → M => ![z (.inl 0), z (.inr 0)]) from
        fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
  refine Map.ofCodes _ (fun p : Values.GammaTop (M := M) × Values.GammaTop (M := M) => p.1 * p.2)
    F hF (fun c => rv_mul_mem hM c.property.1 c.property.2) ?_
  intro c
  exact Values.vrv_mul (M := M)
    ⟨c.val (.inl (0 : Fin 1)), c.property.1⟩ ⟨c.val (.inr (0 : Fin 1)), c.property.2⟩

end DiamondIntegral.Section3
