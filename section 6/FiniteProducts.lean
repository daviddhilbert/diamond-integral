import «section 6».UniformMixedRadius
import Section3.DefinableMeans

/-! An unordered finite product of a definable finite VF set is definable
over its original base. No enumeration is added as a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.Barycentre
open RawClosure.Tuple
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rawProduct : (k : ℕ) → (Fin k → M) → M
  | 0, _ => iVFOne
  | k+1, c => iVFMul (c 0) (rawProduct k (Fin.tail c))

theorem rawProduct_definable (S : Set M) (k : ℕ) : S.DefinableFun LRV (rawProduct (M := M) k) := by
  induction k with
  | zero =>
      exact SpecialTransformations.DefinableConstants.constant
        (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  | succ k ih =>
      exact scalarMulCode_definable (Set.DefinableFun.proj LRV)
        (ih.comp (show S.DefinableMap LRV (Fin.tail : (Fin (k+1) → M) → Fin k → M) from
          fun _ => Set.DefinableFun.proj LRV))

theorem rawProduct_at (k : ℕ) (c : Fin k → VF M) :
    rawProduct k (vfValues c) = (∏ i, c i).val := by
  induction k with
  | zero => simp only [rawProduct,Fin.prod_univ_zero]; rfl
  | succ k ih =>
      rw [Fin.prod_univ_succ]
      change iVFMul (c 0).val (rawProduct k (vfValues (fun i => c i.succ))) = _
      rw [ih]
      rfl

theorem enumerated_product (F : Finset (VF M)) {k : ℕ} (c : Fin k → M)
    (hc : Enumerates (finiteFibreRelation (fun _ : Fin 0 → M => F)) k Fin.elim0 c) :
    rawProduct k c = (∏ x ∈ F, x).val := by
  classical
  have hsort (i : Fin k) : iVF (c i) := by
    obtain ⟨x,_,hx⟩ := hc.2.1 i
    change x.val = c i at hx
    rw [← hx]
    exact x.property
  let C (i : Fin k) : VF M := ⟨c i,hsort i⟩
  have hmem (i : Fin k) : C i ∈ F := by
    obtain ⟨x,hx,he⟩ := hc.2.1 i
    exact (show x = C i from Subtype.ext he) ▸ hx
  let e0 (i : Fin k) : ↥F := ⟨C i,hmem i⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      exact hc.1 (congrArg (fun x : ↥F => x.val.val) hij)
    · intro x
      obtain ⟨i,hi⟩ := hc.2.2 x.val.val ⟨x.val,x.property,rfl⟩
      exact ⟨i,Subtype.ext (Subtype.ext hi)⟩
  let e : Fin k ≃ ↥F := Equiv.ofBijective e0 he0
  have hprod : (∏ i, C i) = ∏ x ∈ F, x := by
    calc
      _ = ∏ x : ↥F, x.val := Fintype.prod_equiv e C (fun x => x.val) (fun _ => rfl)
      _ = _ := F.prod_attach id
  exact (rawProduct_at k C).trans (congrArg Subtype.val hprod)

theorem finiteProduct_definable (S : Set M) (F : Finset (VF M))
    (hF : S.Definable₁ LRV (Subtype.val '' (F : Set (VF M)))) :
    S.Definable₁ LRV {(∏ x ∈ F, x).val} := by
  classical
  let R := finiteFibreRelation (fun _ : Fin 0 → M => F)
  have hR : RelationDefinable S R := by
    change S.Definable LRV {w : Fin 0 ⊕ Fin 1 → M | ∃ x ∈ F, x.val = w (.inr 0)}
    convert hF.preimage_comp (Sum.inr : Fin 1 → Fin 0 ⊕ Fin 1) using 1
    ext w
    rfl
  let k := F.card
  let idx : Fin 0 ⊕ Fin k → Fin 1 ⊕ Fin k := Sum.elim Fin.elim0 Sum.inr
  have he := (enumeration_definable S R hR k).preimage_comp idx
  have hp := (rawProduct_definable S k).comp
    (show S.DefinableMap LRV (fun w : Fin 1 ⊕ Fin k → M => w ∘ Sum.inr) from
      fun _ => Set.DefinableFun.proj LRV)
  have h := (he.inter (hp.ofPred_eq (Set.DefinableFun.proj (L := LRV) (i := (.inl 0))))).exists_of_finite
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ {(∏ x ∈ F, x).val}}
  convert h using 1
  ext z
  constructor
  · intro hz
    obtain ⟨c,hc⟩ := finiteFibre_enumeration_exists (fun _ : Fin 0 → M => F) Fin.elim0
    refine ⟨c,?_,?_⟩
    · exact hc
    · exact (enumerated_product F c hc).trans (Set.mem_singleton_iff.mp hz).symm
  · rintro ⟨c,hc,hprod⟩
    exact Set.mem_singleton_iff.mpr (hprod.symm.trans (enumerated_product F c hc))

end DiamondIntegral.Section6
