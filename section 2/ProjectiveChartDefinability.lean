import «section 2».ProjectiveCharts
import «section 2».DefinableVFInverse
import «section 2».FinitaryCoding

/-!
# Same-base definability of reciprocal charts

Inverse is defined by its field graph, not treated as a new LRV symbol.
Chart images are guarded preimages under the same involution. Full curve
graphs retain the input coordinate and every output coordinate.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n k : ℕ}

noncomputable def rawInvertCoordinates (mask : Fin n → Bool) (x : Fin n → M) : Fin n → M :=
  fun i => if mask i then rawVFInverse (x i) else x i

theorem rawInvertCoordinates_definable (S : Set M) (mask : Fin n → Bool) :
    S.DefinableMap LRV (rawInvertCoordinates mask) := by
  intro i
  cases h : mask i with
  | false => simpa only [rawInvertCoordinates,h,Bool.false_eq_true,ite_false] using
      (Set.DefinableFun.proj LRV (i := i))
  | true => simpa only [rawInvertCoordinates,h,ite_true] using rawVFInverse_definable S i

theorem vfValues_invertCoordinates (mask : Fin n → Bool) (x : Fin n → VF M) :
    vfValues (invertCoordinates mask x) = rawInvertCoordinates mask (vfValues x) := by
  funext i
  cases h : mask i with
  | false => simp only [vfValues,invertCoordinates,rawInvertCoordinates,h,Bool.false_eq_true,ite_false]
  | true =>
    simp only [vfValues,invertCoordinates,rawInvertCoordinates,h,ite_true]
    exact (rawVFInverse_vf (x i)).symm

theorem inversionDomain_definable (S : Set M) (mask : Fin n → Bool) :
    S.Definable LRV (vfValues '' inversionDomain (M := M) mask) := by
  have hz : S.DefinableFun LRV (fun _ : Fin n → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hc (i : Fin n) : S.Definable LRV {z : Fin n → M | mask i = true → z i ≠ iVFZero} := by
    cases h : mask i with
    | false => simpa only [h,Bool.false_eq_true,IsEmpty.forall_iff,Set.setOf_true] using
        (Set.definable_univ (L := LRV) (A := S) (α := Fin n))
    | true =>
      convert ((Set.DefinableFun.proj LRV (i := i)).ofPred_eq hz).compl using 1
      ext z
      simp only [h,forall_true_left,Set.mem_ofPred_eq,Set.mem_compl_iff]
  have h := (vfRawUniverse_definable S n).inter (Set.definable_iInter_of_finite hc)
  convert h using 1
  ext z
  simp only [Set.mem_image,Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq,vfRawUniverse]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨fun i => (x i).property,fun i hi he => hx i hi (Subtype.ext he)⟩
  · rintro ⟨hs,hne⟩
    let x : Fin n → VF M := fun i => ⟨z i,hs i⟩
    exact ⟨x,fun i hi he => hne i hi (congrArg Subtype.val he),rfl⟩

theorem invertCoordinates_image_definable {S : Set M} (mask : Fin n → Bool)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) :
    S.Definable LRV (vfValues '' (invertCoordinates mask '' A)) := by
  have h := (vfRawUniverse_definable S n).inter
    (hA.preimage_map (rawInvertCoordinates_definable S mask))
  convert h using 1
  ext z
  change (∃ x ∈ invertCoordinates mask '' A, vfValues x = z) ↔
    (∀ i, iVF (z i)) ∧ rawInvertCoordinates mask z ∈ vfValues '' A
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨fun i => (invertCoordinates mask x i).property,x,hx,?_⟩
    rw [← vfValues_invertCoordinates,invertCoordinates_involutive]
  · rintro ⟨hs,a,ha,he⟩
    let x : Fin n → VF M := fun i => ⟨z i,hs i⟩
    have hxa : invertCoordinates mask x = a := by
      apply vfValues_injective
      rw [vfValues_invertCoordinates]
      exact he.symm
    refine ⟨x,⟨a,ha,?_⟩,rfl⟩
    rw [← hxa,invertCoordinates_involutive]

private noncomputable def rawOutputInvert (mask : Fin n → Bool)
    (z : Fin k ⊕ Fin n → M) : Fin k ⊕ Fin n → M :=
  Sum.elim (z ∘ Sum.inl) (rawInvertCoordinates mask (z ∘ Sum.inr))

private theorem rawOutputInvert_definable (S : Set M) (mask : Fin n → Bool) :
    S.DefinableMap LRV (rawOutputInvert (k := k) mask) := by
  intro j
  cases j with
  | inl i => exact Set.DefinableFun.proj LRV
  | inr i =>
    cases h : mask i with
    | false => simpa only [rawOutputInvert,Sum.elim_inr,rawInvertCoordinates,h,
        Bool.false_eq_true,ite_false,Function.comp_apply] using
        (Set.DefinableFun.proj LRV (i := (Sum.inr i : Fin k ⊕ Fin n)))
    | true => simpa only [rawOutputInvert,Sum.elim_inr,rawInvertCoordinates,h,
        ite_true,Function.comp_apply] using rawVFInverse_definable S (Sum.inr i : Fin k ⊕ Fin n)

theorem invertCoordinates_correspondence_definable {S : Set M} (mask : Fin n → Bool)
    (U : Set (Fin k → VF M)) (F : (Fin k → VF M) → Set (Fin n → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph U F)) :
    S.Definable LRV (vfCorrespondenceGraph U (fun c => invertCoordinates mask '' F c)) := by
  have h := ((vfRawUniverse_definable S n).preimage_comp (Sum.inr : Fin n → Fin k ⊕ Fin n)).inter
    (hF.preimage_map (rawOutputInvert_definable S mask))
  convert h using 1
  ext z
  change (∃ a ∈ U, ∃ y ∈ invertCoordinates mask '' F a, Sum.elim (vfValues a) (vfValues y) = z) ↔
    (∀ i, iVF (z (.inr i))) ∧ rawOutputInvert mask z ∈ vfCorrespondenceGraph U F
  constructor
  · rintro ⟨a,ha,_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨fun i => (invertCoordinates mask x i).property,a,ha,x,hx,?_⟩
    have hi : rawInvertCoordinates mask (vfValues (invertCoordinates mask x)) = vfValues x := by
      rw [← vfValues_invertCoordinates,invertCoordinates_involutive]
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (congrFun hi i).symm
  · rintro ⟨hs,a,ha,x,hx,he⟩
    let y : Fin n → VF M := fun i => ⟨z (.inr i),hs i⟩
    have hxy : x = invertCoordinates mask y := by
      apply vfValues_injective
      rw [vfValues_invertCoordinates]
      exact funext (fun i => congrFun he (.inr i))
    refine ⟨a,ha,y,⟨x,hx,?_⟩,?_⟩
    · rw [hxy,invertCoordinates_involutive]
    · funext i
      cases i with
      | inl i => exact congrFun he (.inl i)
      | inr i => rfl

end DiamondIntegral.Section2
