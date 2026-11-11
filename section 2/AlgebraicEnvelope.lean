import «section 2».Henselianity
import Section6.HenselianValuationRing
import Section6.HenselianInvariance
import Section6.HenselianRVClosure
import Section6.CanonicalEmbedding
import Section3.CanonicalContext

/-! The algebraic-envelope step in the reverse implication of Lemma 2.11. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section6

namespace DiamondIntegral.Section2

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

omit hM in
private theorem vf_substructure (C : LRV.Substructure M) (a : C) :
    iVF a ↔ iVF a.val := by
  change Structure.RelMap (L := LRV) Rel.memVF (fun i => (![a] i).val) ↔
    Structure.RelMap (L := LRV) Rel.memVF ![a.val]
  have he : (fun i : Fin 1 => (![a] i).val) = ![a.val] := by
    funext i
    fin_cases i
    rfl
  rw [he]

omit hM in
private theorem rv_substructure (C : LRV.Substructure M) (a : C) :
    iRV a ↔ iRV a.val := by
  change Structure.RelMap (L := LRV) Rel.memRV (fun i => (![a] i).val) ↔
    Structure.RelMap (L := LRV) Rel.memRV ![a.val]
  have he : (fun i : Fin 1 => (![a] i).val) = ![a.val] := by
    funext i
    fin_cases i
    rfl
  rw [he]

private theorem canonical_elementarySubstructure (hc : CanonicalStructure.IsCanonical (M := M))
    (C : LRV.ElementarySubstructure M) : CanonicalStructure.IsCanonical (M := C) := by
  have hC := (C.theory_model_iff CanonicalTheory.CanonicalACVF).mpr
    (CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨hM, hc⟩)
  exact (CanonicalTheory.model_CanonicalACVF_iff.mp hC).2

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)

include hv in
/-- The reverse implication of Lemma 2.11 on the canonical totalization.
The algebraic envelope, its Galois property, and valuation invariance are
constructed in the proof, rather than assumed as extra paper hypotheses. -/
theorem definableClosure_eq_of_henselian_canonical
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ a : B.field, a ≠ 0 ∧ v a.val ≠ 1)
    (hH : HenselianLocalRing (v.comap B.field.subtype).valuationSubring) :
    definableClosure (S : Set M) = (S : Set M) := by
  classical
  let K := B.field
  let A := vfFieldNames K
  have hA : ∀ x ∈ A, iVF x := by
    rintro _ ⟨a, _, rfl⟩
    exact a.property
  have hKmem (a : VF M) : a ∈ K ↔ a.val ∈ A := by
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, he⟩
      exact (Subtype.ext he : b = a) ▸ hb
  have hntA : ∃ a : vfAlgebraicClosureField A, a ≠ 0 ∧ v a.val ≠ 1 := by
    obtain ⟨a, ha0, hav⟩ := hnt
    have ha : a.val ∈ vfAlgebraicClosureField A :=
      (mem_vfAlgebraicClosureField A a.val).mpr
        (definableClosureAt_of_mem (σ := .vf)
          ((hKmem _).mp a.property) a.val.property).algebraic
    refine ⟨⟨a.val, ha⟩, ?_, hav⟩
    intro he
    exact ha0 (Subtype.ext (congrArg (fun x : vfAlgebraicClosureField A => x.val) he))
  let C : LRV.ElementarySubstructure M :=
    ⟨algebraicClosureSubstructure hc A,
      canonical_algebraicClosureSubstructure_elementary v hv hc h00 A hA hntA⟩
  letI : C ⊨ Axioms.ACVF := (C.theory_model_iff _).mpr hM
  have h00C : C ⊨ Axioms.ACVF00 := (C.theory_model_iff _).mpr h00
  have hcC : CanonicalStructure.IsCanonical (M := C) :=
    canonical_elementarySubstructure hc C
  let ι : VF C →+* VF M :=
    { toFun := fun a => ⟨a.val.val, (vf_substructure C.toSubstructure a.val).mp a.property⟩
      map_zero' := by
        apply Subtype.ext
        change Structure.funMap (L := LRV) Fn.vfZero _ =
          Structure.funMap (L := LRV) Fn.vfZero _
        congr 1
        funext i
        exact i.elim0
      map_one' := by
        apply Subtype.ext
        change Structure.funMap (L := LRV) Fn.vfOne _ =
          Structure.funMap (L := LRV) Fn.vfOne _
        congr 1
        funext i
        exact i.elim0
      map_add' := by
        intro a b
        apply Subtype.ext
        change Structure.funMap (L := LRV) Fn.vfAdd _ =
          Structure.funMap (L := LRV) Fn.vfAdd _
        congr 1
        funext i
        fin_cases i <;> rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        change Structure.funMap (L := LRV) Fn.vfMul _ =
          Structure.funMap (L := LRV) Fn.vfMul _
        congr 1
        funext i
        fin_cases i <;> rfl }
  let w := v.comap ι
  have hRv (a : VF C) : (iRv a.val).val = iRv (ι a).val := by
    change Structure.funMap (L := LRV) Fn.rvMap _ =
      Structure.funMap (L := LRV) Fn.rvMap _
    congr 1
    funext i
    fin_cases i
    rfl
  have hw (a b : VF C) : VFValued.predV a b ↔ w a ≤ w b := by
    have hp : VFValued.predV a b ↔ VFValued.predV (ι a) (ι b) := by
      change Structure.RelMap (L := LRV) Rel.rvLe
        (fun i => (![iRv b.val, iRv a.val] i).val) ↔
        Structure.RelMap (L := LRV) Rel.rvLe ![iRv (ι b).val, iRv (ι a).val]
      have he : (fun i : Fin 2 => (![iRv b.val, iRv a.val] i).val) =
          ![iRv (ι b).val, iRv (ι a).val] := by
        funext i
        fin_cases i
        · exact hRv b
        · exact hRv a
      rw [he]
    exact hp.trans (hv (ι a) (ι b))
  have hSC : (S : Set M) ⊆ (C : Set M) := by
    intro x hx
    obtain ⟨σ, hd⟩ := B.definable_over_fieldNames x hx
    exact ⟨σ, hd.algebraic⟩
  let Y : LRV.Substructure C := S.comap C.subtype.toHom
  let L := K.comap ι
  have hL (a : VF C) : a ∈ L ↔ a.val ∈ Y := B.mem_iff (ι a)
  let lift (a : K) : VF C :=
    ⟨⟨a.val.val, subset_algebraicClosureSet A ((hKmem _).mp a.property)⟩,
      (vf_substructure C.toSubstructure _).mpr a.val.property⟩
  have hlift (a : K) : ι (lift a) = a.val := rfl
  let k : L →+* K :=
    { toFun := fun a => ⟨ι a.val, a.property⟩
      map_zero' := Subtype.ext (map_zero ι)
      map_one' := Subtype.ext (map_one ι)
      map_add' := fun a b => Subtype.ext (map_add ι a.val b.val)
      map_mul' := fun a b => Subtype.ext (map_mul ι a.val b.val) }
  have hk : Function.Bijective k := by
    constructor
    · intro a b he
      exact Subtype.ext (ι.injective (congrArg Subtype.val he))
    · intro a
      exact ⟨⟨lift a, a.property⟩, rfl⟩
  let e : L ≃+* K := RingEquiv.ofBijective k hk
  letI : CharZero (VF C) := charZero_of_inj_zero (fun n hn => by
    by_contra hn0
    exact Barycentre.natCast_ne_zero h00C n hn0 hn)
  letI : IsAlgClosed (VF C) := VFAlgClosed.isAlgClosed_vfType
  letI : Algebra.IsAlgebraic L (VF C) := ⟨fun a => by
    have ha : AlgebraicAt A .vf (ι a).val := by
      obtain ⟨σ, ha⟩ := a.val.property
      cases σ with
      | vf => exact ha
      | rv => exact (TypedModelMap.not_rv_of_vf (ι a).property ha.sorted).elim
    have halg : IsAlgebraic K (ι a) :=
      (VFFieldBase.algebraicAt_iff A ⟨K, hKmem⟩ (ι a)).mp ha
    exact halg.of_ringHom_of_comp_eq e.toRingHom ι e.surjective ι.injective
      (by ext x; rfl)⟩
  letI : IsAlgClosure L (VF C) :=
    { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  letI : IsGalois L (VF C) := inferInstance
  have hH' : HenselianLocalRing (w.comap L.subtype).valuationSubring := by
    letI := hH
    apply HenselianTheory.henselian_of_compatible_equiv
      (v.comap K.subtype) (w.comap L.subtype) e.symm
    intro a b
    change v (ι (e.symm a).val) ≤ v (ι (e.symm b).val) ↔ v a.val ≤ v b.val
    rw [show ι (e.symm a).val = a.val from congrArg Subtype.val (e.apply_symm_apply a),
      show ι (e.symm b).val = b.val from congrArg Subtype.val (e.apply_symm_apply b)]
  have hsep (n m : ℕ) (hne : n ≠ m) : w ((n : VF C) - (m : VF C)) = 1 := by
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · rw [← Valuation.map_neg w ((n : VF C) - (m : VF C)), neg_sub,
        ← Nat.cast_sub hnm.le]
      exact Barycentre.natCast_value_one w hw h00C (m - n) (Nat.sub_ne_zero_of_lt hnm)
    · rw [← Nat.cast_sub hmn.le]
      exact Barycentre.natCast_value_one w hw h00C (n - m) (Nat.sub_ne_zero_of_lt hmn)
  have hEP : HenselianAutomorphismInvariance w L := by
    intro hH''
    letI := hH''
    exact henselian_automorphism_invariance w hsep
  have hRV (t : C) (ht : t ∈ Y) (htRV : iRV t) :
      ∃ a : L, iRv a.val.val = t := by
    obtain ⟨a, ha⟩ := B.rv_lift t.val ht
      ((rv_substructure C.toSubstructure t).mp htRV)
    refine ⟨⟨lift a, a.property⟩, ?_⟩
    apply Subtype.ext
    exact (hRv (lift a)).trans ha
  have hrv (a : VF C) (ha : a.val ∈ Y) : iRv a.val ∈ Y :=
    Y.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact ha)
  have hYC : NormalizedDclClosed (Y : Set C) :=
    @dclClosed_of_functionallyClosed LRV C (CanonicalStructure.normalize (M := C))
      (Y : Set C)
      (@lemma_6_2_in_algebraic_envelope_pure C inferInstance inferInstance Γ inferInstance
        w hw h00C L inferInstance (Y : Set C) hL hRV hrv hH' hEP)
  let j := CanonicalEmbedding.normalized hcC hc C.subtype
  have himage : j '' (Y : Set C) = (S : Set M) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, hSC hx⟩, hx, rfl⟩
  have hclosed : NormalizedDclClosed (S : Set M) := by
    rw [← himage]
    exact @DclClosed.image LRV C M (CanonicalStructure.normalize (M := C))
      (CanonicalStructure.normalize (M := M)) (Y : Set C) hYC j
  apply Set.Subset.antisymm
  · rintro x ⟨σ, hx⟩
    exact hclosed x ((definableAt_iff_normalized_raw (S : Set M) σ {x}).mp hx).1
  · exact subset_definableClosure _

include hv in
/-- Lemma 2.11 (`cut:to:hensel:substru`) in the canonical encoding of the
two-sorted language. `B` records the standing VF-field convention and the
RV representatives of the VF-generated base. -/
theorem lemma_2_11
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ a : B.field, a ≠ 0 ∧ v a.val ≠ 1) :
    definableClosure (S : Set M) = (S : Set M) ↔
      HenselianLocalRing (v.comap B.field.subtype).valuationSubring :=
  ⟨henselian_of_definableClosure_eq v hv (S : Set M) B.toVFFieldBase,
    definableClosure_eq_of_henselian_canonical v hv hc h00 S B hnt⟩

end DiamondIntegral.Section2
