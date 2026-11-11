import «section 2».FinitaryGeneric
import «section 2».LimitGerms

/-!
# Lemma 2.44: almost-everywhere continuity of finite correspondences

The finite uniform RV codes, the same-base exceptional locus and every
inverse branch are constructed in the preceding modules. This assembles
the actual minimal-limit conclusion, including empty fibres. Source arity
is positive, exactly as approved in the manuscript.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FinitaryRVCode.minimalLimit_of_good (S : Set M)
    (A : Set (Fin n → VF M)) (F : (Fin n → VF M) → Set (Fin m → VF M))
    (C : FinitaryRVCode S A F)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (a : Fin n → VF M) (ha : a ∈ A) (hfin : (F a).Finite)
    (hgood : vfValues a ∉ C.badRaw) : HasMinimalLimitSet A a F (F a) := by
  classical
  have hg := not_or.mp (fun h => hgood ((C.mem_badRaw hv a).mpr h))
  have hloc : rvLocallyConstantAt (rvFibre C.labelGraph) a := not_not.mp hg.1
  have hcont (t : Fin C.arity → RVInfinity M) : ContinuousAt (C.branch (rvValues t)) a := by
    by_contra h
    exact hg.2 ⟨rvValues t, fun i => (t i).property, h⟩
  obtain ⟨U, hU, haU, hlabel⟩ := hloc
  let T := rvFibre C.labelGraph a
  have hT : T.Finite := by
    change (rvFibre C.labelGraph a).Finite
    rw [C.labelFibre_eq_image a ha]
    exact hfin.image _
  by_cases hTempty : T = ∅
  · have haempty : F a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have ht : C.typedCode a y ∈ T := by
        change C.typedCode a y ∈ rvFibre C.labelGraph a
        rw [C.labelFibre_eq_image a ha]
        exact Set.mem_image_of_mem _ hy
      rw [hTempty] at ht
      exact ht
    rw [haempty]
    refine ⟨?_, fun K hK _ => hK.ne (Set.eq_empty_iff_forall_notMem.mpr
      (fun _ hy => hK.1 hy))⟩
    intro ε
    obtain ⟨δ, hδ⟩ := exists_vfBall_subset_nhds hv a (hU.mem_nhds haU)
    refine ⟨δ, fun x hx hnear y hy => ?_⟩
    have ht : C.typedCode x y ∈ rvFibre C.labelGraph x := by
      rw [C.labelFibre_eq_image x hx.1]
      exact Set.mem_image_of_mem _ hy
    rw [hlabel x (hδ hnear)] at ht
    change C.typedCode x y ∈ T at ht
    rw [hTempty] at ht
    exact ht.elim
  · obtain ⟨t₀, ht₀⟩ := Set.nonempty_iff_ne_empty.mpr hTempty
    have hUA : U ⊆ A := by
      intro x hx
      have ht : t₀ ∈ rvFibre C.labelGraph x := (hlabel x hx).symm ▸ ht₀
      exact ((C.mem_labelGraph x (rvValues t₀)).mp ht).1
    let : Fintype T := hT.fintype
    let branches : T → (Fin n → VF M) → Fin m → VF M := fun t => C.branch (rvValues t.val)
    have hrep (x : Fin n → VF M) (hx : x ∈ U) :
        F x = Set.range (fun t : T => branches t x) := by
      ext y
      constructor
      · intro hy
        let t := C.typedCode x y
        have ht : t ∈ T := by
          change t ∈ rvFibre C.labelGraph a
          rw [← hlabel x hx, C.labelFibre_eq_image x (hUA hx)]
          exact Set.mem_image_of_mem _ hy
        refine ⟨⟨t, ht⟩, ?_⟩
        exact C.branch_eq_of_hasValue ⟨hUA hx, hy, rfl⟩
      · rintro ⟨t, rfl⟩
        have ht : t.val ∈ rvFibre C.labelGraph x := (hlabel x hx).symm ▸ t.property
        obtain ⟨hxA, y, hy, hcode⟩ := (C.mem_labelGraph x (rvValues t.val)).mp ht
        exact (C.hasValue_branch ⟨y, hxA, hy, hcode⟩).2.1
    have hbranches := finite_continuous_branches_minimal_limit hv hn A a
      (Filter.mem_of_superset (hU.mem_nhds haU) hUA) branches (fun t => hcont t.val)
    have heq : (fun x => Set.range (fun t : T => branches t x)) =ᶠ[𝓝 a] F := by
      filter_upwards [hU.mem_nhds haU] with x hx
      exact (hrep x hx).symm
    rw [← hrep a haU] at hbranches
    exact (hasMinimalLimitSet_iff_of_eventuallyEq hv heq).mp hbranches

/-- Lemma 2.44 in the real-base canonical presentation. The lower-dimensional
exception is a definable subset of the original domain, and continuity is
the paper's actual punctured minimal-limit condition for all values.
No choice, branch-continuity or dimension principle is an additional premise.
The conclusion also covers lower-dimensional domains, where all of A may
be exceptional, so the paper's full-dimension premise is unnecessary here. -/
theorem lemma_2_44
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (F : (Fin n → VF M) → Set (Fin m → VF M))
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) (hfin : ∀ a ∈ A, (F a).Finite) :
    ∃ E ⊆ A, S.Definable LRV (vfValues '' E) ∧
      vfDimension (E ×ˢ (Set.univ : Set (Fin 0 → RVInfinity M))) < (n : WithBot ℕ) ∧
      ∀ a ∈ A \ E, HasMinimalLimitSet A a F (F a) := by
  obtain ⟨C⟩ := exists_finitaryRVCode h00 hs hsmall A F hG hfin
  let R := (vfValues '' A) ∩ C.badRaw
  have hR : S.Definable LRV R := hA.inter (C.badRaw_definable hG)
  let E := {a ∈ A | vfValues a ∈ C.badRaw}
  have he : vfValues '' E = R := by
    ext z
    constructor
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hb⟩
    · rintro ⟨⟨a, ha, rfl⟩, hb⟩
      exact ⟨a, ⟨ha, hb⟩, rfl⟩
  refine ⟨E, fun _ h => h.1, he.symm ▸ hR, ?_, ?_⟩
  · have hd := vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn hR
      (fun a ha hind => C.not_mem_badRaw_of_independent hc hκ hs hsmall hv hG a hind ha.2)
    have hcarrier : (vfObjectOfRaw hR).carrier =
        E ×ˢ (Set.univ : Set (Fin 0 → RVInfinity M)) := by
      ext p
      constructor
      · rintro ⟨⟨a, ha, hea⟩, hb⟩
        have hap : a = p.1 := vfValues_injective hea
        exact ⟨⟨hap ▸ ha, hb⟩, Set.mem_univ _⟩
      · rintro ⟨⟨ha, hb⟩, _⟩
        exact ⟨⟨p.1, ha, rfl⟩, hb⟩
    rw [← hcarrier]
    exact vfDimension_lt_of_companion_lt hc hs hsmall _ (rawRVSpace_rvCoded 1) hv _ hd
  · intro a ⟨ha, hbad⟩
    exact C.minimalLimit_of_good S A F hv hn a ha (hfin a ha) (fun h => hbad ⟨ha, h⟩)

end DiamondIntegral.Section2
