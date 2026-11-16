import «section 6».RVFamilyContinuityBases
import Section3.FiniteImage

/-! Uniform fiberwise continuity over every existing RV label. The
canonical first-coordinate bad sets are finite in each label fiber;
the checked RV-to-VF finite-image theorem makes their original-base
definable union finite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_uniform_rv_fibrewise_continuity_exception
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : (Fin r ⊕ Fin (n+1) → M) → M) (hF : S.DefinableFun LRV F)
    (f : (Fin r → RVInfinity M) → (Fin (n+1) → VF M) → Fin 1 → VF M)
    (hAt : ∀ u x, F (Sum.elim (rvValues u) (vfValues x)) = (f u x 0).val)
    (hFibres : ∀ u (a : VF M), Continuous (fun b : Fin n → VF M => f u (Fin.cons a b))) :
    ∃ E : Set (Fin 1 → VF M), E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      ∀ u, ContinuousOn (f u) {x | (fun _ : Fin 1 => x 0) ∉ E} := by
  let H := rvFunctionFamilyBadBases F
  have hH : S.Definable LRV H := rvFunctionFamilyBadBases_definable F hF
  have hSort (t : Fin r → M) (y : Fin 1 → M) (hy : Sum.elim t y ∈ H) :
      (∀ i, iRV (t i)) ∧ ∀ i, iVF (y i) := rvFunctionFamilyBadBases_sorted F t y hy
  have hRows (t : Fin r → M) : {y : Fin 1 → M | Sum.elim t y ∈ H}.Finite := by
    by_cases ht : ∀ i, iRV (t i)
    · let u : Fin r → RVInfinity M := fun i => ⟨t i,ht i⟩
      have hSmallU : Cardinal.mk ↥(S ∪ Set.range (rvValues u)) < κ :=
        small_union_range hκ.le S hsmall (rvValues u)
      have hFinite := firstCoordinateDiscontinuities_finite h00 hc hκ hs hSmallU hv
        (f u) (rvFunctionFamily_section_definable F hF f hAt u) (hFibres u)
      apply (hFinite.image vfValues).subset
      intro y hy
      let a : Fin 1 → VF M := fun i => ⟨y i,(hSort t y hy).2 i⟩
      refine ⟨a,?_,rfl⟩
      exact (rvFunctionFamilyBadBases_at hv F f hAt u a).mp hy
    · apply (Set.finite_empty : (∅ : Set (Fin 1 → M)).Finite).subset
      intro y hy
      exact False.elim (ht (hSort t y hy).1)
  let RawE : Set (Fin 1 → M) := {y | ∃ t : Fin r → M, Sum.elim t y ∈ H}
  have hRawFinite : RawE.Finite := finite_rv_to_vf_tuple_relation_image hc hs S hsmall H hH hSort hRows
  have hRawDef : S.Definable LRV RawE := by
    convert hH.image_comp (Sum.inr : Fin 1 → Fin r ⊕ Fin 1) using 1
    ext y
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨Sum.elim t y,ht,rfl⟩
    · rintro ⟨w,hw,he⟩
      refine ⟨w ∘ Sum.inl,?_⟩
      have hw' : Sum.elim (w ∘ Sum.inl) y = w := by
        funext i
        cases i with
        | inl i => rfl
        | inr i => exact (congrFun he i).symm
      rw [hw']
      exact hw
  let E : Set (Fin 1 → VF M) := {a | vfValues a ∈ RawE}
  have hEF : E.Finite := hRawFinite.preimage vfValues_injective.injOn
  have hCodes : vfValues '' E = RawE := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · rintro ⟨t,hy⟩
      let a : Fin 1 → VF M := fun i => ⟨y i,(hSort t y hy).2 i⟩
      exact ⟨a,⟨t,hy⟩,rfl⟩
  refine ⟨E,hEF,hCodes.symm ▸ hRawDef,fun u x hx => ?_⟩
  have hcont : ContinuousAt (f u) x := by
    by_contra hn
    apply hx
    refine ⟨rvValues u,?_⟩
    exact (rvFunctionFamilyBadBases_at hv F f hAt u (fun _ : Fin 1 => x 0)).mpr ⟨x,rfl,hn⟩
  exact hcont.continuousWithinAt

end DiamondIntegral.Section6
