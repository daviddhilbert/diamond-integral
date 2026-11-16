import «section 6».TotalFibrewiseContinuity

/-! Canonical first-coordinate discontinuity sets in RV-parameter
families. The complete projection graph remains over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem rvFunctionFamily_section_definable
    (F : (Fin r ⊕ Fin n → M) → M) (hF : S.DefinableFun LRV F)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin 1 → VF M)
    (hAt : ∀ u a, F (Sum.elim (rvValues u) (vfValues a)) = (f u a 0).val)
    (u : Fin r → RVInfinity M) :
    (S ∪ Set.range (rvValues u)).Definable LRV (vfGraph (f u)) := by
  let T := S ∪ Set.range (rvValues u)
  let arg (w : Fin n ⊕ Fin 1 → M) : Fin r ⊕ (Fin n ⊕ Fin 1) → M := Sum.elim (rvValues u) w
  have harg : T.DefinableMap LRV arg := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have h := ((rvFunctionFamilyGraph_definable F hF).mono Set.subset_union_left).preimage_map harg
  change T.Definable LRV {w | Sum.elim (rvValues u) w ∈ rvFunctionFamilyGraph F} at h
  rwa [rvFunctionFamilyGraph_section F f hAt u] at h

def rvFunctionFamilyBaseIndex : Fin r ⊕ Fin 1 → Fin r ⊕ Fin (n+1) :=
  Sum.elim Sum.inl (fun _ => .inr 0)

def rvFunctionFamilyBadBases (F : (Fin r ⊕ Fin (n+1) → M) → M) : Set (Fin r ⊕ Fin 1 → M) :=
  (fun z => z ∘ rvFunctionFamilyBaseIndex) '' rvFunctionFamilyBadInputs F

theorem rvFunctionFamilyBadBases_definable (F : (Fin r ⊕ Fin (n+1) → M) → M)
    (hF : S.DefinableFun LRV F) : S.Definable LRV (rvFunctionFamilyBadBases F) :=
  (rvFunctionFamilyBadInputs_definable F hF).image_comp rvFunctionFamilyBaseIndex

theorem rvFunctionFamilyBadBases_sorted (F : (Fin r ⊕ Fin (n+1) → M) → M)
    (t : Fin r → M) (a : Fin 1 → M) (ha : Sum.elim t a ∈ rvFunctionFamilyBadBases F) :
    (∀ i, iRV (t i)) ∧ ∀ i, iVF (a i) := by
  obtain ⟨w,⟨hsort,_⟩,he⟩ := ha
  refine ⟨fun i => ?_,fun i => ?_⟩
  · have hi : w (.inl i) = t i := congrFun he (.inl i)
    rw [← hi]
    exact hsort.1 i
  · have hi : w (.inr 0) = a i := congrFun he (.inr i)
    rw [← hi]
    exact hsort.2 0

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem rvFunctionFamilyBadBases_at
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : (Fin r ⊕ Fin (n+1) → M) → M)
    (f : (Fin r → RVInfinity M) → (Fin (n+1) → VF M) → Fin 1 → VF M)
    (hAt : ∀ u x, F (Sum.elim (rvValues u) (vfValues x)) = (f u x 0).val)
    (u : Fin r → RVInfinity M) (a : Fin 1 → VF M) :
    Sum.elim (rvValues u) (vfValues a) ∈ rvFunctionFamilyBadBases F ↔ a ∈ firstCoordinateDiscontinuities (f u) := by
  constructor
  · rintro ⟨w,hw,he⟩
    let x : Fin (n+1) → VF M := fun i => ⟨w (.inr i),hw.1.2 i⟩
    have hprefix (i : Fin r) : w (.inl i) = (u i).val := congrFun he (.inl i)
    have hcode : w = Sum.elim (rvValues u) (vfValues x) := by
      funext i
      cases i with
      | inl i => exact hprefix i
      | inr i => rfl
    have hbad : ¬ ContinuousAt (f u) x := by
      rw [hcode] at hw
      exact (rvFunctionFamilyBadInputs_at hv F f hAt u x).mp hw
    exact ⟨x,Subtype.ext (congrFun he (.inr 0)),hbad⟩
  · rintro ⟨x,hxa,hbad⟩
    refine ⟨Sum.elim (rvValues u) (vfValues x),(rvFunctionFamilyBadInputs_at hv F f hAt u x).mpr hbad,?_⟩
    funext i
    cases i with
    | inl i => rfl
    | inr i => fin_cases i; exact congrArg Subtype.val hxa

end DiamondIntegral.Section6
