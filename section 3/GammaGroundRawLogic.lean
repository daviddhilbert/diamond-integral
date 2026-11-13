import «section 3».RawTupleSpace

/-! Formula operations with the original Gamma parameters retained.
Real tuple quantifiers range over all of the released universe. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def GammaGroundRawDefinable (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) {ι : Type} [Finite ι] (A : Set (ι → M)) : Prop :=
  GammaGroundDefinable hc ground (rawTupleSpace LRV M ι) A

def rawTupleProjectionMap {ι η : Type} [Finite ι] [Finite η] (S : Set M) (f : ι → η) :
    Map (DefSet.univ (rawTupleSpace LRV M η) S) (DefSet.univ (rawTupleSpace LRV M ι) S) :=
  Map.ofCodes _ (fun z => z ∘ f) (fun z => z ∘ f)
    (fun _ => Set.DefinableFun.proj LRV) (fun _ => Set.mem_univ _) (fun _ => rfl)

namespace GammaGroundRawDefinable
variable {ι η : Type} [Finite ι] [Finite η] {A B : Set (ι → M)}

theorem of_real (hA : ground.real.Definable LRV A) : GammaGroundRawDefinable hc ground A :=
  GammaGroundDefinable.of_real (rawTupleSpace_definable_iff.mpr hA)

theorem inter (hA : GammaGroundRawDefinable hc ground A) (hB : GammaGroundRawDefinable hc ground B) :
    GammaGroundRawDefinable hc ground (A ∩ B) := GammaGroundDefinable.inter hA hB

theorem union (hA : GammaGroundRawDefinable hc ground A) (hB : GammaGroundRawDefinable hc ground B) :
    GammaGroundRawDefinable hc ground (A ∪ B) := GammaGroundDefinable.union hA hB

theorem compl (hA : GammaGroundRawDefinable hc ground A) :
    GammaGroundRawDefinable hc ground Aᶜ := GammaGroundDefinable.compl hA

theorem congr (hA : GammaGroundRawDefinable hc ground A) (h : ∀ z, z ∈ A ↔ z ∈ B) :
    GammaGroundRawDefinable hc ground B := GammaGroundDefinable.congr hA h

theorem himp (hA : GammaGroundRawDefinable hc ground A) (hB : GammaGroundRawDefinable hc ground B) :
    GammaGroundRawDefinable hc ground {z | z ∈ A → z ∈ B} := by
  classical
  exact (hA.compl.union hB).congr (fun _ => by simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]; tauto)

theorem preimage_comp (hA : GammaGroundRawDefinable hc ground A) (f : ι → η) :
    GammaGroundRawDefinable hc ground {z : η → M | z ∘ f ∈ A} :=
  GammaGroundDefinable.preimage hA (rawTupleProjectionMap ground.real f)

theorem image_comp {D : Set (η → M)} (hD : GammaGroundRawDefinable hc ground D) (f : ι → η) :
    GammaGroundRawDefinable hc ground ((fun z => z ∘ f) '' D) := by
  apply (GammaGroundDefinable.image hD (rawTupleProjectionMap ground.real f)).congr
  intro z
  rfl

theorem exists_of_finite {D : Set ((ι ⊕ η) → M)} (hD : GammaGroundRawDefinable hc ground D) :
    GammaGroundRawDefinable hc ground {z : ι → M | ∃ w : η → M, Sum.elim z w ∈ D} := by
  apply (hD.image_comp (Sum.inl : ι → ι ⊕ η)).congr
  intro z
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u ∘ Sum.inr, ?_⟩
    convert hu using 1
    congr 1
    funext i
    cases i <;> rfl
  · rintro ⟨w, hw⟩
    exact ⟨Sum.elim z w, hw, rfl⟩

theorem forall_of_finite {D : Set ((ι ⊕ η) → M)} (hD : GammaGroundRawDefinable hc ground D) :
    GammaGroundRawDefinable hc ground {z : ι → M | ∀ w : η → M, Sum.elim z w ∈ D} := by
  classical
  exact hD.compl.exists_of_finite.compl.congr (fun _ => by simp)

theorem iInter {J : Type} [Finite J] {D : J → Set (ι → M)}
    (hD : ∀ j, GammaGroundRawDefinable hc ground (D j)) :
    GammaGroundRawDefinable hc ground (⋂ j, D j) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  have h : ∀ t : Finset J, GammaGroundRawDefinable hc ground {z | ∀ j ∈ t, z ∈ D j} := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Set.setOf_true]
        using (of_real (hc := hc) (ground := ground) (Set.definable_univ (α := ι)))
    | @insert j t hj ih =>
      apply ((hD j).inter ih).congr
      intro z
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp]
  convert h Finset.univ using 1
  ext z
  simp

theorem iUnion {J : Type} [Finite J] {D : J → Set (ι → M)}
    (hD : ∀ j, GammaGroundRawDefinable hc ground (D j)) :
    GammaGroundRawDefinable hc ground (⋃ j, D j) := by
  classical
  exact (iInter (fun j => (hD j).compl)).compl.congr (fun _ => by simp)

end GammaGroundRawDefinable

theorem GammaGroundDefinable.on_real_codes {Q : Space LRV M} {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc ground Q A) : GammaGroundRawDefinable hc ground (Q.preimage A) := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  exact ⟨k, γ, hγ, hA.on_real_codes⟩

end DiamondIntegral.Section3
