import «section 4».GammaTupleSingletonProfiles

/-! Finite Gamma domains can be indexed by finite sets of tuples of
original-base Gamma names. These tuples contain no RV representatives. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaNameTuples
open GammaOrderLogic GammaDefinableMaps GammaNamesSubgroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev NameTuple (B : Base (M := M)) (n : ℕ) := Fin n → namesSubgroup B

def values {B : Base (M := M)} {n : ℕ} (α : NameTuple B n) : Fin n → Values.Gamma (M := M) := fun i => (α i).val

theorem values_injective (B : Base (M := M)) (n : ℕ) : Function.Injective (values (B := B) (n := n)) := by
  intro α β h
  funext i
  exact Subtype.ext (congrFun h i)

theorem singleton_definable {B : Base (M := M)} {n : ℕ} (α : NameTuple B n) :
    GammaDefinable B ({values α} : Set (Fin n → Values.Gamma (M := M))) :=
  GammaTupleSingletonProfiles.singleton_definable B (values α) (fun i => (α i).property)

def namedSupport (B : Base (M := M)) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) : Set (NameTuple B n) :=
  values ⁻¹' I

theorem namedSupport_finite (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hi : I.Finite) : (namedSupport B I).Finite :=
  Set.Finite.preimage (values_injective B n).injOn hi

theorem namedSupport_image (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hi : I.Finite) :
    values '' namedSupport B I = I := by
  apply Set.Subset.antisymm
  · rintro z ⟨α, hα, rfl⟩
    exact hα
  · intro z hz
    let α : NameTuple B n := fun i => ⟨z i, GammaFiniteNames.finite_coordinate_definable B I hI hi z hz i⟩
    exact ⟨α, hz, rfl⟩

def support {B : Base (M := M)} {n : ℕ} (s : Finset (NameTuple B n)) : Set (Fin n → Values.Gamma (M := M)) :=
  values '' (s : Set (NameTuple B n))

theorem support_definable {B : Base (M := M)} {n : ℕ} (s : Finset (NameTuple B n)) : GammaDefinable B (support s) := by
  have h := GammaQuantifierLogic.finite_iUnion_definable_base B
    (fun α : s => ({values α.val} : Set (Fin n → Values.Gamma (M := M)))) (fun α => singleton_definable α.val)
  convert h using 1
  ext z
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨α, hα⟩, rfl⟩
  · intro hz
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp hz
    exact ⟨α.val, α.property, hα.symm⟩

theorem finite_support_representation (B : Base (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hi : I.Finite) :
    ∃ s : Finset (NameTuple B n), support s = I := by
  refine ⟨(namedSupport_finite B I hi).toFinset, ?_⟩
  change values '' ((namedSupport_finite B I hi).toFinset : Set (NameTuple B n)) = I
  rw [(namedSupport_finite B I hi).coe_toFinset]
  exact namedSupport_image B I hI hi

theorem support_empty (B : Base (M := M)) (n : ℕ) : support (∅ : Finset (NameTuple B n)) = ∅ := by simp [support]

theorem support_insert {B : Base (M := M)} {n : ℕ} (α : NameTuple B n) (s : Finset (NameTuple B n)) :
    support (insert α s) = {values α} ∪ support s := by
  simp only [support, Finset.coe_insert, Set.image_insert_eq, Set.singleton_union]

theorem values_not_mem_support {B : Base (M := M)} {n : ℕ} {α : NameTuple B n} {s : Finset (NameTuple B n)}
    (hα : α ∉ s) : values α ∉ support s := by
  rintro ⟨β, hβ, he⟩
  have hβα : β = α := values_injective B n he
  subst β
  exact hα hβ

theorem singleton_inter_support {B : Base (M := M)} {n : ℕ} {α : NameTuple B n} {s : Finset (NameTuple B n)}
    (hα : α ∉ s) : ({values α} : Set (Fin n → Values.Gamma (M := M))) ∩ support s = ∅ :=
  Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_singleton_left.mpr (values_not_mem_support hα))

theorem scalar_value_definable {B : Base (M := M)} {n : ℕ} (α : NameTuple B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f) :
    GammaDefinableClosureAtBase B (f (values α)) :=
  GammaFiniteNames.finite_value_definable B {values α} (singleton_definable α) (Set.finite_singleton _)
    f hf _ (Set.mem_singleton _)

end DiamondIntegral.Section4.GammaNameTuples
