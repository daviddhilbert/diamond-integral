import «section 4».RVResidueFiniteNormalization
import «section 4».RVResidueScaledCovers
import «section 4».FieldTaggedFamilies

/-! Every finite-pattern RV set has a single pure-field code and a
finite scaled-coordinate description of its decoding bijection. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueCodes
open RVResidueFiniteNormalization RVResidueScaledCovers
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure Code {n : ℕ} (A : Set (Fin n → CanonicalRV.RVSort M)) where
  chart : FieldDefinableRing.Chart (ModelResidue M)
  decode : (Fin chart.arity → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)
  bijective : Set.BijOn decode chart.domain A
  cover : Cover chart.domain decode

section Construction
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
  (A : DefSet (rawRVSpace (M := M) n) S) [Finite (Patterns A)] [Infinite (ModelResidue M)]

local instance : Fintype (Patterns A) := Fintype.ofFinite (Patterns A)

def tag : Patterns A → ModelResidue M := FieldTaggedFamilies.tag

theorem tag_injective : Function.Injective (tag A) := FieldTaggedFamilies.tag_injective

def chart : FieldDefinableRing.Chart (ModelResidue M) :=
  FieldTaggedFamilies.chart (tag A) (normalized hc A) (normalized_definable hc A)

def equiv : (chart hc A).domain ≃ A :=
  (FieldTaggedFamilies.equiv (tag A) (tag_injective A) (normalized hc A)).symm.trans
    (sumEquiv hc A)

def decode (x : Fin (n + 1) → ModelResidue M) : Fin n → CanonicalRV.RVSort M :=
  if hx : x ∈ (chart hc A).domain then (equiv hc A ⟨x, hx⟩).val else fun _ => 0

theorem decode_bijective : Set.BijOn (decode hc A) (chart hc A).domain A.carrier := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simpa only [decode, dif_pos hx] using (equiv hc A ⟨x, hx⟩).property
  · intro x hx y hy he
    simp only [decode, dif_pos hx, dif_pos hy] at he
    exact congrArg Subtype.val ((equiv hc A).injective (Subtype.ext he))
  · intro t ht
    let x := (equiv hc A).symm ⟨t, ht⟩
    refine ⟨x.val, x.property, ?_⟩
    simp only [decode, dif_pos x.property]
    exact congrArg Subtype.val ((equiv hc A).apply_symm_apply ⟨t, ht⟩)

theorem decode_on_tag (i : Patterns A) (x : Fin (n + 1) → ModelResidue M)
    (hx : x ∈ (chart hc A).domain) (hi : x 0 = tag A i) :
    decode hc A x = residueScale (representative A i).val (Fin.tail x) := by
  have hdom := hx
  obtain ⟨j, hj, hnorm⟩ := hdom
  have hji : j = i := tag_injective A (hj.symm.trans hi)
  subst j
  let z : Σ i : Patterns A, normalized hc A i := ⟨i, ⟨Fin.tail x, hnorm⟩⟩
  let e := FieldTaggedFamilies.equiv (tag A) (tag_injective A) (normalized hc A)
  have he : e z = ⟨x, hx⟩ := by
    apply Subtype.ext
    change Fin.cons (tag A i) (Fin.tail x) = x
    rw [← hi]
    exact Fin.cons_self_tail x
  have hsymm : e.symm ⟨x, hx⟩ = z := by rw [← he, Equiv.symm_apply_apply]
  simp only [decode, dif_pos hx]
  change (sumEquiv hc A (e.symm ⟨x, hx⟩)).val = _
  rw [hsymm, sumEquiv_value]

def cover : Cover (FieldTaggedFamilies.domain (tag A) (normalized hc A)) (decode hc A) where
  Index := Patterns A
  finite := inferInstance
  piece i := {
    guard := {x | x 0 = tag A i}
    definable := (pure_proj (0 : Fin (n + 1))).eq_const (tag A i)
    scale := (representative A i).val
    coord := Fin.succ }
  covers x hx := by
    obtain ⟨i, hi, _⟩ := hx
    exact ⟨i, hi⟩
  agrees i x hx hi := decode_on_tag hc A i x hx hi

def code : Code A.carrier := ⟨chart hc A, decode hc A, decode_bijective hc A, cover hc A⟩

end Construction
end DiamondIntegral.Section4.RVResidueCodes
