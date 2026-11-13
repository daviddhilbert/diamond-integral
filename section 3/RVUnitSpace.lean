import «section 3».RVMonomialMaps
import Section3.GammaCodeDefinability
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rvUnitValues (x : Fin n → (CanonicalRV.RVSort M)ˣ) : Fin n → M := fun i => (x i).val.val

theorem rvUnitValues_injective : Function.Injective (rvUnitValues (M := M) (n := n)) := by
  intro x y he
  funext i
  apply Units.ext
  apply Subtype.ext
  exact congrFun he i

theorem rvUnitValues_range : Set.range (rvUnitValues (M := M) (n := n)) = {z | ∀ i, NonzeroRV (z i)} := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩ i
    exact ⟨(x i).val.property,fun h => Units.ne_zero (x i) (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩
  · intro hz
    let x : Fin n → (CanonicalRV.RVSort M)ˣ := fun i => Units.mk0 ⟨z i,(hz i).1⟩ (fun h =>
      (hz i).2 ((congrArg Subtype.val h).trans RVOperations.zero_val))
    exact ⟨x,rfl⟩

theorem rvUnitValues_range_definable : (∅ : Set M).Definable LRV (Set.range (rvUnitValues (M := M) (n := n))) := by
  rw [rvUnitValues_range,Set.ofPred_forall]
  exact Set.definable_iInter_of_finite (fun i => (nonzero_rv_definable (M := M) ∅).preimage_comp (fun _ : Fin 1 => i))

def rawRVUnitSpace (n : ℕ) : Space LRV M :=
  Space.ofEmbedding (rvUnitValues (M := M) (n := n)) rvUnitValues_injective rvUnitValues_range_definable

theorem rvUnitValues_decode (c : (rawRVUnitSpace (M := M) n).domain) :
    rvUnitValues ((rawRVUnitSpace n).decode c) = c.val :=
  Space.ofEmbedding_decode rvUnitValues rvUnitValues_injective (rawRVUnitSpace n).domain_definable c

theorem decode_rvUnitValues (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    (rawRVUnitSpace n).decode ⟨rvUnitValues x,Set.mem_range_self x⟩ = x :=
  rvUnitValues_injective (rvUnitValues_decode _)

/-- A raw code predicate compatible with RV units defines a set in the
actual nonzero RV presentation, over the same real parameter set. -/
theorem rvUnitSpace_predicate_definable (S : Set M) (P : (Fin n → (CanonicalRV.RVSort M)ˣ) → Prop)
    (Q : (Fin n → M) → Prop) (hQ : S.Definable LRV {z | Q z})
    (hPQ : ∀ x, P x ↔ Q (rvUnitValues x)) : (rawRVUnitSpace n).Definable S {x | P x} := by
  have hh := ((rawRVUnitSpace (M := M) n).definable_domain S).inter hQ
  change S.Definable LRV ((rawRVUnitSpace n).preimage {x | P x})
  convert hh using 1
  ext z
  change (∃ hz : z ∈ (rawRVUnitSpace n).domain, P ((rawRVUnitSpace n).decode ⟨z,hz⟩)) ↔
    (z ∈ (rawRVUnitSpace n).domain ∧ Q z)
  constructor
  · rintro ⟨hz,hp⟩
    have hq := (hPQ _).mp hp
    have he : rvUnitValues ((rawRVUnitSpace n).decode ⟨z,hz⟩) = z := rvUnitValues_decode ⟨z,hz⟩
    rw [he] at hq
    exact ⟨hz,hq⟩
  · rintro ⟨hz,hq⟩
    refine ⟨hz,(hPQ _).mpr ?_⟩
    have he : rvUnitValues ((rawRVUnitSpace n).decode ⟨z,hz⟩) = z := rvUnitValues_decode ⟨z,hz⟩
    rw [he]
    exact hq
end DiamondIntegral.Section3
