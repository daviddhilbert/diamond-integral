import «section 5».KummerDescentDefinability

/-! The finite-level constructions are inverse on actual original-base
RV sets of prescribed value lines and on invariant constructible sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance finiteComparisonStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem framedRVSet_pure_definable {S : Set Carrier} {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) S) :
    (Set.univ : Set ℂ).Definable Language.ring (framedRVSet N a A) := by
  obtain ⟨C, hC, he⟩ := framedRVSet_constructible N a A
  convert constructible_field_definable (⊤ : Subfield ℂ) C hC using 1
  ext x
  exact he x

theorem framed_descendedOriginalSet {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X)
    (hinv : FiniteInvariant N a X) :
    framedRVSet N a (descendedOriginalSet N a X hX) = X := by
  ext x
  change (fun i => rvTag (finiteFrame N a x i)) ∈
    Set.range (fun u : descentSource N X hX => (descentMonomialMap N a X hX u).val) ↔ _
  rw [descentMonomialMap_range]
  constructor
  · rintro ⟨r, y, hy, he⟩
    have hn : finiteFrame N a x = frameAtRoot N a r y :=
      funext (fun i => congrArg taggedRVEquiv (congrFun he i))
    have hf : finiteFrame N a x ∈ descendSet N a X := ⟨r, y, hy, hn⟩
    have hmem := (Set.ext_iff.mp (descendSet_eq_image N a X hinv) _).mp hf
    obtain ⟨z, hz, hez⟩ := hmem
    exact (finiteFrame_injective N a hez) ▸ hz
  · intro hx
    refine ⟨rootOfPhase N 1, x, hx, ?_⟩
    simp only [frameAtRoot, rootOfPhase, OneMemClass.coe_one, weightedAction_one]

def HasFrameSupport {S : Set Carrier} {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) S) : Prop :=
  ∀ r ∈ A.carrier, ∀ i, taggedRVEquiv (r i) = none ∨
    value (taggedRVEquiv (r i)) = (((a i : ℚ) / (N : ℕ) : ℚ) : WithTop ℚ)

theorem frame_reconstruction {S : Set Carrier} {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) S) (hA : HasFrameSupport N a A)
    (r : A) : (fun i => rvTag (finiteFrame N a (fun j => lineCoefficient (taggedRVEquiv (r.val j))) i)) = r.val := by
  funext i
  have he := linePoint_coefficient ((a i : ℚ) / (N : ℕ))
    (⟨taggedRVEquiv (r.val i), hA r.val r.property i⟩ : ValueLine _)
  change rvTag (linePoint _ (lineCoefficient (taggedRVEquiv (r.val i)))) = _
  rw [he]
  exact taggedRVEquiv.symm_apply_apply _

theorem descended_framedOriginalSet {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : HasFrameSupport N a A) :
    (descendedOriginalSet N a (framedRVSet N a A) (framedRVSet_pure_definable N a A)).carrier = A.carrier := by
  rw [show (descendedOriginalSet N a (framedRVSet N a A) (framedRVSet_pure_definable N a A)).carrier =
      Set.range (fun u : descentSource N (framedRVSet N a A) (framedRVSet_pure_definable N a A) =>
        (descentMonomialMap N a (framedRVSet N a A) (framedRVSet_pure_definable N a A) u).val) from rfl,
    descentMonomialMap_range]
  ext r
  constructor
  · rintro ⟨root, x, hx, rfl⟩
    have hi := (framedRVSet_finiteInvariant N a A (rootPhase N root) x).mpr hx
    exact hi
  · intro hr
    let x : Fin n → ℂ := fun i => lineCoefficient (taggedRVEquiv (r i))
    have he := frame_reconstruction N a A hA ⟨r, hr⟩
    have hx : x ∈ framedRVSet N a A := by
      change (fun i => rvTag (finiteFrame N a x i)) ∈ A.carrier
      exact Eq.mpr (congrArg (fun v => v ∈ A.carrier) he) hr
    refine ⟨rootOfPhase N 1, x, hx, ?_⟩
    simp only [frameAtRoot, rootOfPhase, OneMemClass.coe_one, weightedAction_one]
    exact he.symm

end DiamondIntegral.Section5.PuiseuxOriginal
