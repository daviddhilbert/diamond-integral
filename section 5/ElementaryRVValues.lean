import «section 5».ElementaryNamedDefinableSets
import «section 5».GammaRVSetObjects
import Mathlib.ModelTheory.ElementaryMaps

/-! Elementary embeddings preserve the actual RV and value quotients.
Restriction of a finite-value RV set to the smaller model still has
finite value support, including its zero-coordinate patterns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (e : M ↪ₑ[LRV] N)

def elementaryRVMap (r : CanonicalRV.RVSort M) : CanonicalRV.RVSort N :=
  ⟨e r.val,by
    have h := e.map_rel Rel.memRV ![r.val]
    have ht : (e ∘ (![r.val] : Fin 1 → M)) = ![e r.val] := by
      funext i
      fin_cases i
      rfl
    rw [ht] at h
    exact h.mpr r.property⟩

theorem elementaryRVMap_injective : Function.Injective (elementaryRVMap e) := by
  intro r s h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

theorem elementaryRVMap_le (r s : CanonicalRV.RVSort M) :
    iLe (elementaryRVMap e r).val (elementaryRVMap e s).val ↔ iLe r.val s.val := by
  have h := e.map_rel Rel.rvLe ![r.val,s.val]
  have ht : (e ∘ (![r.val,s.val] : Fin 2 → M)) = ![e r.val,e s.val] := by
    funext i
    fin_cases i <;> rfl
  rw [ht] at h
  exact h

theorem elementaryRVMap_sameValue (r s : CanonicalRV.RVSort M) :
    Values.sameValue (elementaryRVMap e r) (elementaryRVMap e s) ↔ Values.sameValue r s := by
  exact and_congr (elementaryRVMap_le e r s) (elementaryRVMap_le e s r)

def elementaryGammaTopMap : Values.GammaTop (M := M) → Values.GammaTop (M := N) :=
  Quotient.map (elementaryRVMap e) (fun r s h => (elementaryRVMap_sameValue e r s).mpr h)

theorem elementaryGammaTopMap_vrv (r : CanonicalRV.RVSort M) :
    elementaryGammaTopMap e (Values.vrv r) = Values.vrv (elementaryRVMap e r) := rfl

theorem elementaryGammaTopMap_injective : Function.Injective (elementaryGammaTopMap e) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h r =>
    induction b using Quotient.inductionOn with
    | h s =>
      intro he
      apply (Values.vrv_eq_iff r s).mpr
      exact (elementaryRVMap_sameValue e r s).mp
        ((Values.vrv_eq_iff (elementaryRVMap e r) (elementaryRVMap e s)).mp he)

theorem elementaryRV_finite_values_restrict {n : ℕ} (X : Set (Fin n → CanonicalRV.RVSort N))
    (hX : ((fun x i => Values.vrv (x i)) '' X).Finite) :
    ((fun x i => Values.vrv (x i)) '' {x : Fin n → CanonicalRV.RVSort M |
      elementaryRVMap e ∘ x ∈ X}).Finite := by
  let f : (Fin n → Values.GammaTop (M := M)) → (Fin n → Values.GammaTop (M := N)) :=
    fun g => elementaryGammaTopMap e ∘ g
  have hf : Function.Injective f := by
    intro g h he
    funext i
    exact elementaryGammaTopMap_injective e (congrFun he i)
  apply (hX.preimage hf.injOn).subset
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨elementaryRVMap e ∘ x,hx,?_⟩
  rfl

end DiamondIntegral.Section5
