import «section 3».RVFamilyObjects
import Section4.RVRestrictions

/-! The explicit family realization respects restrictions and complements,
using disjoint tags rather than an assumed additivity property. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {N k : ℕ}

theorem rvFamilyTuple_injective : Function.Injective
    (fun p : Fin N × (Fin k → CanonicalRV.RVSort M) => rvAppend (rvFamilyTag (M := M) p.1) p.2) := by
  rintro ⟨i, t⟩ ⟨j, u⟩ he
  have hij : i = j := by
    apply rvFamilyTag_injective (M := M)
    funext q
    simpa only [rvAppend, Fin.append_left] using congrFun he (Fin.castAdd k q)
  have htu : t = u := by
    funext q
    simpa only [rvAppend, Fin.append_right] using congrFun he (Fin.natAdd N q)
  exact Prod.ext hij htu

theorem rvFamilyRealization_mono
    (A X : Fin N → DefSet (rawRVSpace (M := M) k) S)
    (hX : ∀ i, (X i).carrier ⊆ (A i).carrier) :
    (FiniteFamily.rvRealization ⟨N, X⟩).carrier ⊆ (FiniteFamily.rvRealization ⟨N, A⟩).carrier := by
  rintro t ⟨i, u, hu⟩
  exact ⟨i, ⟨u.val, hX i u.property⟩, hu⟩

theorem rvFamilyRealization_sdiff (A X : Fin N → DefSet (rawRVSpace (M := M) k) S) :
    (FiniteFamily.rvRealization ⟨N, fun i => (A i).sdiff (X i)⟩).carrier =
      (FiniteFamily.rvRealization ⟨N, A⟩).carrier \ (FiniteFamily.rvRealization ⟨N, X⟩).carrier := by
  ext t
  constructor
  · rintro ⟨i, u, hu⟩
    refine ⟨⟨i, ⟨u.val, u.property.1⟩, hu⟩, ?_⟩
    rintro ⟨j, v, hv⟩
    have he : rvAppend (rvFamilyTag i) u.val = rvAppend (rvFamilyTag j) v.val := hu.trans hv.symm
    have hp : (i, u.val) = (j, v.val) := rvFamilyTuple_injective (M := M) (N := N) (k := k) he
    have hij : i = j := congrArg Prod.fst hp
    subst j
    have huv : u.val = v.val := congrArg Prod.snd hp
    exact u.property.2 (huv.symm ▸ v.property)
  · rintro ⟨⟨i, u, hu⟩, hn⟩
    have hnu : u.val ∉ (X i).carrier := by
      intro hx
      exact hn ⟨i, ⟨u.val, hx⟩, hu⟩
    exact ⟨i, ⟨u.val, u.property, hnu⟩, hu⟩

end DiamondIntegral.Section3
