import «section 6».OrdinaryMaps
import «section 6».NamedVFValues
import IntegrationSection5.UnaryBijection
import Section3.GammaClosureElimination

/-! Ordinary preparation may internally use real representatives of
Gamma parameters. Naming precisely the already definable value fibres
does not enlarge the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def ordinaryNamedGammaBase (S : Set M) : GammaParameters.Base (M := M) :=
  ⟨S,{γ | S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}}⟩

theorem ordinary_named_gamma_eliminate
    (hc : CanonicalStructure.IsCanonical (M := M)) {l : ℕ} {sn : Fin l → SortTag}
    {A : Set (Fin l → M)} (hA : GammaParameters.DefinableOverBase (ordinaryNamedGammaBase S) sn A) :
    DefinableOver S sn A := by
  apply hA.eliminate_to_real_base
  · intro b hb
    rcases TypedModelMap.sort_cover (M := M) b with hVF | hRV
    · exact ⟨.vf,definableClosureAt_of_mem hb hVF⟩
    · exact ⟨.rv,definableClosureAt_of_mem hb hRV⟩
  · intro γ hγ
    apply (definableAt_iff_normalized_raw S .rv (Values.gammaPullback {γ})).mpr
    refine ⟨?_,fun z hz => hz.1⟩
    change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1) _
    rw [normalize_eq_of_isCanonical hc]
    exact hγ

theorem ordinary_gamma_point_values (p : Mixed M n r) :
    SpecialTransformations.Section5.gammaPointCode p ∘ finSumFinEquiv=mixedValues p := by
  funext i
  cases i with
  | inl i => simp only [Function.comp_apply,finSumFinEquiv_apply_left,
      SpecialTransformations.Section5.gammaPointCode,Fin.append_left]
             rfl
  | inr i => simp only [Function.comp_apply,finSumFinEquiv_apply_right,
      SpecialTransformations.Section5.gammaPointCode,Fin.append_right]
             rfl

theorem ordinary_named_gamma_set_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : Set (Mixed M n r))
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S) A) :
    (rawMixedSpace (M := M) n r).Definable S A := by
  apply (mixed_definable_iff_values_image S A).mpr
  have h : S.Definable LRV (SpecialTransformations.Section5.gammaPointCode '' A) :=
    (ordinary_named_gamma_eliminate hc hA).raw_definable
  have h' := h.preimage_comp (finSumFinEquiv.symm : Fin (n+r) → Fin n ⊕ Fin r)
  convert h' using 1
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨p,hp,?_⟩
    funext i
    have he := congrFun (ordinary_gamma_point_values p) (finSumFinEquiv.symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using he
  · rintro ⟨p,hp,he⟩
    refine ⟨p,hp,?_⟩
    simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using
      (ordinary_gamma_point_values p).symm.trans (congrArg (fun w => w ∘ finSumFinEquiv) he)

end DiamondIntegral.Section6
