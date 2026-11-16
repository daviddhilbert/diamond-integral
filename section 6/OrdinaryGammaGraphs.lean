import «section 6».OrdinaryNamedGammaBase

/-! Complete original-base graph descent for the ordinary matching
construction. Internal Gamma presentations add no real parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}

theorem rawMixed_relation_values (R : Mixed M n r → Mixed M m s → Prop) :
    (rawMixedSpace n r).relation (rawMixedSpace m s) R=
      {z | ∃ p q,R p q ∧ Sum.elim (mixedValues p) (mixedValues q)=z} := by
  ext z
  constructor
  · rintro ⟨hp,hq,hR⟩
    let p := (rawMixedSpace n r).decode ⟨z ∘ Sum.inl,hp⟩
    let q := (rawMixedSpace m s).decode ⟨z ∘ Sum.inr,hq⟩
    refine ⟨p,q,hR,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun (mixedValues_decode _) i
    | inr i => exact congrFun (mixedValues_decode _) i
  · rintro ⟨p,q,hR,rfl⟩
    have h := (rawMixedSpace n r).relation_decode (rawMixedSpace m s) R
      ⟨mixedValues p,mixedValues_mem_domain p⟩ ⟨mixedValues q,mixedValues_mem_domain q⟩
    rw [decode_mixedValues,decode_mixedValues] at h
    exact h.mpr hR

def ordinaryGammaRelationIndex : ((Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s)) ≃ Fin ((n+r)+(m+s)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

theorem ordinary_gamma_relation_values (p : Mixed M n r) (q : Mixed M m s) :
    Fin.append (SpecialTransformations.Section5.gammaPointCode p)
      (SpecialTransformations.Section5.gammaPointCode q) ∘ ordinaryGammaRelationIndex=
      Sum.elim (mixedValues p) (mixedValues q) := by
  funext i
  cases i with
  | inl i =>
    change Fin.append _ _ (Fin.castAdd (m+s) (finSumFinEquiv i))=mixedValues p i
    rw [Fin.append_left]
    exact congrFun (ordinary_gamma_point_values p) i
  | inr i =>
    change Fin.append _ _ (Fin.natAdd (n+r) (finSumFinEquiv i))=mixedValues q i
    rw [Fin.append_right]
    exact congrFun (ordinary_gamma_point_values q) i

theorem ordinary_named_gamma_graph_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (R : Mixed M n r → Mixed M m s → Prop)
    (hR : SpecialTransformations.Section5.GammaGraphDefinable (ordinaryNamedGammaBase S) R) :
    (rawMixedSpace n r).RelationDefinable (rawMixedSpace m s) S R := by
  have h : S.Definable LRV {z : Fin ((n+r)+(m+s)) → M | ∃ (p : Mixed M n r) (q : Mixed M m s),
      R p q ∧ Fin.append (SpecialTransformations.Section5.gammaPointCode p)
        (SpecialTransformations.Section5.gammaPointCode q)=z} :=
    (ordinary_named_gamma_eliminate hc hR).raw_definable
  have h' := h.preimage_comp (ordinaryGammaRelationIndex (n := n) (r := r) (m := m) (s := s)).symm
  change S.Definable LRV ((rawMixedSpace n r).relation (rawMixedSpace m s) R)
  rw [rawMixed_relation_values]
  change S.Definable LRV {z : ((Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s)) → M |
    ∃ (p : Mixed M n r) (q : Mixed M m s),R p q ∧ Sum.elim (mixedValues p) (mixedValues q)=z}
  convert h' using 1
  ext z
  constructor
  · rintro ⟨p,q,hR,he⟩
    refine ⟨p,q,hR,?_⟩
    funext i
    have hValue := congrFun ((ordinary_gamma_relation_values p q).trans he) (ordinaryGammaRelationIndex.symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hValue
  · rintro ⟨p,q,hR,he⟩
    refine ⟨p,q,hR,?_⟩
    simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using
      (ordinary_gamma_relation_values p q).symm.trans
        (congrArg (fun w => w ∘ ordinaryGammaRelationIndex) he)

end DiamondIntegral.Section6
