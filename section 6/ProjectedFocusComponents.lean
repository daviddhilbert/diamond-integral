import «section 6».ProjectedFocusLifts

/-! A permitted component from actual continuous projected focus data,
named uniform covariance and a named dominating aperture coefficient.
The same constructor applies to every protected source piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {U : DefSet (rawRVSpace (M := M) r) S}

def projectedFocusComponent
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) (hPD : VFDoublyBounded P.carrier)
    (htag : ∀ p ∈ P.carrier, ∀ q ∈ P.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hf : ∀ u, Continuous (FMT.focusFibre f u))
    (hFocusRV : ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre f p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last n)))
    (γ β : Gamma M)
    (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}})
    (hInv : ∀ u, AlphaInvariant (fun _ => γ) (vfFibre P.carrier u))
    (hCov : ∀ u, AlphaBetaCovariant (fun _ => β) (fun _ => γ)
      (vfFibre (projectedActiveDomain A U).carrier u) (totalFocusFibre f u))
    (c : VF M) (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hcdom : ∀ a ∈ scalarFocusImage f, γ.val < vfValue (c*a)) : CentripetalData (G := G) P where
  coordinate := Fin.last n
  activeTags := U
  focus := fun x u => totalFocusFibre f u (Fin.init x) 0
  focusMap := projectedFocusLift f hPA
  focusMap_eq := by
    intro p
    rw [init_update_last]
    exact projectedFocusLift_value f hPA p
  sourceProper := hP
  sourceDoublyBounded := hPD
  tagged := htag
  continuous := by
    intro u hu
    simp only [init_update_last]
    exact projectedFocusLift_continuousOn f hPA hf u hu
  focusRV := by
    intro p hp hu
    simp only [init_update_last]
    exact hFocusRV p (hPA hp) hu
  coefficient := c
  coefficient_nonzero := hc0
  coefficient_nonnegative := hcpos
  coefficient_definable := hcdef
  covariance := by
    intro u hu
    have hnγ := hγ.mono (Set.subset_union_left : S ⊆ S ∪ Set.range (rvValues u))
    have hnβ := (gamma_max_named γ β hγ hβ).mono
      (Set.subset_union_left : S ⊆ S ∪ Set.range (rvValues u))
    refine ⟨γ,fun _ => max γ β,hnγ,fun _ => hnβ,?_,?_,?_⟩
    · intro a b hab
      apply hInv u a b
      apply hab.of_larger_radius
      intro i
      split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    · intro a ha b hb hab
      have hA : (Fin.init a,u) ∈ (projectedActiveDomain A U).carrier := ⟨⟨(a,u),hPA ha,hu⟩,rfl⟩
      have hB : (Fin.init b,u) ∈ (projectedActiveDomain A U).carrier := ⟨⟨(b,u),hPA hb,hu⟩,rfl⟩
      have hClose : Congruent (fun _ => β) (Fin.init a) (Fin.init b) := by
        intro i
        have hh := hab i.castSucc
        have hlt := (show β.val ≤ (max γ β).val from le_max_right γ β).trans_lt hh
        simpa only [Function.update_of_ne (Fin.castSucc_ne_last i),Fin.init] using hlt
      have hh := hCov u (Fin.init a) hA (Fin.init b) hB hClose 0
      simpa only [init_update_last] using hh
    · intro a ha
      let q : projectedActiveDomain A U := ⟨(Fin.init a,u),⟨⟨(a,u),hPA ha,hu⟩,rfl⟩⟩
      have hm : (f q).val 0 ∈ scalarFocusImage f := ⟨q,rfl⟩
      have he := congrFun (totalFocusFibre_at f u (Fin.init a) q.property) 0
      simpa only [init_update_last,he] using (hcdom _ hm).le

end DiamondIntegral.Section6
