import «section 6».ProtectedProjectedFreezing

/-! Actual permitted simultaneous steps after the protected continuity
repair. The finite freezing data and every current product-domain check
are constructed over the original base and retained in the result. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unary_focus_tail_continuous
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawVFSpace (M := M) 1) S}
    (f : Map A B) (u : Fin r → RVInfinity M) (a : VF M) : Continuous (focusTailMap f u a) := by
  have h : (Set.univ : Set (focusTailDomain A u a)).Subsingleton :=
    fun _ _ _ _ => Subsingleton.elim _ _
  simpa only [continuousOn_univ] using h.continuousOn (focusTailMap f u a)

theorem repaired_focus_simultaneous_step_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hf : ∀ u a, Continuous (focusTailMap f u a))
    (hFocusRV : ∀ p ∈ A.carrier, p.2 ∈ U.carrier →
      rv M (totalFocusFibre f p.2 (Fin.init p.1) 0) = rv M (p.1 (Fin.last (n+1))))
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier) :
    ∃ F : FMT.FocusFreezingData (projectedActiveDomain A U),
      (∀ E : F.balls, FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val)
        (F.centers E) (0 : Fin (n+1)).castSucc) ∧
      (∀ i, ∀ E : F.balls, FMT.CoordinateProductDomain (P i).carrier (FMT.vfOpenBall E.val)
        (F.centers E) (0 : Fin (n+1)).castSucc) ∧
      ∃ D : CentripetalData (G := G) A, D.coordinate = Fin.last (n+1) ∧ D.activeTags = U ∧
        (∀ x u, D.focus x u = totalFocusFibre (F.frozenMap f) u (Fin.init x) 0) ∧
        SimultaneousCentripetalChain (G := G) (Fin k) A (regularizeMap D.map.image).image
          (centripetalStepMap D) P := by
  obtain ⟨F,hCont,hRV,hProdA,hProdP⟩ := exists_protected_projected_focus_freezing h00 hc linear hκ hs hv
    V hsmall hΓ hV hVS hSV hnt A hA U f hf hFocusRV P hP
  obtain ⟨D,hj,hU,hFocus,hChain⟩ := continuous_focus_simultaneous_step_exists h00 hc linear hκ hs hv
    V hsmall hΓ hV hVS hSV hnt A hA hAD htag U (F.frozenMap f) hCont hRV P hPA hP
  exact ⟨F,hProdA,hProdP,D,hj,hU,hFocus,hChain⟩

end DiamondIntegral.Section6
