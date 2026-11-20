import «section 7».Corollary715

/-! Head starts of any length (for Lemma 7.23 with `n > 2` and for 7.24).

* `fibreObject_doublyBounded`: the fibre objects of a proper invariant set,
  with any head-start labels, are doubly bounded.
* `ispRel_same_set_k`: the independence of the centre with head start `k`.
  Lemma 7.14 with equal sets gives `μIsp^db` between any two standard
  contractions of one set in one order, read with the same head-start labels.
* `cls_graftRest_k`: grafting a contraction `H` of the first-stage set after the
  first stage of `F` (`ContractionChoice.graftRest`) gives, with head start `k`
  and labels `π`, the class of `H` with head start `k + 1` and labels
  `restLabels F π`. For `k = 0` this is `ContractionChoice.cls_graftRest`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.HeadStartK
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Fibre objects of a proper invariant set are doubly bounded. -/
theorem fibreObject_doublyBounded {T : LRV.Substructure M} {m r k : ℕ}
    (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M)) (hA : ProperInvariant (T : Set M) A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (a : Fin m → VF M) (π : Fin k → Fin r)
    (hFin : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero) :
    (fibreObject T A ω a π hFin hNZ).doublyBounded := by
  obtain ⟨γ, hγ⟩ := hA.rvBounded
  refine ⟨⟨γ, fun u hu i => hγ (a, u) ((mem_fibreDomain A a u).mp hu) i⟩, ⟨γ, ?_⟩⟩
  rintro _ ⟨u, rfl⟩ i
  exact hγ (a, u.val) ((mem_fibreDomain A a u.val).mp u.property) (π i)

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include V hV hVT hTV hnt in
/-- **Independence of the centre, head start `k`.** -/
theorem ispRel_same_set_k (h714 : Lemma714 M G) {n r k : ℕ} (A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (hA : ProperInvariant (T : Set M) A.carrier)
    (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero)
    {e : Equiv.Perm (Fin (n + 1))} (F₁ F₂ : NormalizedMeasuredContraction (G := G) A ω e) :
    IspRel (cls (objOf hc T (F₁.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π hFin)
        (F₁.headStartObject_doublyBounded k π)))
      (cls (objOf hc T (F₂.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π hFin)
        (F₂.headStartObject_doublyBounded k π))) :=
  h714 hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ A A ω ω hA hA (fun _ => Iff.rfl) π π hFin hFin hNZ hNZ
    (fun a _ => ⟨fibreObject_doublyBounded A hA ω a π _ _, fibreObject_doublyBounded A hA ω a π _ _,
      ispRel_refl _⟩) F₁ F₂

variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1 + 1))}
variable (F : NormalizedMeasuredContraction (G := G) A ω e)
variable (H : NormalizedMeasuredContraction (G := G) (firstSet F) (firstForm F) 1)

/-- **Grafting, head start `k`.** -/
theorem cls_graftRest_k {k : ℕ} (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (n + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hFinH : ∀ (a : Fin (n + 1) → VF M) (t : Fin (k + 1) → RVInfinity M),
      {u | (a, u) ∈ (firstSet F).carrier ∧ u ∘ restLabels F π = t}.Finite) :
    cls (objOf hc T ((graftRest h00 hc linear hκ hs hv hsmall hΓ F H).headStartMeasuredObject h00 hc linear hκ hs hv
        hsmall hΓ k π hFin) ((graftRest h00 hc linear hκ hs hv hsmall hΓ F H).headStartObject_doublyBounded k π)) =
      castCls (show (n + 1) + (k + 1) = (n + 1 + 1) + k by omega)
        (cls (objOf hc T (H.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ (k + 1) (restLabels F π) hFinH)
          (H.headStartObject_doublyBounded (k + 1) (restLabels F π)))) := by
  rw [cls_headStart_rest h00 hc linear hκ hs hv hsmall hΓ]
  congr 1
  exact cls_labelObject_eq hc rfl
    (restLift h00 hc linear hκ hs hv hsmall hΓ
      (graftRest h00 hc linear hκ hs hv hsmall hΓ F H).preparedContraction.data).recover
    H.preparedContraction.lift.originalTarget_recover _ _ (by
      intro f
      refine Finset.prod_congr rfl (fun i _ => congrArg f ?_)
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left, Fin.append_left]
        exact congrFun (precomposeFixedVF_volumeIndex h00 hc linear hκ hs hv hsmall hΓ
          H.preparedContraction.data.program _ _ _ _ _ _ _) i
      | right j =>
        rw [Fin.append_right, Fin.append_right]
        change (restProgram (graftRest h00 hc linear hκ hs hv hsmall hΓ F H).preparedContraction.data.program).oldLabels
            (restLabels (graftRest h00 hc linear hκ hs hv hsmall hΓ F H) π j) =
          H.preparedContraction.data.program.oldLabels (Fin.natAdd (n + 1) (restLabels F π j))
        exact precomposeFixedVF_oldLabels h00 hc linear hκ hs hv hsmall hΓ
          H.preparedContraction.data.program _ _ _ _ _ _ _ _)
    H.preparedContraction.data.rvForm _ _ _ _ _ _
    (restContraction h00 hc linear hκ hs hv hsmall hΓ
      (graftRest h00 hc linear hκ hs hv hsmall hΓ F H).preparedContraction.data).form _ H.form _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

end DiamondIntegral.Section7.HeadStartK
