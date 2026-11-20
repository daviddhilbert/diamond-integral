import «section 7».HeadStartK

/-! Lemma 7.23 for `n > 2`: the reduction to fibres over the other coordinates.

Let `A` be an object of `μVF^◇[n + 3]`, and `σ₁`, `σ₂ = σ₁ ∘ τ` two orders that
contract the same two coordinates `{i, j}` first, in opposite orders (`τ` swaps
the last two positions). Take contractions `G'₀`, `G''₀` of `A` in these orders
with a common centre, and contractions `H'`, `H''` of their first-stage sets in
the order `1`. The second-stage sets `B' = firstSet H'` and `B'' = firstSet H''`
lie over the remaining `n + 1` coordinates.

* `secondSet_vf`: `B'` and `B''` have the same VF projection, namely the
  projection of the normalized `A` to the coordinates other than `i`, `j`, in the
  common order.
* `reduction_7_23`: if their fibres, with the two leading labels as head-start
  labels, are `μIsp^db`-related over `S⟨a⟩` at every point `a`
  (`FibreHypothesis2`), then any standard contractions `F₁`, `F₂` of `A` in the
  orders `σ₁`, `σ₂` have `μIsp^db`-related classes.

The proof grafts twice (`ContractionChoice.cls_graftRest`,
`HeadStartK.cls_graftRest_k`), with the independence of the centre in head start
`0` and `1` (`Corollary715.ispRel_same_set`, `HeadStartK.ispRel_same_set_k`), and
applies the Lemma 7.14 input with head start `2`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma723Reduction
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.HeadStartK DiamondIntegral.Section7.KernelBaseChange

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ}

/-- The swap of the last two positions. -/
abbrev lastSwap (n : ℕ) : Equiv.Perm (Fin (n + 1 + 1 + 1)) :=
  Equiv.swap (Fin.last (n + 1 + 1)) (Fin.last (n + 1)).castSucc

theorem lastSwap_low (j : Fin (n + 1)) : lastSwap n j.castSucc.castSucc = j.castSucc.castSucc := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castSucc, Fin.val_last] at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castSucc, Fin.val_last] at this
    omega

section Sets
variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1 + 1 + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1 + 1 + 1))}

/-- The leading label of the first stage, as head-start label of the first-stage set. -/
abbrev π₁ (G₀ : NormalizedMeasuredContraction (G := G) A ω e) : Fin 1 → Fin (stage G₀).arity :=
  ![(stage G₀).leading]

/-- The two leading labels, as head-start labels of the second-stage set. -/
abbrev ρ₂ (G₀ : NormalizedMeasuredContraction (G := G) A ω e)
    (H : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) 1) :=
  restLabels H (π₁ G₀)

/-- The VF projection of the second-stage set. -/
theorem secondSet_vf (G₀ : NormalizedMeasuredContraction (G := G) A ω e)
    (H : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) 1) (b : Fin (n + 1) → VF M) :
    (∃ u, (b, u) ∈ (firstSet H).carrier) ↔
      ∃ p ∈ A.carrier, ∀ j, b j = tau G₀.normalization.center (p.1 (e j.castSucc.castSucc)) := by
  rw [firstSet_vf H b]
  constructor
  · rintro ⟨p, hp, hb⟩
    have hp' : ∃ u, (p.1, u) ∈ (firstSet G₀).carrier := ⟨p.2, hp⟩
    obtain ⟨q, hq, hpq⟩ := (firstSet_vf G₀ p.1).mp hp'
    refine ⟨q, hq, fun j => ?_⟩
    have hfix : tau H.normalization.center (p.1 j.castSucc) = p.1 j.castSucc :=
      (point_fst H.normalization p j.castSucc).symm.trans
        (congrFun (H.normalization.point_field_of_doublyBounded (stage G₀).contracted_doublyBounded hp) j.castSucc)
    exact (hb j).trans (hfix.trans (hpq j.castSucc))
  · rintro ⟨q, hq, hb⟩
    let y : Fin (n + 1 + 1) → VF M := fun k => tau G₀.normalization.center (q.1 (e k.castSucc))
    obtain ⟨u, hu⟩ := (firstSet_vf G₀ y).mpr ⟨q, hq, fun _ => rfl⟩
    refine ⟨(y, u), hu, fun j => ?_⟩
    have hfix : tau H.normalization.center (y j.castSucc) = y j.castSucc :=
      (point_fst H.normalization (y, u) j.castSucc).symm.trans
        (congrFun (H.normalization.point_field_of_doublyBounded (stage G₀).contracted_doublyBounded hu) j.castSucc)
    exact (hb j).trans hfix.symm

end Sets

end DiamondIntegral.Section7.Lemma723Reduction
