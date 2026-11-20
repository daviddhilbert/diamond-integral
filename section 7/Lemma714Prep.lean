import «section 7».Lemma714Transl

/-! Lemma 7.14, part 36: prepared contraction data.

The reduction `n + 1 → 1` runs over **prepared contraction data**
(`PrepContr A ω`): a bijection `prep : A → Y` onto a set `Y` with the same VF
dimension that keeps the old labels and translates the VF coordinates by an
amount determined by the labels of `Y`, followed by a measured ordered
contraction `C` of `(Y, θ)` with `θ ∘ prep = ω`. A normalized measured
contraction, after reindexing its source, is such data (its zero-centred
normalization is a label translation); so is the rest of the first stage of
such data, pulled back to the common VF projection. This is how GAP-REPAIRS 11
is handled inside the proof: the induction never needs the two first-stage sets
to come from the same centre.

The head-start class of the data is the head-start class of `C` with the
labels carried by `prep` (`PrepContr.cls`). With one VF coordinate, prepared
contraction data give unary contraction data with the same head-start class
(`PrepContr.toUnary`, `PrepContr.cls_eq_clsH`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### Unbundling head-start finiteness in any VF dimension -/

theorem unbundle_finite_n {S : Set M} {m q k : ℕ} {Y : DefSet (rawMixedSpace (M := M) m q) S} {lab : Fin k → Fin q}
    (hB : ∀ a : Fin (m + k) → VF M, {u : Fin q → RVInfinity M |
      (a, u) ∈ (rvHeadStartBundle Y k lab).carrier}.Finite) :
    ∀ (a : Fin m → VF M) (t : Fin k → RVInfinity M),
      {u : Fin q → RVInfinity M | (a, u) ∈ Y.carrier ∧ u ∘ lab = t}.Finite := by
  intro a t
  obtain ⟨e, he⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) t
  apply (hB (Fin.append a e)).subset
  rintro u ⟨hu, hl⟩
  apply (mem_rvHeadStartBundle Y k lab _ _).mpr
  rw [headStartBaseVF_append, headStartExtraVF_append, he, hl]
  exact ⟨hu, rfl⟩

/-! ### Prepared contraction data -/

/-- **Prepared contraction data** for `(A, ω)`. -/
structure PrepContr {T : LRV.Substructure M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) where
  q : ℕ
  Y : DefSet (rawMixedSpace (M := M) (n + 1) q) (T : Set M)
  prep : Map A Y
  homeo : ProperCovariantHomeomorphism (G := G) prep
  unit : ∀ p : A, HasMixedUnitDerivativeAt prep p
  oldIndex : Fin r → Fin q
  retained : ∀ p : A, ∀ j, (prep p).val.2 (oldIndex j) = p.val.2 j
  transl : ∀ p p' : A, (prep p).val.2 = (prep p').val.2 → trAt prep p = trAt prep p'
  θ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))
  transport : ∀ p : A, (θ (prep p)).val = (ω p).val
  C : MeasuredOrderedContraction (G := G) Y θ

namespace PrepContr
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  {T : LRV.Substructure M} (hsmall : Cardinal.mk (T : Set M) < κ)
  {n r k : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}

include hc h00 hκ hs hsmall in
/-- Head-start finiteness passes from `A` to the prepared set. -/
theorem finY (D : PrepContr (G := G) A ω) (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin D.q → RVInfinity M | (a, u) ∈ D.Y.carrier ∧ u ∘ (D.oldIndex ∘ π) = t}.Finite :=
  unbundle_finite_n (head_start_finite_rv_fibres_of_bijective hc h00 hκ.le hs hsmall D.prep D.homeo.bijective k π
    (D.oldIndex ∘ π) (fun p i => D.retained p (π i)) hFin)

/-- **The head-start class of prepared contraction data**, in degree `(n + 1) + k`. -/
def cls (D : PrepContr (G := G) A ω) (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) : Cls (BT T) ((n + 1) + k) :=
  BoundedClasses.cls (objOf hc T (D.C.headStartObject hc h00 hκ.le hs hsmall k (D.oldIndex ∘ π)
      (D.finY hc h00 hκ hs hsmall π hFin))
    (headStartObject_doublyBounded h00 hc hκ hs hsmall D.C k (D.oldIndex ∘ π) (D.finY hc h00 hκ hs hsmall π hFin)))

/-! ### One VF coordinate -/

section Unary
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  {A₁ : DefSet (rawMixedSpace (M := M) (0 + 1) r) (T : Set M)}
  {ω₁ : Map A₁ (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}

include h00 hc hκ hs hv hsmall hΓ in
/-- With one VF coordinate, prepared contraction data are unary contraction data. -/
def toUnary (D : PrepContr (G := G) A₁ ω₁) : UnaryContr (G := G) A₁ ω₁ where
  s := _
  target := D.C.lift.target
  map := D.C.lift.map.comp D.prep
  homeo := lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ D.homeo D.C.lift.home
  oldIndex := D.C.data.program.oldLabels ∘ D.oldIndex
  retained := fun p j => by
    change (D.C.lift.map (D.prep p)).val.2 (D.C.data.program.oldLabels (D.oldIndex j)) = p.val.2 j
    rw [D.C.lift.retained, D.retained]
  form := D.C.form
  form_transport := fun p => (D.C.form_transport (D.prep p)).trans (D.transport p)
  form_same_tags := D.C.form_same_tags
  pullback := D.C.lift.pullback
  vfBounded := D.C.lift.doublyBounded
  proper := D.C.lift.proper
  tagged := D.C.lift.target_tagged
  unit := fun p hp => by
    letI : CharZero (VF M) := vf_charZero_of_model00 h00
    have hInd := independent_map_of_finiteFibres hc D.prep
      (Map.finiteFibres_of_injective D.homeo.bijective.1) p hp
    exact (D.C.lift.genericUnit (D.prep p) hInd).comp (D.unit p)

theorem cls_eq_clsH (D : PrepContr (G := G) A₁ ω₁) (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (0 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A₁.carrier ∧ u ∘ π = t}.Finite) :
    D.cls hc h00 hκ hs hsmall π hFin =
      clsH hc ((D.toUnary hc h00 hκ hs hsmall hv hΓ).hgood hc h00 hκ hs hsmall π hFin) := by
  rw [clsH_eq_hsObj hc _ D.C.lift.target_tagged]
  apply cls_objOf_eq hc
  exact MeasuredRVIso.identity _

end Unary

end PrepContr

end DiamondIntegral.Section7.Lemma714Reduce
