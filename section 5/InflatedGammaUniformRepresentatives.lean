import «section 5».InflatedGammaWeakLiftSchemata
import «section 5».Section5DischargedInputs
import «section 5».NativeWeakLiftValues
import «section 5».NativeRawWeightedValues

/-! # Uniform RV representatives over Gamma parameters

Exported interface (used by the inflated-family Fubini assembly):

* `section5BoundedRVSetValue G hc X` is `nativeRVSetValue … .bounded X` over `G.base`.
* `GammaVFFamily.uniform_representatives G A` gives a finite family of
  definable RV families `U l ⊆ Γ^n × RV^{r l}` over `G.base`, with a definable
  partition `P l` of `Γ^n` such that `U l` lies over `P l`, and
  - `A.row γ = ∅` iff every row of every `U l` at `γ` is empty (all `γ`);
  - for every `γ` with definable coordinates and `γ ∈ P l`,
    `E_b∫[A_γ] = section5BoundedRVSetValue G hc ((U l).gammaFibre γ hγ)`,
    and the rows of the other `U l'` at `γ` are empty, so
    `E_b∫[A_γ] = ∑ l, section5BoundedRVSetValue G hc ((U l).gammaFibre γ hγ)`;
  - `E_b∫[A^inf] = ∑ l, section5BoundedRVSetValue G hc (U l).gammaRVInflation`,
    where `gammaRVInflation` is `{(z,u) : z ∈ (RV^×)^n, (vrv z, u) ∈ U l}`.

The fibre equalities come from actual bijections `A_γ ≅ L(U_γ)` over the
original base, and the total equality from one actual bijection
`A^inf ∩ vv⁻¹(P l) ≅ L(U l^inf)` for each piece. The label of every
representative is a coordinate projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- The bounded RV value over the original Gamma ground. -/
def section5BoundedRVSetValue (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    {r : ℕ} (X : GammaGroundDefSet hc G.base (rawRVSpace (M := M) r)) : RESDimensionFreeReduction.Ring G.base :=
  nativeRVSetValue G.model00 GammaQE.gamma_piecewise_rational_affine G.uncountable.le G.saturated hc G.base
    G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded X

/-! ### Bijections given by definable functional relations -/

/-- A map whose complete graph is a definable relation that is functional
on the source and lands in the target. -/
def inflatedRelationMap {Q R : Space LRV M} {A' : GammaGroundDefSet hc B Q} {B' : GammaGroundDefSet hc B R}
    (Rel : Set (Q.prod R).Carrier) (hRel : GammaGroundDefinable hc B (Q.prod R) Rel)
    (htot : ∀ a ∈ A'.carrier, ∃! b, (a, b) ∈ Rel)
    (hmaps : ∀ a ∈ A'.carrier, ∀ b, (a, b) ∈ Rel → b ∈ B'.carrier) : GammaGroundMap A' B' where
  toFun a := ⟨Classical.choose (htot a.val a.property).exists,
    hmaps _ a.property _ (Classical.choose_spec (htot a.val a.property).exists)⟩
  graph_definable := by
    apply ((A'.definable.preimage (universalProductFst Q R B.real)).inter hRel).congr
    intro z
    constructor
    · rintro ⟨hz, hr⟩
      exact ⟨⟨z.1, hz⟩, rfl, (htot z.1 hz).unique (Classical.choose_spec (htot z.1 hz).exists) hr⟩
    · rintro ⟨a, ha, hb⟩
      have he : z = (a.val, Classical.choose (htot a.val a.property).exists) := Prod.ext ha.symm hb.symm
      refine ⟨?_, ?_⟩
      · change z.1 ∈ A'.carrier
        rw [← ha]
        exact a.property
      · rw [he]
        exact Classical.choose_spec (htot a.val a.property).exists

theorem inflatedRelationMap_spec {Q R : Space LRV M} {A' : GammaGroundDefSet hc B Q} {B' : GammaGroundDefSet hc B R}
    (Rel : Set (Q.prod R).Carrier) (hRel : GammaGroundDefinable hc B (Q.prod R) Rel)
    (htot : ∀ a ∈ A'.carrier, ∃! b, (a, b) ∈ Rel)
    (hmaps : ∀ a ∈ A'.carrier, ∀ b, (a, b) ∈ Rel → b ∈ B'.carrier) (a : A') :
    (a.val, (inflatedRelationMap Rel hRel htot hmaps a).val) ∈ Rel :=
  Classical.choose_spec (htot a.val a.property).exists

theorem inflatedRelationMap_bijective {Q R : Space LRV M} {A' : GammaGroundDefSet hc B Q}
    {B' : GammaGroundDefSet hc B R}
    (Rel : Set (Q.prod R).Carrier) (hRel : GammaGroundDefinable hc B (Q.prod R) Rel)
    (htot : ∀ a ∈ A'.carrier, ∃! b, (a, b) ∈ Rel)
    (hmaps : ∀ a ∈ A'.carrier, ∀ b, (a, b) ∈ Rel → b ∈ B'.carrier)
    (honto : ∀ b ∈ B'.carrier, ∃! a, a ∈ A'.carrier ∧ (a, b) ∈ Rel) :
    Function.Bijective (inflatedRelationMap Rel hRel htot hmaps) := by
  constructor
  · intro a₁ a₂ he
    have h1 := inflatedRelationMap_spec Rel hRel htot hmaps a₁
    have h2 := inflatedRelationMap_spec Rel hRel htot hmaps a₂
    rw [he] at h1
    let b := inflatedRelationMap Rel hRel htot hmaps a₂
    exact Subtype.ext ((honto b.val b.property).unique ⟨a₁.property, h1⟩ ⟨a₂.property, h2⟩)
  · intro b
    obtain ⟨a, ⟨ha, hab⟩, _⟩ := honto b.val b.property
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    exact (htot a ha).unique (inflatedRelationMap_spec Rel hRel htot hmaps ⟨a, ha⟩) hab

/-- The bijection given by a functional, onto, definable relation. -/
def inflatedRelationBijection {Q R : Space LRV M} {A' : GammaGroundDefSet hc B Q}
    {B' : GammaGroundDefSet hc B R}
    (Rel : Set (Q.prod R).Carrier) (hRel : GammaGroundDefinable hc B (Q.prod R) Rel)
    (htot : ∀ a ∈ A'.carrier, ∃! b, (a, b) ∈ Rel)
    (hmaps : ∀ a ∈ A'.carrier, ∀ b, (a, b) ∈ Rel → b ∈ B'.carrier)
    (honto : ∀ b ∈ B'.carrier, ∃! a, a ∈ A'.carrier ∧ (a, b) ∈ Rel) : GammaGroundBijection A' B' :=
  ⟨inflatedRelationMap Rel hRel htot hmaps, inflatedRelationMap_bijective Rel hRel htot hmaps honto⟩

/-! ### Representatives at definable parameters -/

namespace GammaWeakLiftDatum
variable {n m s : ℕ} (D : GammaWeakLiftDatum hc B n m s)

/-- The weak RV object `U_γ` at a parameter with definable coordinates. -/
def objectAt (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i))
    (hfin : ∀ y, (D.labelFibre γ y).Finite) : NativeWeakRVObject hc B D.degree where
  arity := D.arity + D.degree
  domain := D.domain.gammaFibre γ hγ
  volume := GammaGroundMap.ofGlobal _ _ (inflatedRVReindexMap B.real (Fin.natAdd D.arity))
    (fun _ => Set.mem_univ _)
  finite := by
    intro y
    apply ((hfin y.val).preimage Subtype.val_injective.injOn).subset
    intro u hu
    exact ⟨u.property, congrArg Subtype.val hu⟩

theorem mem_lift_objectAt (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i))
    (hfin : ∀ y, (D.labelFibre γ y).Finite) (q : (rawMixedSpace (M := M) D.degree (D.arity + D.degree)).Carrier) :
    q ∈ (nativeWeakRVObjectLift (D.objectAt γ hγ hfin)).carrier ↔ q ∈ D.liftRow γ := by
  constructor
  · rintro ⟨u, hu, hl⟩
    change (γ, q.2) ∈ D.domain.carrier ∧ q.2 ∘ Fin.natAdd D.arity = tupleRV q.1
    rw [← hu]
    exact ⟨u.property, hl⟩
  · rintro ⟨hq, hl⟩
    exact ⟨⟨q.2, hq⟩, rfl, hl⟩

/-- The actual bijection `A_γ ≅ L(U_γ)` over the original base. -/
def bijectionAt (A : GammaVFFamily hc B n) (D : GammaWeakLiftDatum hc B n A.m A.s)
    (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i))
    (hv : D.Valid A.domain.carrier γ) :
    GammaGroundBijection (A.fibreAt γ hγ).domain (nativeWeakRVObjectLift (D.objectAt γ hγ hv.labelFibre_finite)) :=
  inflatedRelationBijection {z | (γ, z) ∈ D.graph.carrier}
    (D.graph.definable.gammaFibre (inflatedGamma_singleton_definable hγ))
    (fun q hq => hv.total q hq)
    (fun q _ q' hqq => (D.mem_lift_objectAt γ hγ hv.labelFibre_finite q').mpr (hv.maps q q' hqq).2)
    (fun q' hq' => by
      obtain ⟨q, hq, hu⟩ := hv.onto q' ((D.mem_lift_objectAt γ hγ hv.labelFibre_finite q').mp hq')
      exact ⟨q, ⟨(hv.maps q q' hq).1, hq⟩, fun q₁ h₁ => hu q₁ h₁.2⟩)

end GammaWeakLiftDatum

/-- The value of a row at a definable parameter, computed from a valid datum. -/
theorem GammaWeakLiftDatum.fibre_value {n : ℕ} (G : GammaGroundContext M) (A : GammaVFFamily hc G.base n)
    (D : GammaWeakLiftDatum hc G.base n A.m A.s) (γ : Fin n → Values.Gamma (M := M))
    (hγ : ∀ i, GammaDefinableClosureAtBase G.base (γ i)) (hv : D.Valid A.domain.carrier γ) :
    section5BoundedVFIntegral G hc (nativeVFClass (A.fibreAt γ hγ)) =
      section5BoundedRVSetValue G hc (D.domain.gammaFibre γ hγ) :=
  nativeVFBoundedValue_of_weak_lift_bijection GammaQE.gamma_piecewise_rational_affine
    (completed18GroundLiftInput G hc) (A.fibreAt γ hγ) (D.objectAt γ hγ hv.labelFibre_finite)
    (D.bijectionAt A γ hγ hv)

/-! ### The inflated total space over a piece of the parameter space -/

/-- The label coordinates `(z, last w)` of an inflated representative `(z, w)`. -/
def inflatedLabelIndex (n a k : ℕ) : Fin (n + k) → Fin (n + (a + k)) :=
  Fin.append (Fin.castAdd (a + k)) (fun j => Fin.natAdd n (Fin.natAdd a j))

@[simp] theorem inflatedLabelIndex_castAdd {n a k : ℕ} (i : Fin n) :
    inflatedLabelIndex n a k (Fin.castAdd k i) = Fin.castAdd (a + k) i := Fin.append_left _ _ i

@[simp] theorem inflatedLabelIndex_natAdd {n a k : ℕ} (j : Fin k) :
    inflatedLabelIndex n a k (Fin.natAdd n j) = Fin.natAdd n (Fin.natAdd a j) := Fin.append_right _ _ j

namespace GammaWeakLiftDatum
variable {n m s : ℕ} (D : GammaWeakLiftDatum hc B n m s)

/-- The RV family of a datum, restricted to a definable set of parameters. -/
def restrictDomain (P : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaGroundDefinable hc B (inflatedGammaPower hc n) P) :
    GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawRVSpace (M := M) (D.arity + D.degree))) :=
  ⟨{z | z ∈ D.domain.carrier ∧ z.1 ∈ P}, D.domain.definable.inter (hP.preimage (universalProductFst _ _ B.real))⟩

theorem inflated_label_fibre_finite (P : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaGroundDefinable hc B (inflatedGammaPower hc n) P)
    (hfin : ∀ γ ∈ P, ∀ y, (D.labelFibre γ y).Finite) (y : Fin (n + D.degree) → CanonicalRV.RVSort M) :
    {v | v ∈ (D.restrictDomain P hP).gammaRVInflation.carrier ∧
      v ∘ inflatedLabelIndex n D.arity D.degree = y}.Finite := by
  by_cases hne : {v | v ∈ (D.restrictDomain P hP).gammaRVInflation.carrier ∧
      v ∘ inflatedLabelIndex n D.arity D.degree = y}.Nonempty
  · obtain ⟨v₀, ⟨γ₀, hγ₀, _, hP₀⟩, hy₀⟩ := hne
    have hfirst : ∀ v : Fin (n + (D.arity + D.degree)) → CanonicalRV.RVSort M,
        v ∘ inflatedLabelIndex n D.arity D.degree = y → ∀ i, v (Fin.castAdd _ i) = v₀ (Fin.castAdd _ i) := by
      intro v hv i
      have h1 := congrFun hv (Fin.castAdd D.degree i)
      have h2 := congrFun hy₀ (Fin.castAdd D.degree i)
      simp only [Function.comp_apply, inflatedLabelIndex_castAdd] at h1 h2
      rw [h1, h2]
    apply Set.Finite.of_finite_image (f := fun v => v ∘ Fin.natAdd n)
    · apply (hfin γ₀ hP₀ (y ∘ Fin.natAdd n)).subset
      rintro _ ⟨v, ⟨⟨γ, hγ, hD, _⟩, hy⟩, rfl⟩
      have hγγ : γ = γ₀ := inflated_gamma_unique
        (t := fun i => Values.vrv (v₀ (Fin.castAdd _ i))) (fun i => (hfirst v hy i) ▸ hγ i) hγ₀
      rw [hγγ] at hD
      refine ⟨hD, funext fun j => ?_⟩
      have h1 := congrFun hy (Fin.natAdd n j)
      simp only [Function.comp_apply, inflatedLabelIndex_natAdd] at h1
      exact h1
    · intro v hv w hw he
      rw [← inflated_append_split_rows v, ← inflated_append_split_rows w]
      congr 1
      · funext i
        exact (hfirst v hv.2 i).trans (hfirst w hw.2 i).symm
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

/-- The inflated weak RV object `U^inf` over a piece of the parameter space. -/
def inflatedObject (P : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaGroundDefinable hc B (inflatedGammaPower hc n) P)
    (hfin : ∀ γ ∈ P, ∀ y, (D.labelFibre γ y).Finite) : NativeWeakRVObject hc B (n + D.degree) where
  arity := n + (D.arity + D.degree)
  domain := (D.restrictDomain P hP).gammaRVInflation
  volume := GammaGroundMap.ofGlobal _ _ (inflatedRVReindexMap B.real (inflatedLabelIndex n D.arity D.degree))
    (fun _ => Set.mem_univ _)
  finite := by
    intro y
    apply ((D.inflated_label_fibre_finite P hP hfin y.val).preimage Subtype.val_injective.injOn).subset
    intro v hv
    exact ⟨v.property, congrArg Subtype.val hv⟩

theorem mem_lift_inflatedObject (P : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaGroundDefinable hc B (inflatedGammaPower hc n) P)
    (hfin : ∀ γ ∈ P, ∀ y, (D.labelFibre γ y).Finite)
    (c : (rawMixedSpace (M := M) (n + D.degree) (n + (D.arity + D.degree))).Carrier) :
    c ∈ (nativeWeakRVObjectLift (D.inflatedObject P hP hfin)).carrier ↔
      c.2 ∈ (D.restrictDomain P hP).gammaRVInflation.carrier ∧
        c.2 ∘ inflatedLabelIndex n D.arity D.degree = tupleRV c.1 := by
  constructor
  · rintro ⟨v, hv, hl⟩
    rw [← hv]
    exact ⟨v.property, hl⟩
  · rintro ⟨hc', hl⟩
    exact ⟨⟨c.2, hc'⟩, rfl, hl⟩

end GammaWeakLiftDatum

namespace GammaVFFamily
variable {n : ℕ}

/-- The part of `A^inf` whose value coordinate lies in `P`. -/
def inflatedPiece (A : GammaVFFamily hc B n) (P : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaGroundDefinable hc B (inflatedGammaPower hc n) P) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) (n + A.m) A.s) :=
  ⟨{p | ∃ γ : Fin n → Values.Gamma (M := M),
      (∀ i, Values.vrv (tupleRV (p.1 ∘ Fin.castAdd A.m) i) = (γ i).val) ∧
        (γ, (p.1 ∘ Fin.natAdd n, p.2)) ∈ A.domain.carrier ∧ γ ∈ P},
    (A.domain.definable.inter (hP.preimage (universalProductFst _ _ B.real))).exists_gamma_lift
      (inflatedValueMap B.real n A.m A.s) (inflatedSplitMap B.real n A.m A.s)⟩

theorem inflatedPiece_subset (A : GammaVFFamily hc B n) (P : Set (Fin n → Values.Gamma (M := M)))
    (hP : GammaGroundDefinable hc B (inflatedGammaPower hc n) P) :
    (A.inflatedPiece P hP).carrier ⊆ A.inflated.domain.carrier := by
  rintro p ⟨γ, hγ, hA, _⟩
  exact ⟨γ, hγ, hA⟩

/-- The graph of the uniform total bijection `A^inf ∩ vv⁻¹(P) ≅ L(U^inf)`:
retain `x`, put `z = rv x`, and apply the row bijection at `vv x`. -/
def inflatedPieceRelation (A : GammaVFFamily hc B n) (D : GammaWeakLiftDatum hc B n A.m A.s) :
    Set ((rawMixedSpace (M := M) (n + A.m) A.s).prod
      (rawMixedSpace (M := M) (n + D.degree) (n + (D.arity + D.degree)))).Carrier :=
  {z | z.2.1 ∘ Fin.castAdd D.degree = z.1.1 ∘ Fin.castAdd A.m ∧
    z.2.2 ∘ Fin.castAdd (D.arity + D.degree) = tupleRV (z.1.1 ∘ Fin.castAdd A.m) ∧
    ∃ γ : Fin n → Values.Gamma (M := M),
      (∀ i, Values.vrv (tupleRV (z.1.1 ∘ Fin.castAdd A.m) i) = (γ i).val) ∧
        (γ, ((z.1.1 ∘ Fin.natAdd n, z.1.2), (z.2.1 ∘ Fin.natAdd n, z.2.2 ∘ Fin.natAdd n))) ∈ D.graph.carrier}

theorem inflatedPieceRelation_definable (A : GammaVFFamily hc B n) (D : GammaWeakLiftDatum hc B n A.m A.s) :
    GammaGroundDefinable hc B ((rawMixedSpace (M := M) (n + A.m) A.s).prod
      (rawMixedSpace (M := M) (n + D.degree) (n + (D.arity + D.degree)))) (A.inflatedPieceRelation D) := by
  let X := rawMixedSpace (M := M) (n + A.m) A.s
  let Y := rawMixedSpace (M := M) (n + D.degree) (n + (D.arity + D.degree))
  let fstZ := universalProductFst X Y B.real
  let sndZ := universalProductSnd X Y B.real
  let fstX := universalProductFst (rawVFSpace (M := M) (n + A.m)) (rawRVSpace (M := M) A.s) B.real
  let fstY := universalProductFst (rawVFSpace (M := M) (n + D.degree))
    (rawRVSpace (M := M) (n + (D.arity + D.degree))) B.real
  let sndY := universalProductSnd (rawVFSpace (M := M) (n + D.degree))
    (rawRVSpace (M := M) (n + (D.arity + D.degree))) B.real
  have d1 := GammaGroundDefinable.diagonal_preimage (hc := hc) (B := B)
    ((inflatedVFReindexMap B.real (Fin.castAdd D.degree : Fin n → Fin (n + D.degree))).comp (fstY.comp sndZ))
    ((inflatedVFReindexMap B.real (Fin.castAdd A.m : Fin n → Fin (n + A.m))).comp (fstX.comp fstZ))
  have d2 := GammaGroundDefinable.diagonal_preimage (hc := hc) (B := B)
    ((inflatedRVReindexMap B.real (Fin.castAdd (D.arity + D.degree) : Fin n → Fin (n + (D.arity + D.degree)))).comp
      (sndY.comp sndZ))
    ((universalTupleRVMap B.real n).comp
      ((inflatedVFReindexMap B.real (Fin.castAdd A.m : Fin n → Fin (n + A.m))).comp (fstX.comp fstZ)))
  have d3 := D.graph.definable.exists_gamma_lift ((inflatedValueMap B.real n A.m A.s).comp fstZ)
    (((inflatedSplitMap B.real n A.m A.s).comp fstZ).pair
      (((inflatedVFReindexMap B.real (Fin.natAdd n : Fin D.degree → Fin (n + D.degree))).comp (fstY.comp sndZ)).pair
        ((inflatedRVReindexMap B.real (Fin.natAdd n : Fin (D.arity + D.degree) → Fin (n + (D.arity + D.degree)))).comp
          (sndY.comp sndZ))).toUniv).toUniv
  exact (d1.inter (d2.inter d3)).congr (fun _ => Iff.rfl)

/-- The uniform actual bijection between a piece of `A^inf` and the lift of
the inflated representative over that piece. -/
def inflatedPieceBijection (A : GammaVFFamily hc B n) (D : GammaWeakLiftDatum hc B n A.m A.s)
    (P : Set (Fin n → Values.Gamma (M := M))) (hP : GammaGroundDefinable hc B (inflatedGammaPower hc n) P)
    (hvalid : ∀ γ ∈ P, D.Valid A.domain.carrier γ) :
    GammaGroundBijection (A.inflatedPiece P hP)
      (nativeWeakRVObjectLift (D.inflatedObject P hP (fun γ hγ => (hvalid γ hγ).labelFibre_finite))) := by
  refine inflatedRelationBijection (A.inflatedPieceRelation D) (A.inflatedPieceRelation_definable D) ?_ ?_ ?_
  · rintro p ⟨γ, hγ, hA, hPγ⟩
    obtain ⟨q', hq', hu⟩ := (hvalid γ hPγ).total _ hA
    refine ⟨(Fin.append (p.1 ∘ Fin.castAdd A.m) q'.1, Fin.append (tupleRV (p.1 ∘ Fin.castAdd A.m)) q'.2),
      ⟨inflated_append_comp_castAdd _ _, inflated_append_comp_castAdd _ _, γ, hγ, ?_⟩, ?_⟩
    · change (γ, ((p.1 ∘ Fin.natAdd n, p.2), (Fin.append (p.1 ∘ Fin.castAdd A.m) q'.1 ∘ Fin.natAdd n,
        Fin.append (tupleRV (p.1 ∘ Fin.castAdd A.m)) q'.2 ∘ Fin.natAdd n))) ∈ D.graph.carrier
      rw [inflated_append_comp_natAdd, inflated_append_comp_natAdd]
      exact hq'
    · rintro c ⟨h1, h2, γ', hγ', hg⟩
      have hγγ : γ' = γ := inflated_gamma_unique hγ' hγ
      rw [hγγ] at hg
      have hq'' := hu _ hg
      refine Prod.ext ?_ ?_
      · change c.1 = Fin.append (p.1 ∘ Fin.castAdd A.m) q'.1
        rw [← inflated_append_split_rows c.1, h1, ← congrArg Prod.fst hq'']
      · change c.2 = Fin.append (tupleRV (p.1 ∘ Fin.castAdd A.m)) q'.2
        rw [← inflated_append_split_rows c.2, h2, ← congrArg Prod.snd hq'']
  · rintro p ⟨γ, hγ, _, hPγ⟩ c ⟨h1, h2, γ', hγ', hg⟩
    have hγγ : γ' = γ := inflated_gamma_unique hγ' hγ
    rw [hγγ] at hg
    obtain ⟨_, hl1, hl2⟩ := (hvalid γ hPγ).maps _ _ hg
    apply (D.mem_lift_inflatedObject P hP _ c).mpr
    refine ⟨⟨γ, fun i => ?_, ⟨hl1, hPγ⟩⟩, funext fun j => ?_⟩
    · rw [show c.2 (Fin.castAdd _ i) = tupleRV (p.1 ∘ Fin.castAdd A.m) i from congrFun h2 i]
      exact hγ i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have e1 := congrFun h1 i
        have e2 := congrFun h2 i
        simp only [Function.comp_apply] at e1 e2
        simp only [Function.comp_apply, inflatedLabelIndex_castAdd]
        rw [e2]
        change CanonicalRV.encodedRv (p.1 (Fin.castAdd A.m i)) = CanonicalRV.encodedRv (c.1 (Fin.castAdd D.degree i))
        rw [e1]
      · have e3 := congrFun hl2 i
        simp only [Function.comp_apply] at e3
        simp only [Function.comp_apply, inflatedLabelIndex_natAdd]
        exact e3
  · intro c hc'
    obtain ⟨⟨γ, hγ, hD, hPγ⟩, hlab⟩ := (D.mem_lift_inflatedObject P hP _ c).mp hc'
    have hv := hvalid γ hPγ
    have hfirst : c.2 ∘ Fin.castAdd (D.arity + D.degree) = tupleRV (c.1 ∘ Fin.castAdd D.degree) :=
      funext fun i => by
        have h := congrFun hlab (Fin.castAdd D.degree i)
        simp only [Function.comp_apply, inflatedLabelIndex_castAdd] at h
        exact h
    have hlast : (c.2 ∘ Fin.natAdd n) ∘ Fin.natAdd D.arity = tupleRV (c.1 ∘ Fin.natAdd n) :=
      funext fun j => by
        have h := congrFun hlab (Fin.natAdd n j)
        simp only [Function.comp_apply, inflatedLabelIndex_natAdd] at h
        exact h
    have hrow : (c.1 ∘ Fin.natAdd n, c.2 ∘ Fin.natAdd n) ∈ D.liftRow γ := ⟨hD, hlast⟩
    obtain ⟨q, hq, hqu⟩ := hv.onto _ hrow
    have hAq := (hv.maps _ _ hq).1
    let p : (rawMixedSpace (M := M) (n + A.m) A.s).Carrier := (Fin.append (c.1 ∘ Fin.castAdd D.degree) q.1, q.2)
    have hx₀ : p.1 ∘ Fin.castAdd A.m = c.1 ∘ Fin.castAdd D.degree := inflated_append_comp_castAdd _ _
    have hγp : ∀ i, Values.vrv (tupleRV (p.1 ∘ Fin.castAdd A.m) i) = (γ i).val := fun i => by
      rw [hx₀, ← congrFun hfirst i]
      exact hγ i
    have hqp : (p.1 ∘ Fin.natAdd n, p.2) = q := Prod.ext (inflated_append_comp_natAdd _ _) rfl
    refine ⟨p, ⟨⟨γ, hγp, by rw [hqp]; exact hAq, hPγ⟩, ⟨hx₀.symm, by rw [hx₀]; exact hfirst, γ, hγp, ?_⟩⟩, ?_⟩
    · change (γ, ((p.1 ∘ Fin.natAdd n, p.2), (c.1 ∘ Fin.natAdd n, c.2 ∘ Fin.natAdd n))) ∈ D.graph.carrier
      rw [hqp]
      exact hq
    · rintro p' ⟨_, ⟨h1', _, γ'', hγ'', hg'⟩⟩
      have hx' : p'.1 ∘ Fin.castAdd A.m = c.1 ∘ Fin.castAdd D.degree := h1'.symm
      have hγ2 : γ'' = γ := inflated_gamma_unique hγ'' (fun i => by
        rw [hx', ← congrFun hfirst i]
        exact hγ i)
      rw [hγ2] at hg'
      have hq' := hqu _ hg'
      refine Prod.ext ?_ ?_
      · change p'.1 = Fin.append (c.1 ∘ Fin.castAdd D.degree) q.1
        rw [← inflated_append_split_rows p'.1, hx', ← congrArg Prod.fst hq']
      · change p'.2 = q.2
        exact congrArg Prod.snd hq'

theorem inflatedPiece_partition (A : GammaVFFamily hc B n) {K : ℕ}
    (P : Fin K → Set (Fin n → Values.Gamma (M := M)))
    (hP : ∀ l, GammaGroundDefinable hc B (inflatedGammaPower hc n) (P l))
    (hdisj : ∀ l l', l ≠ l' → Disjoint (P l) (P l')) (hcov : ∀ γ, ∃ l, γ ∈ P l) :
    (∀ l l', l ≠ l' → Disjoint (A.inflatedPiece (P l) (hP l)).carrier (A.inflatedPiece (P l') (hP l')).carrier) ∧
      ∀ p, p ∈ A.inflated.domain.carrier ↔ ∃ l, p ∈ (A.inflatedPiece (P l) (hP l)).carrier := by
  refine ⟨fun l l' hne => Set.disjoint_left.mpr ?_, fun p => ⟨?_, ?_⟩⟩
  · rintro p ⟨γ, hγ, _, hPγ⟩ ⟨γ', hγ', _, hPγ'⟩
    rw [inflated_gamma_unique hγ hγ'] at hPγ
    exact Set.disjoint_left.mp (hdisj l l' hne) hPγ hPγ'
  · rintro ⟨γ, hγ, hA⟩
    obtain ⟨l, hl⟩ := hcov γ
    exact ⟨l, γ, hγ, hA, hl⟩
  · rintro ⟨l, hp⟩
    exact A.inflatedPiece_subset (P l) (hP l) hp

/-! ### Values -/

/-- Emptiness of rows is detected by the representatives, at every parameter. -/
theorem row_empty_iff (A : GammaVFFamily hc B n) {K : ℕ} (D : Fin K → GammaWeakLiftDatum hc B n A.m A.s)
    (P : Fin K → Set (Fin n → Values.Gamma (M := M)))
    (hP : ∀ l, GammaGroundDefinable hc B (inflatedGammaPower hc n) (P l))
    (hdisj : ∀ l l', l ≠ l' → Disjoint (P l) (P l')) (hcov : ∀ γ, ∃ l, γ ∈ P l)
    (hvalid : ∀ l γ, γ ∈ P l → (D l).Valid A.domain.carrier γ) (γ : Fin n → Values.Gamma (M := M)) :
    A.row γ = ∅ ↔ ∀ l, (((D l).restrictDomain (P l) (hP l)).gammaFibreOver γ).carrier = ∅ := by
  obtain ⟨l₀, hl₀⟩ := hcov γ
  have hv := hvalid l₀ γ hl₀
  constructor
  · intro hrow l
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hw, hPl⟩
    have hl : l = l₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj l l₀ hne) hPl hl₀
    subst hl
    obtain ⟨b, hb⟩ := tupleRV_surjective (w ∘ Fin.natAdd (D l).arity)
    obtain ⟨q, hq, _⟩ := hv.onto (b, w) ⟨hw, hb.symm⟩
    have hqrow : q ∈ A.row γ := (hv.maps q (b, w) hq).1
    rw [hrow] at hqrow
    exact hqrow
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨q', hq', _⟩ := hv.total q hq
    have hl := (hv.maps q q' hq').2
    have hmem : q'.2 ∈ (((D l₀).restrictDomain (P l₀) (hP l₀)).gammaFibreOver γ).carrier := ⟨hl.1, hl₀⟩
    rw [h l₀] at hmem
    exact hmem

/-- Fibre values at definable parameters, as a sum over the pieces. -/
theorem fibre_value_sum (G : GammaGroundContext M) (A : GammaVFFamily hc G.base n) {K : ℕ}
    (D : Fin K → GammaWeakLiftDatum hc G.base n A.m A.s) (P : Fin K → Set (Fin n → Values.Gamma (M := M)))
    (hP : ∀ l, GammaGroundDefinable hc G.base (inflatedGammaPower hc n) (P l))
    (hdisj : ∀ l l', l ≠ l' → Disjoint (P l) (P l')) (hcov : ∀ γ, ∃ l, γ ∈ P l)
    (hvalid : ∀ l γ, γ ∈ P l → (D l).Valid A.domain.carrier γ)
    (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, GammaDefinableClosureAtBase G.base (γ i)) :
    section5BoundedVFIntegral G hc (nativeVFClass (A.fibreAt γ hγ)) =
      ∑ l, section5BoundedRVSetValue G hc (((D l).restrictDomain (P l) (hP l)).gammaFibre γ hγ) := by
  obtain ⟨l₀, hl₀⟩ := hcov γ
  rw [Finset.sum_eq_single l₀]
  · refine ((D l₀).fibre_value G A γ hγ (hvalid l₀ γ hl₀)).trans (congrArg (section5BoundedRVSetValue G hc) ?_)
    apply GammaGroundDefSet.eq_of_carrier_eq
    ext w
    exact ⟨fun h => ⟨h, hl₀⟩, fun h => h.1⟩
  · intro l _ hne
    apply nativeRVSetValue_of_empty
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨_, hPl⟩
    exact Set.disjoint_left.mp (hdisj l l₀ hne) hPl hl₀
  · intro h
    exact absurd (Finset.mem_univ l₀) h

/-- The value of the inflated total space, as a sum over the pieces. -/
theorem inflated_value_sum (G : GammaGroundContext M) (A : GammaVFFamily hc G.base n) {K : ℕ}
    (D : Fin K → GammaWeakLiftDatum hc G.base n A.m A.s) (P : Fin K → Set (Fin n → Values.Gamma (M := M)))
    (hP : ∀ l, GammaGroundDefinable hc G.base (inflatedGammaPower hc n) (P l))
    (hdisj : ∀ l l', l ≠ l' → Disjoint (P l) (P l')) (hcov : ∀ γ, ∃ l, γ ∈ P l)
    (hvalid : ∀ l γ, γ ∈ P l → (D l).Valid A.domain.carrier γ) :
    section5BoundedVFIntegral G hc (nativeVFClass A.inflated) =
      ∑ l, section5BoundedRVSetValue G hc ((D l).restrictDomain (P l) (hP l)).gammaRVInflation := by
  obtain ⟨hd, hcv⟩ := A.inflatedPiece_partition P hP hdisj hcov
  rw [nativeVFClass_finite_partition A.inflated (fun l => A.inflatedPiece (P l) (hP l)) hd hcv, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact nativeVFBoundedValue_of_weak_lift_bijection GammaQE.gamma_piecewise_rational_affine
    (completed18GroundLiftInput G hc) _
    ((D l).inflatedObject (P l) (hP l) (fun γ hγ => (hvalid l γ hγ).labelFibre_finite))
    (A.inflatedPieceBijection (D l) (P l) (hP l) (hvalid l))

/-- **Uniform RV representatives over Gamma parameters.**
There are finitely many definable RV families `U l ⊆ Γ^n × RV^{r l}`, lying
over the pieces of a definable partition `(P l)` of `Γ^n`, which compute the
bounded integral of every row at a parameter with definable coordinates and of
the inflated total space. Emptiness of rows is detected at every parameter. -/
theorem uniform_representatives (G : GammaGroundContext M) (A : GammaVFFamily hc G.base n) :
    ∃ (K : ℕ) (r : Fin K → ℕ)
      (U : ∀ l, GammaGroundDefSet hc G.base ((inflatedGammaPower hc n).prod (rawRVSpace (M := M) (r l))))
      (P : Fin K → Set (Fin n → Values.Gamma (M := M))),
      (∀ l, GammaGroundDefinable hc G.base (inflatedGammaPower hc n) (P l)) ∧
      (∀ l, Section4.GammaOrderLogic.GammaDefinable G.base (P l)) ∧
      (∀ l l', l ≠ l' → Disjoint (P l) (P l')) ∧ (∀ γ, ∃ l, γ ∈ P l) ∧
      (∀ l γ w, (γ, w) ∈ (U l).carrier → γ ∈ P l) ∧
      (∀ γ, A.row γ = ∅ ↔ ∀ l, ((U l).gammaFibreOver γ).carrier = ∅) ∧
      (∀ l γ (hγ : ∀ i, GammaDefinableClosureAtBase G.base (γ i)), γ ∈ P l →
        section5BoundedVFIntegral G hc (nativeVFClass (A.fibreAt γ hγ)) =
          section5BoundedRVSetValue G hc ((U l).gammaFibre γ hγ)) ∧
      (∀ γ (hγ : ∀ i, GammaDefinableClosureAtBase G.base (γ i)),
        section5BoundedVFIntegral G hc (nativeVFClass (A.fibreAt γ hγ)) =
          ∑ l, section5BoundedRVSetValue G hc ((U l).gammaFibre γ hγ)) ∧
      section5BoundedVFIntegral G hc (nativeVFClass A.inflated) =
        ∑ l, section5BoundedRVSetValue G hc (U l).gammaRVInflation := by
  obtain ⟨K, D, P, hP, hdisj, hcov, hvalid⟩ :=
    A.uniform_lift_catalog G.model00 G.uncountable G.saturated G.small_real G.small_gamma
  refine ⟨K, fun l => (D l).arity + (D l).degree, fun l => (D l).restrictDomain (P l) (hP l), P, hP,
    fun l => (Section4.Section3GammaCodeBridge.native_iff (hc := hc) (P l)).mp (hP l), hdisj, hcov,
    fun l γ w h => h.2, A.row_empty_iff D P hP hdisj hcov hvalid, ?_,
    A.fibre_value_sum G D P hP hdisj hcov hvalid, A.inflated_value_sum G D P hP hdisj hcov hvalid⟩
  intro l γ hγ hl
  refine ((D l).fibre_value G A γ hγ (hvalid l γ hl)).trans (congrArg (section5BoundedRVSetValue G hc) ?_)
  apply GammaGroundDefSet.eq_of_carrier_eq
  ext w
  exact ⟨fun h => ⟨h, hl⟩, fun h => h.1⟩

end GammaVFFamily

end DiamondIntegral.Section5
