import «section 7».TautologicalContractions
import «section 7».FirstStageObjects
import «section 7».StageBaseChange
import «section 7».RestrictContractions
import «section 7».SliceClasses

/-! Contractions of the fibres over the first contracted coordinate (for
Proposition 7.24).

Let `G₀` be a normalized contraction of an object `A` of `μVF^◇[n + 2]` with first
stage `H` and leading label `ℓ`. For a VF value `a` of the contracted coordinate,
the fibre of the lifted first-stage target at `a` is the label slice
`L(a) = {(z, t) ∈ firstSet G₀ | t_ℓ = rv(a)}` (`mem_sliceAt`), an object of
`μVF^◇[n + 1]` over `S⟨a⟩` (`sliceObjAt`): its form is covariant
(`FirstStageObjects.firstForm_covariant`) and its RV fibres are finite (the first
stage set has finite fibres modulo `ℓ`).

For a normalized contraction `K` of the first-stage set (any order), moving `K`
to the base `S⟨a⟩` (`StageBaseChange.extendContraction`) and restricting it to the
label-saturated piece `L(a)` (`RestrictContractions.restrictContraction`) gives a
normalized contraction `contractionAt K a` of `L(a)`. Its RV target is the fibre at
`a` of the bundle `B_K = {(x, w) | w ∈ U_K, rv(x) = w_{ℓ'}}` over the RV target
`U_K` of `K`, with `ℓ'` the label carrying `ℓ` (`mem_contractionAt_target`), and its
class is the class of the fibre object of `B_K` at `a` with the volume labels of
`K` (`cls_contractionAt`). This is the fibre hypothesis of Lemma 7.14 with one VF
coordinate, applied to the bundles of two contractions of the first-stage set. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.FibreContractions
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.TautologicalContractions DiamondIntegral.Section7.FirstStageObjects
open DiamondIntegral.Section7.StageBaseChange DiamondIntegral.Section7.RestrictContractions
open DiamondIntegral.Section7.SliceContractions DiamondIntegral.Section7.Corollary715
open DiamondIntegral.Section7.PieceCombination

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### Finitely many labels -/

theorem finite_labels {S : Set M} {a q k : ℕ} {X : DefSet (rawMixedSpace (M := M) a q) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} {ν : Fin a → Fin q}
    (hX : ∀ p : Mixed M a q, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (ν i))
    (l : Fin k → Fin q) (hT : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hfin : (preparedHeadStartRVObject X k l hT).volume.FiniteFibres) (t : Fin (a + k) → RVInfinity M) :
    {u : Fin q → RVInfinity M | ((Fin.elim0, u) : Mixed M 0 q) ∈ U.carrier ∧
      (fun i => u (Fin.append ν l i)) = t}.Finite := by
  by_cases hne : ∃ u₀, ((Fin.elim0, u₀) : Mixed M 0 q) ∈ U.carrier ∧ (fun i => u₀ (Fin.append ν l i)) = t
  · obtain ⟨u₀, hu₀, ht₀⟩ := hne
    let d₀ : (preparedHeadStartRVObject X k l hT).domain := ⟨u₀, (mem_domain_labels hX l hT u₀).mpr hu₀⟩
    refine ((hfin ((preparedHeadStartRVObject X k l hT).volume d₀)).image Subtype.val).subset ?_
    rintro u ⟨hu, hut⟩
    refine ⟨⟨u, (mem_domain_labels hX l hT u).mpr hu⟩, ?_, rfl⟩
    apply Subtype.ext
    change (preparedHeadStartRVObject X k l hT).value _ = (preparedHeadStartRVObject X k l hT).value d₀
    rw [value_labels hX l hT, value_labels hX l hT]
    exact hut.trans ht₀.symm
  · exact Set.finite_empty.subset (fun u hu => hne ⟨u, hu⟩)

theorem label_ne_zero_of_rvBounded {S : Set M} {n q : ℕ} {U : DefSet (rawMixedSpace (M := M) n q) S}
    (hU : ProperInvariant S U.carrier) {p : Mixed M n q} (hp : p ∈ U.carrier) (i : Fin q) :
    (p.2 i).val ≠ iRVZero := by
  intro h0
  obtain ⟨γ, hγ⟩ := hU.rvBounded
  have hb := (hγ p hp i).2
  rw [(Values.vrv_eq_infinity_iff _).mpr h0] at hb
  exact γ.property (le_antisymm (Values.le_infinity _) hb)

/-! ### The bundle of a contraction -/

section Bundle
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {N r : ℕ} {X : DefSet (rawMixedSpace (M := M) (N + 1) r) (T : Set M)}
variable {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (N + 1))}
variable (K : NormalizedMeasuredContraction (G := G) X ω e) (ℓ : Fin r)

/-- The bundle of a contraction over its RV target, along the label carrying `ℓ`. -/
abbrev kBundle := rvCoordinateBundle K.preparedContraction.data.rvTarget (K.oldIndex ℓ)

include h00 hc hκ hs hv in
theorem rvTarget_proper : ProperInvariant (T : Set M) K.preparedContraction.data.rvTarget.carrier :=
  K.preparedContraction.data.program.target_proper
    (reindexedVFSet_properInvariant _ e (K.normalization.image_properInvariant h00 hc hκ hs hv))

include h00 hc hκ hs hv in
theorem kBundle_proper : ProperInvariant (T : Set M) (kBundle K ℓ).carrier :=
  rvCoordinateBundle_properInvariant h00 hc hκ hs hv _ _ (rvTarget_proper h00 hc hκ hs hv K)

include h00 hc hκ hs hv in
theorem kBundle_nonzero :
    ∀ p ∈ (kBundle K ℓ).carrier, ∀ i, (p.2 (K.preparedContraction.data.program.volumeIndex i)).val ≠ iRVZero :=
  fun p hp i => label_ne_zero_of_rvBounded (rvTarget_proper h00 hc hκ hs hv K) ((mem_bundle _ _ p).mp hp).1
    (K.preparedContraction.data.program.volumeIndex i)

include h00 hc linear hκ hs hv hsmall hΓ in
theorem kBundle_hFin
    (hFin : ∀ (a : Fin (N + 1) → VF M) (t : Fin 1 → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ ![ℓ] = t}.Finite) :
    ∀ (a : Fin 1 → VF M) (t : Fin (N + 1) → RVInfinity M),
      {u | (a, u) ∈ (kBundle K ℓ).carrier ∧ u ∘ K.preparedContraction.data.program.volumeIndex = t}.Finite := by
  intro a t
  have hfin := K.headStartObject_finite_volume h00 hc linear hκ hs hv hsmall hΓ 1 ![ℓ] hFin
  refine (finite_labels K.preparedContraction.lift.originalTarget_recover (K.oldIndex ∘ ![ℓ]) K.target_tagged hfin
    (Fin.append (fun i => t (e.symm i)) ![rv M (a 0)])).subset ?_
  rintro u ⟨hu, hut⟩
  obtain ⟨hU, hrv⟩ := (mem_bundle _ _ (a, u)).mp hu
  refine ⟨hU, funext fun i => ?_⟩
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left, Fin.append_left]
    exact congrFun hut (e.symm i)
  | right j =>
    rw [Fin.append_right, Fin.append_right, Fin.fin_one_eq_zero j]
    exact hrv.symm

end Bundle

/-! ### The slice of a set at its last coordinate -/

section LastSlice
variable {S S' : Set M} {n r : ℕ}

/-- The codes of `(x, t) ↦ ((x, a), t)`. -/
def lastCodes (a : VF M) (z : Fin n ⊕ Fin r → M) : Fin (n + 1) ⊕ Fin r → M :=
  Sum.elim (Fin.snoc (α := fun _ => M) (z ∘ Sum.inl) a.val) (z ∘ Sum.inr)

omit [M ⊨ Axioms.ACVF] in
theorem lastCodes_definable (a : VF M) (ha : a.val ∈ S') :
    S'.DefinableMap LRV (lastCodes (n := n) (r := r) a) := by
  rintro (i | i)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · have he : (fun z : Fin n ⊕ Fin r → M => lastCodes a z (.inl (Fin.last n))) = fun _ => a.val := by
        funext z
        simp [lastCodes]
      rw [he]
      exact LRV.definableFun_const _ ha
    · have he : (fun z : Fin n ⊕ Fin r → M => lastCodes a z (.inl j.castSucc)) = fun z => z (.inl j) := by
        funext z
        simp [lastCodes]
      rw [he]
      exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV

omit [M ⊨ Axioms.ACVF] in
theorem lastCodes_mixedValues (a : VF M) (p : Mixed M n r) :
    lastCodes a (mixedValues p) = mixedValues ((Fin.snoc p.1 a, p.2) : Mixed M (n + 1) r) := by
  funext i
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [lastCodes, mixedValues, vfValues]
    · simp [lastCodes, mixedValues, vfValues]
  · rfl

omit [M ⊨ Axioms.ACVF] in
theorem lastCodes_decode (a : VF M) (c : (rawMixedSpace (M := M) n r).domain) :
    lastCodes a c.val = mixedValues
      ((Fin.snoc ((rawMixedSpace (M := M) n r).decode c).1 a, ((rawMixedSpace (M := M) n r).decode c).2) :
        Mixed M (n + 1) r) := by
  rw [← lastCodes_mixedValues, mixedValues_decode]

/-- The definable map `(x, t) ↦ ((x, a), t)` over `S'`. -/
def lastMap (a : VF M) (ha : a.val ∈ S') :
    Map (DefSet.univ (rawMixedSpace (M := M) n r) S') (DefSet.univ (rawMixedSpace (M := M) (n + 1) r) S') :=
  Map.ofCodes _ (fun p : Mixed M n r => ((Fin.snoc p.1 a, p.2) : Mixed M (n + 1) r))
    (lastCodes a) (lastCodes_definable a ha)
    (fun c => (lastCodes_decode a c) ▸ mixedValues_mem_domain _)
    (fun c => mixedValues_injective ((mixedValues_decode _).trans (lastCodes_decode a c)))

/-- The slice `{(x, t) | ((x, a), t) ∈ X}` over `S'`. -/
def lastSlice (X : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (a : VF M) (hSS : S ⊆ S') (ha : a.val ∈ S') :
    DefSet (rawMixedSpace (M := M) n r) S' where
  carrier := {p | ((Fin.snoc p.1 a, p.2) : Mixed M (n + 1) r) ∈ X.carrier}
  definable := by
    have h := (lastMap (n := n) (r := r) a ha).definable_preimage (X.definable.mono _ hSS)
    convert h using 1
    ext p
    constructor
    · intro hp
      exact ⟨⟨p, Set.mem_univ _⟩, rfl, hp⟩
    · rintro ⟨q, rfl, hq⟩
      exact hq

omit [M ⊨ Axioms.ACVF] in
theorem mem_lastSlice (X : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (a : VF M) (hSS : S ⊆ S') (ha : a.val ∈ S')
    (p : Mixed M n r) : p ∈ (lastSlice X a hSS ha).carrier ↔ ((Fin.snoc p.1 a, p.2) : Mixed M (n + 1) r) ∈ X.carrier :=
  Iff.rfl

end LastSlice

/-! ### The fibre object and the restricted contractions -/

section Fibre
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1)} {σ : Equiv.Perm (Fin (n + 1 + 1))}
variable (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ) (a : VF M)

/-- The point `a` as a tuple. -/
abbrev ptA (a : VF M) : Fin 1 → VF M := fun _ => a

theorem a_mem : a.val ∈ (adjoin T (ptA a) : Set M) := coordinate_mem_adjoin (ptA a) 0

theorem T_sub : (T : Set M) ⊆ adjoin T (ptA a) := subset_adjoin _

/-- **The fibre at `a`**: the slice of the lifted first-stage target at the last
coordinate `a`. -/
def sliceAt : DefSet (rawMixedSpace (M := M) (n + 1) (stage G₀).arity) (adjoin T (ptA a) : Set M) :=
  lastSlice (stage G₀).target a (T_sub a) (a_mem a)

theorem mem_sliceAt (p : Mixed M (n + 1) (stage G₀).arity) :
    p ∈ (sliceAt G₀ a).carrier ↔ p ∈ (firstSet G₀).carrier ∧ rv M a = p.2 (stage G₀).leading := by
  rw [sliceAt, mem_lastSlice, (stage G₀).recover_target]
  simp only [Fin.init_snoc, Fin.snoc_last, Prod.mk.eta]

theorem sliceAt_saturated : LabelSaturated (sliceAt G₀ a) (extendDefSetBase (T_sub a) (firstSet G₀)) :=
  ⟨fun p hp => ((mem_sliceAt G₀ a p).mp hp).1, fun p _ q hq hpq hp =>
    (mem_sliceAt G₀ a q).mpr ⟨hq, by rw [← hpq]; exact ((mem_sliceAt G₀ a p).mp hp).2⟩⟩

theorem sliceAt_proper : ProperInvariant (adjoin T (ptA a) : Set M) (sliceAt G₀ a).carrier := by
  have hF := (stage G₀).contracted_proper
  have hsub : (sliceAt G₀ a).carrier ⊆ (firstSet G₀).carrier := fun p hp => ((mem_sliceAt G₀ a p).mp hp).1
  refine ⟨(sliceAt G₀ a).definable, hF.vfBounded.mono hsub, hF.rvBounded.mono hsub, fun u => ?_⟩
  obtain ⟨α, hα, hinv⟩ := hF.radii u
  refine ⟨α, FibreRestriction.namedRadii_mono hα (T_sub a), fun x y hxy => ?_⟩
  change (x, u) ∈ (sliceAt G₀ a).carrier ↔ (y, u) ∈ (sliceAt G₀ a).carrier
  rw [mem_sliceAt, mem_sliceAt]
  exact and_congr_left (fun _ => hinv x y hxy)

/-- **The fibre object at `a`**, an object of `μVF^◇[n + 1]` over `S⟨a⟩`. -/
def sliceObjAt : VFObject (M := M) (adjoin T (ptA a) : Set M) (n + 1) where
  labels := (stage G₀).arity
  carrier := sliceAt G₀ a
  form := (extendMapBase (T_sub a) (firstForm G₀)).restrict (sliceAt_saturated G₀ a).1
  proper := sliceAt_proper G₀ a
  formCovariant t := by
    obtain ⟨β, hβ, h⟩ := firstForm_covariant h00 hc hκ hs hv G₀ t
    refine ⟨β, FibreRestriction.namedRadii_mono hβ (T_sub a), fun x y hx hy hxy => ?_⟩
    exact h x y ((mem_sliceAt G₀ a _).mp hx).1 ((mem_sliceAt G₀ a _).mp hy).1 hxy
  finiteRV x := by
    refine (firstFin hc h00 hκ hs hsmall G₀ x (fun _ => rv M a)).subset ?_
    intro u hu
    obtain ⟨h1, h2⟩ := (mem_sliceAt G₀ a _).mp hu
    exact ⟨h1, funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h2.symm⟩

variable {e : Equiv.Perm (Fin (n + 1))} (K : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) e)

/-- **The restricted contraction**: `K` moved to `S⟨a⟩` and restricted to the fibre. -/
def contractionAt : NormalizedMeasuredContraction (G := G) (sliceObjAt h00 hc hκ hs hv hsmall G₀ a).carrier
    (sliceObjAt h00 hc hκ hs hv hsmall G₀ a).form e :=
  restrictContraction h00 hc lin hκ hs hv (adjoin_small hκ hsmall (ptA a)) (adjoin_gamma hΓ (ptA a))
    (extendContraction (T_sub a) h00 hc lin hκ hs hv (adjoin_small hκ hsmall (ptA a)) (adjoin_gamma hΓ (ptA a)) K)
    (sliceAt G₀ a) (sliceAt_saturated G₀ a) (sliceAt_proper G₀ a)

theorem label_of_point (D : ZeroCenteredData (firstSet G₀)) {p : Mixed M (n + 1) (stage G₀).arity}
    {y : Mixed M (n + 1) ((n + 1) + (stage G₀).arity)} (hpe : D.point p = reindexVFPoint e.symm y) :
    y.2 (Fin.natAdd (n + 1) (stage G₀).leading) = p.2 (stage G₀).leading := by
  have h := congrArg (fun z : Mixed M (n + 1) ((n + 1) + (stage G₀).arity) =>
    z.2 (Fin.natAdd (n + 1) (stage G₀).leading)) hpe
  simp only [ZeroCenteredData.point, ZeroCenteredData.tags, Fin.append_right, reindexVFPoint] at h
  exact h.symm

/-- The RV target of the restricted contraction is the fibre of the bundle of `K`. -/
theorem mem_contractionAt_target (w : Fin K.preparedContraction.data.arity → RVInfinity M) :
    ((Fin.elim0, w) : Mixed M 0 _) ∈
        (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ a K).preparedContraction.data.rvTarget.carrier ↔
      ((Fin.elim0, w) : Mixed M 0 _) ∈ K.preparedContraction.data.rvTarget.carrier ∧
        rv M a = w (K.oldIndex (stage G₀).leading) := by
  unfold contractionAt
  rw [mem_restrictContraction_target]
  constructor
  · rintro ⟨y, hy, hyw⟩
    have hy' : y.val ∈ (reindexedVFSet K.normalization.map.image e).carrier := by
      rw [← StageBaseChange.prepared_carrier (T_sub a) K.normalization e]
      exact y.property
    let y' : reindexedVFSet K.normalization.map.image e := ⟨y.val, hy'⟩
    have htm := extendContraction_toMap (T_sub a) h00 hc lin hκ hs hv (adjoin_small hκ hsmall (ptA a))
      (adjoin_gamma hΓ (ptA a)) K y y' rfl
    rw [hyw] at htm
    refine ⟨htm ▸ (K.preparedContraction.data.program.toMap y').property, ?_⟩
    obtain ⟨p, hp, hpe⟩ := (mem_prepared_restrict _ e _ _ _ y.val).mp hy
    have hret := K.preparedContraction.data.program.retained y' (Fin.natAdd (n + 1) (stage G₀).leading)
    rw [← htm] at hret
    have hlab := label_of_point G₀ K.normalization hpe
    exact ((mem_sliceAt G₀ a p).mp hp).2.trans (hlab.symm.trans hret.symm)
  · rintro ⟨hw, hrv⟩
    obtain ⟨y', hy'⟩ := K.preparedContraction.data.program.surjective ⟨_, hw⟩
    obtain ⟨p, hp, hpe⟩ := (mem_prepared K.normalization e y'.val).mp y'.property
    have hret := K.preparedContraction.data.program.retained y' (Fin.natAdd (n + 1) (stage G₀).leading)
    rw [hy'] at hret
    have hlab := label_of_point G₀ K.normalization hpe
    have hpS : p ∈ (sliceAt G₀ a).carrier := (mem_sliceAt G₀ a p).mpr ⟨hp, hrv.trans (hret.trans hlab)⟩
    have hyE : y'.val ∈ (reindexedVFSet (extendCentered (T_sub a) K.normalization).map.image e).carrier := by
      rw [StageBaseChange.prepared_carrier (T_sub a) K.normalization e]
      exact y'.property
    refine ⟨⟨y'.val, hyE⟩, (mem_prepared_restrict _ e _ _ _ y'.val).mpr ⟨p, hpS, hpe⟩, ?_⟩
    exact (extendContraction_toMap (T_sub a) h00 hc lin hκ hs hv (adjoin_small hκ hsmall (ptA a))
      (adjoin_gamma hΓ (ptA a)) K ⟨y'.val, hyE⟩ y' rfl).trans (congrArg Subtype.val hy')

theorem contractionAt_volumeIndex :
    (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ a K).preparedContraction.data.program.volumeIndex =
      K.preparedContraction.data.program.volumeIndex :=
  (restrictContraction_volumeIndex h00 hc lin hκ hs hv (adjoin_small hκ hsmall (ptA a)) (adjoin_gamma hΓ (ptA a))
    (extendContraction (T_sub a) h00 hc lin hκ hs hv (adjoin_small hκ hsmall (ptA a)) (adjoin_gamma hΓ (ptA a)) K)
    (sliceAt G₀ a) (sliceAt_saturated G₀ a) (sliceAt_proper G₀ a)).trans
    (extendContraction_volumeIndex (T_sub a) h00 hc lin hκ hs hv (adjoin_small hκ hsmall (ptA a))
      (adjoin_gamma hΓ (ptA a)) K)

/-- **The class of the restricted contraction** is the class of the fibre object of
the bundle of `K` at `a`, with the volume labels of `K`. -/
theorem cls_contractionAt
    (hFinB : ∀ t : Fin (n + 1) → RVInfinity M, {u | (ptA a, u) ∈ (kBundle K (stage G₀).leading).carrier ∧
      u ∘ K.preparedContraction.data.program.volumeIndex = t}.Finite)
    (hNZB : ∀ p ∈ (kBundle K (stage G₀).leading).carrier, ∀ i,
      (p.2 (K.preparedContraction.data.program.volumeIndex i)).val ≠ iRVZero)
    (hdF : (fibreObject T (kBundle K (stage G₀).leading)
      (bundleForm _ _ K.preparedContraction.data.rvForm) (ptA a) K.preparedContraction.data.program.volumeIndex
        hFinB hNZB).doublyBounded) :
    clsOf h00 hc hκ hs hv (adjoin_small hκ hsmall (ptA a)) (adjoin_gamma hΓ (ptA a))
        (sliceObjAt h00 hc hκ hs hv hsmall G₀ a) (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ a K) =
      cls (objOf hc (adjoin T (ptA a)) (fibreObject T (kBundle K (stage G₀).leading)
        (bundleForm _ _ K.preparedContraction.data.rvForm) (ptA a) K.preparedContraction.data.program.volumeIndex
          hFinB hNZB) hdF) := by
  have hprod : ∀ f : Fin K.preparedContraction.data.arity → Gamma M,
      ∏ i : Fin ((n + 1) + 0), f (Fin.append
        (fun i => (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ a K).preparedContraction.data.program.volumeIndex
          (e.symm i))
        ((contractionAt h00 hc hκ hs hv hsmall hΓ G₀ a K).oldIndex ∘ (Fin.elim0 : Fin 0 → Fin (stage G₀).arity)) i) =
      ∏ i, f (K.preparedContraction.data.program.volumeIndex i) := by
    intro f
    rw [Fin.prod_univ_add (a := n + 1) (b := 0), Fin.prod_univ_zero, mul_one]
    simp only [Fin.append_left]
    rw [contractionAt_volumeIndex]
    exact Equiv.prod_comp e.symm (fun i => f (K.preparedContraction.data.program.volumeIndex i))
  unfold clsOf
  exact SliceClasses.cls_labelObject_fibre (B := kBundle K (stage G₀).leading)
    (ωB := bundleForm _ _ K.preparedContraction.data.rvForm) hc (ptA a) (show (n + 1) + 0 = n + 1 from rfl)
    (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ a K).preparedContraction.lift.originalTarget_recover _
    K.preparedContraction.data.program.volumeIndex
    (fun w => (mem_contractionAt_target h00 hc hκ hs hv hsmall hΓ G₀ a K w).trans (mem_bundle _ _ (ptA a, w)).symm)
    hprod hFinB hNZB (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ a K).preparedContraction.data.rvForm
    (fun z _ => congrArg (fun y => (K.preparedContraction.data.rvForm y).val)
      (Subtype.ext (Prod.ext (funext fun i => i.elim0) rfl)))
    _ _ _ _ _ (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ hdF

end Fibre

end DiamondIntegral.Section7.FibreContractions
