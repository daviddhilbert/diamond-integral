import «section 7».FirstStage
import «section 7».MapClasses
import «section 7».PullbackStages
import «section 6».ZeroCenteredBoundedTrace
import «section 6».ZeroCenteredHomeomorphism

/-! Normalized contractions from measured ordered contractions (tag transport).

Let `X ⊆ VF^{n+1} × RV^r` be a proper invariant, VF-doubly bounded set over the
base `T`, with form `ω`, and let `C` be a measured ordered contraction of
`(X, ω)` (Section 6: an ordered program contracting the last coordinate first,
with its RV form and a lift). A normalized measured contraction of `X`
(Section 6's `NormalizedMeasuredContraction`) instead starts with a zero-centred
normalization `D`, and its program lives on the prepared set
`reindexedVFSet D.map.image 1`, which carries `n + 1` extra core-tag labels in
front of the labels of `X`. For a doubly bounded `X` the normalization fixes the
VF coordinates and every core tag is `branchTag false`
(`ZeroCenteredData.point_field_of_doublyBounded`, `point_tags_of_doublyBounded`),
so the prepared set is `X` with the constant tuple `c = (branchTag false)^{n+1}`
prepended to its labels (`prepared_carrier`). Programs pull back easily along
maps that add labels (`precomposeFixedVF`); here they are pushed forward.

* `tagSet m A`: the set `{(x, c ++ u) | (x, u) ∈ A}` (`mem_tagSet`), with the
  definable tag maps `tagMap : A → tagSet m A` and `untagMap` back. Both fix the
  VF coordinates and their labels depend only on the labels; such maps between
  proper invariant sets are proper covariant homeomorphisms (`labelMap_home`)
  with unit derivative everywhere (`labelMap_unit`, the fixed-label chart is the
  identity). Tagging preserves proper invariance (`tagSet_properInvariant`) and
  VF double bounds.
* `tagStage H`: a standard contraction stage `H` of `A`, transported to
  `tagSet m A`. Its target is `tagSet m H.target`, its lift is
  `tagMap ∘ H.lift ∘ untagMap`, the old labels are the tags followed by `H`'s old
  labels (shifted), the leading label is `H`'s (shifted), and its exceptional set
  is produced from the generic unit derivative. Its contracted set is
  `tagSet m H.contracted` (`tagStage_contracted`).
* `tagProgram P`: every stage of an ordered program `P : A → U` tagged, a program
  `tagSet m A → tagSet m U`; along the way the tail is moved along the equality of
  contracted sets (`programOn`). It commutes with the tag maps
  (`tagProgram_toMap`), and its volume labels and old labels are those of `P`
  after the tags (`tagProgram_volumeIndex`, `tagProgram_oldLabels`).
* `ofContraction D hXb C`: the normalized measured contraction of `(X, ω)` in the
  identity order with normalization `D` (`ofContraction_normalization`, by
  `rfl`), whose program is `C`'s program tagged with `c`, moved to the prepared
  set, whose RV target is `tagSet (n + 1) C.data.rvTarget` and whose RV form is
  `C`'s RV form after dropping the tags (`tagForm`).
* `cls_ofContraction`: for every head start `k` and selection `π`, the
  head-start class of `ofContraction D hXb C` equals the head-start class of `C`
  (`MeasuredOrderedContraction.headStartObject`). Dropping the tags is a definable
  bijection of the RV targets matching the volume labels and the forms
  (`MapClasses.cls_labelObject_map`).

Hypotheses. The VF double bound of `X` is needed: without it the normalization
moves the large coordinates and the prepared set is not a tagged copy of `X`.
Proper invariance of `X` is part of `ZeroCenteredData`. No further hypothesis is
needed; the finite fibre hypothesis on `X` only enters through the finite volume
fields of the two head-start objects. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ProgramContractions
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Prepending constant branch tags -/

section Tags
variable {S : Set M} (m : ℕ) {n r : ℕ}

/-- The constant tuple of `m` branch tags `branchTag false`. -/
def constTags : Fin m → RVInfinity M := fun _ => branchTag (M := M) false

/-- `(x, u) ↦ (x, c ++ u)`, with `c` the constant tags. -/
def tagPoint (p : Mixed M n r) : Mixed M n (m + r) := (p.1, Fin.append (constTags m) p.2)

/-- `(x, w) ↦ (x, w ∘ natAdd)`, dropping the first `m` labels. -/
def untagPoint (q : Mixed M n (m + r)) : Mixed M n r := (q.1, fun j => q.2 (Fin.natAdd m j))

/-- The first `m` labels are the constant tags. -/
def Tagged (w : Fin (m + r) → RVInfinity M) : Prop := ∀ i, w (Fin.castAdd r i) = branchTag (M := M) false

theorem untagPoint_tagPoint (p : Mixed M n r) : untagPoint m (tagPoint m p) = p :=
  Prod.ext rfl (funext fun j => Fin.append_right _ _ j)

theorem tagPoint_untagPoint {q : Mixed M n (m + r)} (hq : Tagged m q.2) : tagPoint m (untagPoint m q) = q := by
  refine Prod.ext rfl (funext fun i => ?_)
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · exact (Fin.append_left _ _ i).trans (hq i).symm
  · exact Fin.append_right _ _ j

theorem tagged_tagPoint (p : Mixed M n r) : Tagged m (tagPoint m p).2 := fun i => Fin.append_left _ _ i

/-- The real codes of `tagPoint`. -/
def tagCodes (z : Fin n ⊕ Fin r → M) : Fin n ⊕ Fin (m + r) → M :=
  Sum.elim (fun i => z (.inl i)) (Fin.append (fun _ => (branchTag (M := M) false).val) (fun j => z (.inr j)))

theorem tagCodes_definable : S.DefinableMap LRV (tagCodes (M := M) m (n := n) (r := r)) := by
  rintro (i | i)
  · exact Set.DefinableFun.proj LRV
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [tagCodes, Sum.elim_inr, Fin.append_left] using
        (branchTag_definable (I := Fin n ⊕ Fin r) S false)
    · simpa only [tagCodes, Sum.elim_inr, Fin.append_right] using
        (show S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => z (.inr j)) from Set.DefinableFun.proj LRV)

theorem tagCodes_at (p : Mixed M n r) : tagCodes m (mixedValues p) = mixedValues (tagPoint m p) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [tagCodes, Sum.elim_inr, Fin.append_left, tagPoint, mixedValues, rvValues, constTags]
    · simp only [tagCodes, Sum.elim_inr, Fin.append_right, tagPoint, mixedValues, rvValues]

/-- The definable map `tagPoint` on a set. -/
def tagMapU (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n (m + r)) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n (m + r)
  have hcode (c : P.domain) : mixedValues (tagPoint m (P.decode c)) = tagCodes m c.val :=
    (tagCodes_at m (P.decode c)).symm.trans (congrArg (tagCodes m) (mixedValues_decode c))
  have hdom (c : P.domain) : tagCodes m c.val ∈ Q.domain := by
    rw [← hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A (tagPoint m) (tagCodes m) (tagCodes_definable m) hdom ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode ⟨tagCodes m c.val, hdom c⟩).trans (hcode c).symm

/-- The set `A` with the constant tags prepended to its labels. -/
def tagSet (A : DefSet (rawMixedSpace (M := M) n r) S) : DefSet (rawMixedSpace (M := M) n (m + r)) S :=
  (tagMapU m A).image

theorem mem_tagSet (A : DefSet (rawMixedSpace (M := M) n r) S) (q : Mixed M n (m + r)) :
    q ∈ (tagSet m A).carrier ↔ Tagged m q.2 ∧ untagPoint m q ∈ A.carrier := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨tagged_tagPoint m p.val, ?_⟩
    change untagPoint m (tagPoint m p.val) ∈ A.carrier
    rw [untagPoint_tagPoint]
    exact p.property
  · rintro ⟨hq, hA⟩
    exact ⟨⟨untagPoint m q, hA⟩, tagPoint_untagPoint m hq⟩

theorem tagPoint_mem (A : DefSet (rawMixedSpace (M := M) n r) S) {p : Mixed M n r} (hp : p ∈ A.carrier) :
    tagPoint m p ∈ (tagSet m A).carrier := ⟨⟨p, hp⟩, rfl⟩

/-- `tagPoint` as a map onto the tagged set. -/
def tagMap (A : DefSet (rawMixedSpace (M := M) n r) S) : Map A (tagSet m A) := (tagMapU m A).toImage

theorem tagMap_val (A : DefSet (rawMixedSpace (M := M) n r) S) (p : A) :
    (tagMap m A p).val = tagPoint m p.val := rfl

/-- The real codes of `untagPoint`. -/
def untagIndex : Fin n ⊕ Fin r → Fin n ⊕ Fin (m + r) := Sum.elim Sum.inl (fun j => Sum.inr (Fin.natAdd m j))

omit [M ⊨ Axioms.ACVF] in
theorem untagIndex_mixedValues (q : Mixed M n (m + r)) :
    mixedValues q ∘ untagIndex m = mixedValues (untagPoint m q) := by
  funext i
  rcases i with i | i <;> rfl

/-- `untagPoint` as a map from the tagged set. -/
def untagMap (A : DefSet (rawMixedSpace (M := M) n r) S) : Map (tagSet m A) A :=
  (PullbackStages.reindexMap (tagSet m A) (untagPoint m) (untagIndex m) (untagIndex_mixedValues m)).corestrict
    (fun q => ((mem_tagSet m A q.val).mp q.property).2)

theorem untagMap_val (A : DefSet (rawMixedSpace (M := M) n r) S) (q : tagSet m A) :
    (untagMap m A q).val = untagPoint m q.val := rfl

theorem untagMap_tagMap (A : DefSet (rawMixedSpace (M := M) n r) S) (p : A) :
    untagMap m A (tagMap m A p) = p :=
  Subtype.ext (untagPoint_tagPoint m p.val)

theorem tagMap_untagMap (A : DefSet (rawMixedSpace (M := M) n r) S) (q : tagSet m A) :
    tagMap m A (untagMap m A q) = q :=
  Subtype.ext (tagPoint_untagPoint m ((mem_tagSet m A q.val).mp q.property).1)

theorem tagMap_bijective (A : DefSet (rawMixedSpace (M := M) n r) S) : Function.Bijective (tagMap m A) :=
  ⟨fun p p' he => by rw [← untagMap_tagMap m A p, he, untagMap_tagMap],
    fun q => ⟨untagMap m A q, tagMap_untagMap m A q⟩⟩

theorem untagMap_bijective (A : DefSet (rawMixedSpace (M := M) n r) S) : Function.Bijective (untagMap m A) :=
  ⟨fun q q' he => by rw [← tagMap_untagMap m A q, he, tagMap_untagMap],
    fun p => ⟨tagMap m A p, untagMap_tagMap m A p⟩⟩

theorem tagSet_vfDoublyBounded {A : DefSet (rawMixedSpace (M := M) n r) S} (hA : VFDoublyBounded A.carrier) :
    VFDoublyBounded (tagSet m A).carrier := by
  obtain ⟨γ, hγ⟩ := hA
  exact ⟨γ, fun q hq i => hγ _ ((mem_tagSet m A q).mp hq).2 i⟩

theorem tagSet_properInvariant {A : DefSet (rawMixedSpace (M := M) n r) S} (hA : ProperInvariant S A.carrier) :
    ProperInvariant S (tagSet m A).carrier := by
  refine ⟨(tagSet m A).definable, ?_, ?_, fun w => ?_⟩
  · obtain ⟨γ, hγ⟩ := hA.vfBounded
    exact ⟨γ, fun q hq i => hγ _ ((mem_tagSet m A q).mp hq).2 i⟩
  · obtain ⟨γ, hγ⟩ := hA.rvBounded
    let δ : Gamma M := max 1 γ
    have hlow : (δ⁻¹).val ≤ (γ⁻¹).val := show δ⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_right _ _)
    have hlow1 : (δ⁻¹).val ≤ (1 : GammaInfinity M) := show δ⁻¹ ≤ (1 : Gamma M) from by
      simpa only [inv_one] using inv_le_inv' (show (1 : Gamma M) ≤ δ from le_max_left _ _)
    have hhigh : γ.val ≤ δ.val := le_max_right _ _
    have hhigh1 : (1 : GammaInfinity M) ≤ δ.val := show (1 : Gamma M) ≤ δ from le_max_left _ _
    refine ⟨δ, fun q hq i => ?_⟩
    obtain ⟨hT, hU⟩ := (mem_tagSet m A q).mp hq
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [hT i, branchTag_value]
      exact ⟨hlow1, hhigh1⟩
    · exact ⟨hlow.trans (hγ _ hU j).1, (hγ _ hU j).2.trans hhigh⟩
  · obtain ⟨α, hα, hInv⟩ := hA.radii (fun j => w (Fin.natAdd m j))
    refine ⟨α, fun i => (hα i).mono (Set.union_subset_union_right S (fun z ⟨l, hl⟩ => ⟨Fin.natAdd m l, hl⟩)),
      fun a b hab => ?_⟩
    change (a, w) ∈ (tagSet m A).carrier ↔ (b, w) ∈ (tagSet m A).carrier
    rw [mem_tagSet, mem_tagSet]
    exact and_congr Iff.rfl (hInv a b hab)

end Tags

/-! ### Maps that only change labels -/

section LabelMaps
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

omit [M ⊨ Axioms.ACVF] in
/-- The graph fibre source of a map fixing the VF coordinates, whose labels
depend only on the labels, is a label fibre of the source or empty. -/
theorem labelMap_source (f : Map A B) (hVF : ∀ p : A, (f p).val.1 = p.val.1)
    (hLab : ∀ p p' : A, p.val.2 = p'.val.2 → (f p).val.2 = (f p').val.2)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource f u v = if ∃ p : A, p.val.2 = u ∧ (f p).val.2 = v then vfFibre A.carrier u else ∅ := by
  ext x
  split_ifs with h
  · constructor
    · rintro ⟨y, p, hp, hfp⟩
      change (x, u) ∈ A.carrier
      exact hp ▸ p.property
    · intro hx
      obtain ⟨p, hpu, hpv⟩ := h
      let p' : A := ⟨(x, u), hx⟩
      exact ⟨x, p', rfl, Prod.ext (hVF p') ((hLab p' p hpu.symm).trans hpv)⟩
  · constructor
    · rintro ⟨y, p, hp, hfp⟩
      exact (h ⟨p, congrArg Prod.snd hp, congrArg Prod.snd hfp⟩).elim
    · intro hx
      exact hx.elim

omit [M ⊨ Axioms.ACVF] in
theorem labelMap_range (f : Map A B) (hVF : ∀ p : A, (f p).val.1 = p.val.1)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange f u v = graphFibreSource f u v := by
  ext y
  constructor
  · rintro ⟨x, p, hp, hfp⟩
    have he : y = x := (congrArg Prod.fst hfp).symm.trans ((hVF p).trans (congrArg Prod.fst hp))
    subst he
    exact ⟨y, p, hp, hfp⟩
  · rintro ⟨x, p, hp, hfp⟩
    have he : x = y := (congrArg Prod.fst hfp).symm.trans ((hVF p).trans (congrArg Prod.fst hp))
    subst he
    exact ⟨x, p, hp, hfp⟩

theorem labelMap_source_clopen (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hA : ProperInvariant S A.carrier) (hVF : ∀ p : A, (f p).val.1 = p.val.1)
    (hLab : ∀ p p' : A, p.val.2 = p'.val.2 → (f p).val.2 = (f p').val.2)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) : IsClopen (graphFibreSource f u v) := by
  rw [labelMap_source f hVF hLab]
  split_ifs
  · exact hA.clopen_fibres hv u
  · exact isClopen_empty

theorem labelMap_continuous (f : Map A B) (hVF : ∀ p : A, (f p).val.1 = p.val.1) :
    ContinuousOnGraphFibres (G := G) f := by
  intro u v
  apply continuous_id.continuousOn.congr
  intro a ha
  obtain ⟨p, hp, hfp⟩ := graphFibreMap_graph f u v ha
  exact (congrArg Prod.fst hfp).symm.trans ((hVF p).trans (congrArg Prod.fst hp))

/-- **Label maps are proper covariant homeomorphisms.** A bijection between
proper invariant sets fixing the VF coordinates, whose labels depend only on the
labels. -/
theorem labelMap_home (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (f : Map A B) (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier)
    (hf : Function.Bijective f) (hVF : ∀ p : A, (f p).val.1 = p.val.1)
    (hLab : ∀ p p' : A, p.val.2 = p'.val.2 → (f p).val.2 = (f p').val.2) :
    ProperCovariantHomeomorphism (G := G) f :=
  properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ f
    (properCovariant_of_clopen_ranges h00 hc hκ hs hv f hA hB (labelMap_continuous f hVF)
      (fun u v => (labelMap_source_clopen hv f hA hVF hLab u v).isOpen)
      (fun u v => (labelMap_range f hVF u v).symm ▸ labelMap_source_clopen hv f hA hVF hLab u v))
    hf (labelMap_continuous f hVF)

/-- **Label maps have unit derivative everywhere**: their fixed-label chart is
the identity. -/
theorem labelMap_unit (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hA : ProperInvariant S A.carrier) (hVF : ∀ p : A, (f p).val.1 = p.val.1)
    (hLab : ∀ p p' : A, p.val.2 = p'.val.2 → (f p).val.2 = (f p').val.2) (p : A) :
    HasMixedUnitDerivativeAt f p := by
  obtain ⟨ρ, hρ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((hA.clopen_fibres hv p.val.2).isOpen.mem_nhds p.property)
  refine ⟨LinearMap.id, ⟨fun x => LinearMap.id x + 0, ⟨ρ, fun x hx => ⟨hρ hx, ?_⟩⟩,
    hasVFDerivativeAt_affine LinearMap.id 0 p.val.1⟩, ?_⟩
  · exact Prod.ext ((hVF _).trans (by simp)) (hLab _ p rfl)
  · rw [LinearMap.toMatrix'_id, Matrix.det_one]

end LabelMaps

/-! ### The tag maps -/

section TagMaps
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} (m : ℕ) {n r : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

include h00 hc linear hκ hs hv hsmall hΓ in
theorem tagMap_home (hA : ProperInvariant S A.carrier) : ProperCovariantHomeomorphism (G := G) (tagMap m A) :=
  labelMap_home h00 hc linear hκ hs hv hsmall hΓ _ hA (tagSet_properInvariant m hA) (tagMap_bijective m A)
    (fun _ => rfl) (fun p p' h => by
      change Fin.append (constTags m) p.val.2 = Fin.append (constTags m) p'.val.2
      rw [h])

include h00 hc linear hκ hs hv hsmall hΓ in
theorem untagMap_home (hA : ProperInvariant S A.carrier) : ProperCovariantHomeomorphism (G := G) (untagMap m A) :=
  labelMap_home h00 hc linear hκ hs hv hsmall hΓ _ (tagSet_properInvariant m hA) hA (untagMap_bijective m A)
    (fun _ => rfl) (fun p p' h => by
      change (fun j => p.val.2 (Fin.natAdd m j)) = (fun j => p'.val.2 (Fin.natAdd m j))
      rw [h])

include hv in
theorem tagMap_unit (hA : ProperInvariant S A.carrier) (p : A) : HasMixedUnitDerivativeAt (tagMap m A) p :=
  labelMap_unit (G := G) hv _ hA (fun _ => rfl) (fun p p' h => by
      change Fin.append (constTags m) p.val.2 = Fin.append (constTags m) p'.val.2
      rw [h]) p

include hv in
theorem untagMap_unit (hA : ProperInvariant S A.carrier) (q : tagSet m A) :
    HasMixedUnitDerivativeAt (untagMap m A) q :=
  labelMap_unit (G := G) hv _ (tagSet_properInvariant m hA) (fun _ => rfl) (fun p p' h => by
      change (fun j => p.val.2 (Fin.natAdd m j)) = (fun j => p'.val.2 (Fin.natAdd m j))
      rw [h]) q

end TagMaps

/-! ### Tagged stages -/

section Stages
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} (m : ℕ) {n r : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}

include h00 hc linear hκ hs hv hsmall hΓ in
theorem stage_source_proper (H : StandardContractionStage (G := G) A) : ProperInvariant S A.carrier :=
  H.home.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ

/-- The lift of the tagged stage: drop the tags, lift, prepend the tags. -/
def tagLift (H : StandardContractionStage (G := G) A) : Map (tagSet m A) (tagSet m H.target) :=
  (tagMap m H.target).comp (H.lift.comp (untagMap m A))

theorem tagLift_val (H : StandardContractionStage (G := G) A) (q : tagSet m A) :
    (tagLift m H q).val = tagPoint m (H.lift (untagMap m A q)).val := rfl

include h00 hc linear hκ hs hv hsmall hΓ in
theorem tagLift_home (H : StandardContractionStage (G := G) A) : ProperCovariantHomeomorphism (G := G) (tagLift m H) :=
  lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
      (untagMap_home m h00 hc linear hκ hs hv hsmall hΓ (stage_source_proper h00 hc linear hκ hs hv hsmall hΓ H))
      H.home)
    (tagMap_home m h00 hc linear hκ hs hv hsmall hΓ H.proper)

include h00 hc linear hκ hs hv hsmall hΓ in
theorem tagLift_generic (H : StandardContractionStage (G := G) A) (q : tagSet m A)
    (hq : AlgebraicIndependent (vfParameterField S) q.val.1) : HasMixedUnitDerivativeAt (tagLift m H) q := by
  have hE : (untagMap m A q).val ∉ H.exceptional.carrier :=
    not_mem_small_set_of_independent hc H.exceptional H.exceptional_dim _ hq
  exact (tagMap_unit (G := G) m hv H.proper _).comp ((H.unitDerivative _ hE).comp
    (untagMap_unit (G := G) m hv (stage_source_proper h00 hc linear hκ hs hv hsmall hΓ H) q))

omit [M ⊨ Axioms.ACVF] in
theorem append_labels_injective {a b c : ℕ} {f : Fin b → Fin c} (hf : Function.Injective f) :
    Function.Injective (Fin.append (Fin.castAdd c : Fin a → Fin (a + c)) (fun j => Fin.natAdd a (f j))) := by
  intro x y h
  induction x using Fin.addCases with
  | left i =>
    induction y using Fin.addCases with
    | left i' =>
      rw [Fin.append_left, Fin.append_left] at h
      have h' := congrArg Fin.val h
      simp only [Fin.val_castAdd] at h'
      exact congrArg _ (Fin.ext h')
    | right j' =>
      rw [Fin.append_left, Fin.append_right] at h
      have h' := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
      exact absurd h' (by omega)
  | right j =>
    induction y using Fin.addCases with
    | left i' =>
      rw [Fin.append_right, Fin.append_left] at h
      have h' := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
      exact absurd h' (by omega)
    | right j' =>
      rw [Fin.append_right, Fin.append_right] at h
      have h' := congrArg Fin.val h
      simp only [Fin.val_natAdd] at h'
      have hfj : f j = f j' := Fin.ext (by omega)
      rw [hf hfj]

theorem tagLift_retained (H : StandardContractionStage (G := G) A) (q : tagSet m A) (i : Fin (m + r)) :
    (tagLift m H q).val.2 (Fin.append (Fin.castAdd H.arity) (fun j => Fin.natAdd m (H.oldLabels j)) i) =
      q.val.2 i := by
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    change Fin.append (constTags m) (H.lift (untagMap m A q)).val.2 (Fin.castAdd H.arity i) = _
    rw [Fin.append_left]
    exact (((mem_tagSet m A q.val).mp q.property).1 i).symm
  | right j =>
    rw [Fin.append_right]
    change Fin.append (constTags m) (H.lift (untagMap m A q)).val.2 (Fin.natAdd m (H.oldLabels j)) = _
    rw [Fin.append_right]
    exact H.retained (untagMap m A q) j

theorem tagLift_bundle (H : StandardContractionStage (G := G) A) :
    (tagSet m H.target).carrier =
      (rvCoordinateBundle (vfDropLast (tagSet m H.target)).image (Fin.natAdd m H.leading)).carrier := by
  ext q
  change q ∈ (tagSet m H.target).carrier ↔ (Fin.init q.1, q.2) ∈ (vfDropLast (tagSet m H.target)).image.carrier ∧
    rv M (q.1 (Fin.last n)) = q.2 (Fin.natAdd m H.leading)
  constructor
  · intro hq
    obtain ⟨-, hU⟩ := (mem_tagSet m H.target q).mp hq
    exact ⟨⟨⟨q, hq⟩, rfl⟩, ((H.recover_target (untagPoint m q)).mp hU).2⟩
  · rintro ⟨⟨p, hp⟩, hrv⟩
    have hp1 : Fin.init p.val.1 = Fin.init q.1 := (congrArg Prod.fst hp :)
    have hp2 : p.val.2 = q.2 := (congrArg Prod.snd hp :)
    obtain ⟨hT, hU⟩ := (mem_tagSet m H.target p.val).mp p.property
    refine (mem_tagSet m H.target q).mpr ⟨hp2 ▸ hT, ?_⟩
    refine (H.recover_target (untagPoint m q)).mpr ⟨?_, hrv⟩
    have h := ((H.recover_target (untagPoint m p.val)).mp hU).1
    change (Fin.init p.val.1, fun j => p.val.2 (Fin.natAdd m j)) ∈ H.contracted.carrier at h
    change (Fin.init q.1, fun j => q.2 (Fin.natAdd m j)) ∈ H.contracted.carrier
    rw [← hp1, ← hp2]
    exact h

/-- **The tagged stage.** A stage `H` of `A`, transported to the set `A` with
the constant tags prepended: its target is `H`'s target with the tags prepended,
its lift drops the tags, applies `H` and prepends them again, the tags are
retained old labels and the leading label is `H`'s leading label. -/
def tagStage (H : StandardContractionStage (G := G) A) : StandardContractionStage (G := G) (tagSet m A) := by
  have hEx := exists_mixed_unit_derivative_exception hc hs hsmall (Nat.zero_lt_succ n) (tagLift m H)
    (tagLift_generic m h00 hc linear hκ hs hv hsmall hΓ H)
  exact {
    arity := m + H.arity
    target := tagSet m H.target
    lift := tagLift m H
    home := tagLift_home m h00 hc linear hκ hs hv hsmall hΓ H
    proper := tagSet_properInvariant m H.proper
    doublyBounded := tagSet_vfDoublyBounded m H.doublyBounded
    relative := fun q i => H.relative (untagMap m A q) i
    oldLabels := Fin.append (Fin.castAdd H.arity) (fun j => Fin.natAdd m (H.oldLabels j))
    oldLabels_injective := append_labels_injective H.oldLabels_injective
    retained := tagLift_retained m H
    leading := Fin.natAdd m H.leading
    bundle := tagLift_bundle m H
    exceptional := hEx.choose
    exceptional_subset := hEx.choose_spec.1
    exceptional_dim := hEx.choose_spec.2.1
    unitDerivative := hEx.choose_spec.2.2 }

theorem tagStage_target (H : StandardContractionStage (G := G) A) :
    (tagStage m h00 hc linear hκ hs hv hsmall hΓ H).target = tagSet m H.target := rfl

theorem tagStage_oldLabels (H : StandardContractionStage (G := G) A) (j : Fin r) :
    (tagStage m h00 hc linear hκ hs hv hsmall hΓ H).oldLabels (Fin.natAdd m j) = Fin.natAdd m (H.oldLabels j) :=
  (Fin.append_right (Fin.castAdd H.arity) (fun j => Fin.natAdd m (H.oldLabels j)) j :)

theorem tagStage_leading (H : StandardContractionStage (G := G) A) :
    (tagStage m h00 hc linear hκ hs hv hsmall hΓ H).leading = Fin.natAdd m H.leading := rfl

theorem tagStage_contraction (H : StandardContractionStage (G := G) A) (q : tagSet m A) :
    ((tagStage m h00 hc linear hκ hs hv hsmall hΓ H).contraction q).val =
      tagPoint m (H.contraction (untagMap m A q)).val := rfl

/-- The contracted set of the tagged stage is the tagged contracted set. -/
theorem tagStage_contracted_carrier (H : StandardContractionStage (G := G) A) :
    (tagStage m h00 hc linear hκ hs hv hsmall hΓ H).contracted.carrier = (tagSet m H.contracted).carrier := by
  ext q
  rw [mem_tagSet]
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨hT, hU⟩ := (mem_tagSet m H.target p.val).mp p.property
    exact ⟨hT, ⟨⟨untagPoint m p.val, hU⟩, rfl⟩⟩
  · rintro ⟨hT, ⟨t, ht⟩⟩
    exact ⟨⟨tagPoint m t.val, tagPoint_mem m H.target t.property⟩,
      (congrArg (tagPoint m) ht).trans (tagPoint_untagPoint m hT)⟩

theorem tagStage_contracted (H : StandardContractionStage (G := G) A) :
    (tagStage m h00 hc linear hκ hs hv hsmall hΓ H).contracted = tagSet m H.contracted :=
  defSet_eq_of_carrier_eq (tagStage_contracted_carrier m h00 hc linear hκ hs hv hsmall hΓ H)

end Stages

/-! ### Tagged programs -/

section Programs
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} (m : ℕ)
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))

theorem toMap_step {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (H : StandardContractionStage (G := G) A)
    (tail : OrderedStandardContractionProgram (G := G) S H.contracted U) (p : A) :
    (OrderedStandardContractionProgram.step H tail).toMap p = tail.toMap (H.contraction p) := rfl

theorem oldLabels_step {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (H : StandardContractionStage (G := G) A)
    (tail : OrderedStandardContractionProgram (G := G) S H.contracted U) (i : Fin r) :
    (OrderedStandardContractionProgram.step H tail).oldLabels i = tail.oldLabels (H.oldLabels i) := rfl

/-- A program of `A`, as a program of a set equal to `A`. -/
def programOn {n r q : ℕ} {A A' : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (P : OrderedStandardContractionProgram (G := G) S A U) (e : A' = A) :
    OrderedStandardContractionProgram (G := G) S A' U := e ▸ P

theorem programOn_toMap {n r q : ℕ} {A A' : DefSet (rawMixedSpace (M := M) n r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (P : OrderedStandardContractionProgram (G := G) S A U)
    (e : A' = A) (p : A') (p' : A) (h : p.val = p'.val) : ((programOn P e).toMap p).val = (P.toMap p').val := by
  subst e
  obtain rfl : p = p' := Subtype.ext h
  rfl

theorem programOn_oldLabels {n r q : ℕ} {A A' : DefSet (rawMixedSpace (M := M) n r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (P : OrderedStandardContractionProgram (G := G) S A U)
    (e : A' = A) : (programOn P e).oldLabels = P.oldLabels := by
  subst e
  rfl

theorem programOn_volumeIndex {n r q : ℕ} {A A' : DefSet (rawMixedSpace (M := M) n r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (P : OrderedStandardContractionProgram (G := G) S A U)
    (e : A' = A) : (programOn P e).volumeIndex = P.volumeIndex := by
  subst e
  rfl

/-- **The tagged program.** Every stage of `P` transported to the sets with the
constant tags prepended (`tagStage`), from the tagged source to the tagged RV
target. -/
def tagProgram {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (P : OrderedStandardContractionProgram (G := G) S A U) :
    OrderedStandardContractionProgram (G := G) S (tagSet m A) (tagSet m U) := by
  induction P with
  | zero A => exact .zero _
  | step H tail ih =>
    exact .step (tagStage m h00 hc linear hκ hs hv hsmall hΓ H)
      (programOn ih (tagStage_contracted m h00 hc linear hκ hs hv hsmall hΓ H))

theorem tagProgram_step {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (H : StandardContractionStage (G := G) A)
    (tail : OrderedStandardContractionProgram (G := G) S H.contracted U) :
    tagProgram m h00 hc linear hκ hs hv hsmall hΓ (.step H tail) =
      .step (tagStage m h00 hc linear hκ hs hv hsmall hΓ H)
        (programOn (tagProgram m h00 hc linear hκ hs hv hsmall hΓ tail)
          (tagStage_contracted m h00 hc linear hκ hs hv hsmall hΓ H)) := rfl

/-- The tagged program commutes with the tag maps. -/
theorem tagProgram_toMap {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (P : OrderedStandardContractionProgram (G := G) S A U) :
    ∀ z : tagSet m A, ((tagProgram m h00 hc linear hκ hs hv hsmall hΓ P).toMap z).val =
      tagPoint m (P.toMap (untagMap m A z)).val := by
  induction P with
  | zero A =>
    intro z
    exact (tagPoint_untagPoint m ((mem_tagSet m A z.val).mp z.property).1).symm
  | step H tail ih =>
    intro z
    rw [tagProgram_step, toMap_step, toMap_step,
      programOn_toMap _ _ ((tagStage m h00 hc linear hκ hs hv hsmall hΓ H).contraction z)
        (tagMap m H.contracted (H.contraction (untagMap m _ z))) rfl, ih, untagMap_tagMap]

/-- The tagged program retains the old labels after the tags. -/
theorem tagProgram_oldLabels {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (P : OrderedStandardContractionProgram (G := G) S A U) :
    ∀ i : Fin r, (tagProgram m h00 hc linear hκ hs hv hsmall hΓ P).oldLabels (Fin.natAdd m i) =
      Fin.natAdd m (P.oldLabels i) := by
  induction P with
  | zero A => intro i; rfl
  | step H tail ih =>
    intro i
    rw [tagProgram_step, oldLabels_step, oldLabels_step, programOn_oldLabels, tagStage_oldLabels, ih]

/-- The volume labels of the tagged program are those of `P`, after the tags. -/
theorem tagProgram_volumeIndex {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} (P : OrderedStandardContractionProgram (G := G) S A U) :
    ∀ i : Fin n, (tagProgram m h00 hc linear hκ hs hv hsmall hΓ P).volumeIndex i =
      Fin.natAdd m (P.volumeIndex i) := by
  induction P with
  | zero A => intro i; exact i.elim0
  | step H tail ih =>
    intro i
    rw [tagProgram_step]
    induction i using Fin.lastCases with
    | last =>
      rw [OrderedStandardContractionProgram.volumeIndex_step_last,
        OrderedStandardContractionProgram.volumeIndex_step_last, programOn_oldLabels, tagStage_leading,
        tagProgram_oldLabels]
    | cast j =>
      rw [OrderedStandardContractionProgram.volumeIndex_step_castSucc,
        OrderedStandardContractionProgram.volumeIndex_step_castSucc, programOn_volumeIndex, ih]

end Programs

/-! ### Normalized contractions from measured ordered contractions -/

section Normalized
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n r : ℕ} {X : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
variable {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
variable (D : ZeroCenteredData X) (hXb : VFDoublyBounded X.carrier)
variable (C : MeasuredOrderedContraction (G := G) X ω)

include hXb in
/-- On a doubly bounded set, the prepared set of a zero-centred normalization in
the identity order is the set with the constant tags prepended. -/
theorem prepared_carrier : (reindexedVFSet D.map.image 1).carrier = (tagSet (n + 1) X).carrier := by
  ext q
  rw [mem_reindexedVFSet, D.image_carrier, mem_tagSet]
  constructor
  · rintro ⟨p, hp, he⟩
    have h1 := D.point_field_of_doublyBounded hXb hp
    have h2 := D.point_tags_of_doublyBounded hXb hp
    rw [he] at h1 h2
    have hq : q = tagPoint (n + 1) p := Prod.ext h1 h2
    subst hq
    exact ⟨tagged_tagPoint _ p, by rw [untagPoint_tagPoint]; exact hp⟩
  · rintro ⟨hT, hU⟩
    refine ⟨untagPoint (n + 1) q, hU, Prod.ext ?_ ?_⟩
    · rw [D.point_field_of_doublyBounded hXb hU]
      rfl
    · rw [D.point_tags_of_doublyBounded hXb hU]
      exact congrArg Prod.snd (tagPoint_untagPoint (n + 1) hT)

include hXb in
theorem prepared_eq : reindexedVFSet D.map.image 1 = tagSet (n + 1) X :=
  defSet_eq_of_carrier_eq (prepared_carrier D hXb)

/-- The RV form on the tagged RV target: `C`'s RV form after dropping the tags. -/
def tagForm : Map (tagSet (n + 1) C.data.rvTarget) (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  C.data.rvForm.comp (untagMap (n + 1) C.data.rvTarget)

/-- `C`'s program with the constant tags prepended, on the prepared set of `D`. -/
def preparedProgram : OrderedStandardContractionProgram (G := G) (T : Set M) (reindexedVFSet D.map.image 1)
    (tagSet (n + 1) C.data.rvTarget) :=
  programOn (tagProgram (n + 1) h00 hc linear hκ hs hv hsmall hΓ C.data.program) (prepared_eq D hXb)

theorem preparedProgram_toMap (q : reindexedVFSet D.map.image 1) (p : X) (hq : q.val = tagPoint (n + 1) p.val) :
    untagMap (n + 1) C.data.rvTarget ((preparedProgram h00 hc linear hκ hs hv hsmall hΓ D hXb C).toMap q) =
      C.data.program.toMap p := by
  apply Subtype.ext
  change untagPoint (n + 1) ((preparedProgram h00 hc linear hκ hs hv hsmall hΓ D hXb C).toMap q).val = _
  rw [preparedProgram, programOn_toMap _ _ q (tagMap (n + 1) X p) hq, tagProgram_toMap, untagMap_tagMap,
    untagPoint_tagPoint]

/-- The measured program on the prepared set: the tagged program, with the RV
form `tagForm`. -/
def preparedData : MeasuredOrderedProgram (G := G) (reindexedVFSet D.map.image 1)
    ((tagForm C).comp (preparedProgram h00 hc linear hκ hs hv hsmall hΓ D hXb C).toMap) where
  arity := (n + 1) + C.data.arity
  rvTarget := tagSet (n + 1) C.data.rvTarget
  program := preparedProgram h00 hc linear hκ hs hv hsmall hΓ D hXb C
  rvForm := tagForm C
  factor _ := rfl

/-- **Normalized contractions from measured ordered contractions.** The
normalized measured contraction of the doubly bounded set `X`, in the identity
order, with normalization `D`, whose program is `C`'s program with the constant
branch tags of `D` prepended to every stage. -/
def ofContraction : NormalizedMeasuredContraction (G := G) X ω 1 where
  normalization := D
  preparedForm := (tagForm C).comp (preparedProgram h00 hc linear hκ hs hv hsmall hΓ D hXb C).toMap
  transport p := by
    have hq : (vfRelabeling D.map.image 1 (D.bijection p)).val = tagPoint (n + 1) p.val := by
      rw [vfRelabeling_value]
      change ((D.point p.val).1 ∘ ⇑(1 : Equiv.Perm (Fin (n + 1))), (D.point p.val).2) = _
      rw [D.point_field_of_doublyBounded hXb p.property, D.point_tags_of_doublyBounded hXb p.property]
      rfl
    change (C.data.rvForm (untagMap (n + 1) C.data.rvTarget ((preparedProgram h00 hc linear hκ hs hv hsmall hΓ
      D hXb C).toMap (vfRelabeling D.map.image 1 (D.bijection p))))).val = _
    rw [preparedProgram_toMap h00 hc linear hκ hs hv hsmall hΓ D hXb C _ p hq]
    exact C.data.factor p
  preparedContraction := ⟨preparedData h00 hc linear hκ hs hv hsmall hΓ D hXb C,
    Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
      (reindexedVFSet_properInvariant _ 1 (D.image_properInvariant h00 hc hκ hs hv)))⟩

theorem ofContraction_normalization : (ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).normalization = D :=
  rfl

theorem ofContraction_rvTarget :
    (ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).preparedContraction.data.rvTarget =
      tagSet (n + 1) C.data.rvTarget := rfl

theorem ofContraction_rvForm :
    (ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).preparedContraction.data.rvForm = tagForm C := rfl

theorem ofContraction_volumeIndex (i : Fin (n + 1)) :
    (ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).preparedContraction.data.program.volumeIndex i =
      Fin.natAdd (n + 1) (C.data.program.volumeIndex i) := by
  change (programOn (tagProgram (n + 1) h00 hc linear hκ hs hv hsmall hΓ C.data.program)
    (prepared_eq D hXb)).volumeIndex i = _
  rw [programOn_volumeIndex, tagProgram_volumeIndex]

theorem ofContraction_oldIndex (j : Fin r) :
    (ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).oldIndex j =
      Fin.natAdd (n + 1) (C.data.program.oldLabels j) := by
  change (programOn (tagProgram (n + 1) h00 hc linear hκ hs hv hsmall hΓ C.data.program)
    (prepared_eq D hXb)).oldLabels (Fin.natAdd (n + 1) j) = _
  rw [programOn_oldLabels, tagProgram_oldLabels]

/-- The head-start object of a measured ordered contraction is the label object
over its lifted target, with its old labels at `π` and its form (by `rfl`), for
comparison with other label objects over `C.data.rvTarget`
(`FirstStage.cls_labelObject_eq`, `C.lift.recover`). -/
theorem headStartObject_eq_labelObject (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ π = t}.Finite) :
    C.headStartObject hc h00 hκ.le hs hsmall k π hFin =
      labelObject C.lift.target k (C.data.program.oldLabels ∘ π) C.lift.target_tagged
        (C.lift.headStartObject_finite_volume hc h00 hκ.le hs hsmall k π hFin)
        (preparedRVObject_nonzero _ _
          (rvHeadStartBundle_doublyBounded _ k _ C.lift.doublyBounded C.lift.proper.rvBounded))
        C.form C.form_same_tags := rfl

/-- **The class of `ofContraction`.** For every head start `k` and selection
`π`, the head-start class of `ofContraction D C` is the head-start class of
`C`. Both are label objects; the RV target of `ofContraction D C` is `C`'s with
the constant tags prepended, and dropping the tags is a definable bijection
matching the volume labels and the RV forms (`MapClasses.cls_labelObject_map`). -/
theorem cls_ofContraction (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ π = t}.Finite) :
    cls (objOf hc T ((ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).headStartMeasuredObject h00 hc linear
        hκ hs hv hsmall hΓ k π hFin)
        ((ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).headStartObject_doublyBounded k π)) =
      cls (objOf hc T (C.headStartObject hc h00 hκ.le hs hsmall k π hFin)
        (headStartObject_doublyBounded h00 hc hκ hs hsmall C k π hFin)) :=
  MapClasses.cls_labelObject_map hc (show (n + 1) + k = (n + 1) + k from rfl)
    (ofContraction h00 hc linear hκ hs hv hsmall hΓ D hXb C).preparedContraction.lift.originalTarget_recover
    C.lift.recover _ _ (untagMap (n + 1) C.data.rvTarget) (untagMap_bijective _ _) (fun z => by
      refine Finset.prod_congr rfl (fun i _ => congrArg gam ?_)
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left, Fin.append_left]
        exact congrArg z.val.2 (ofContraction_volumeIndex h00 hc linear hκ hs hv hsmall hΓ D hXb C _)
      | right j =>
        rw [Fin.append_right, Fin.append_right]
        exact congrArg z.val.2 (ofContraction_oldIndex h00 hc linear hκ hs hv hsmall hΓ D hXb C (π j)))
    (tagForm C) C.data.rvForm (fun _ => rfl) _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

end Normalized

end DiamondIntegral.Section7.ProgramContractions
