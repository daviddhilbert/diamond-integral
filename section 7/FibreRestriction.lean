import «section 6».DiamondCategory
import «section 6».VFProjection
import «section 6».DefinableParameterDescent
import «section 7».GoodPoints
import Section9.MixedDifferentiationAE
import Section9.DerivativeCoordinates

/-! Restricting a map that fixes the first `m` VF coordinates to the slices
over a point `b ∈ VFᵐ` (used in Corollary 7.15).

For a definable mixed set `X ⊆ VF^{m+1} × RVʳ` over `S` and `b ∈ VFᵐ`, the
slice `X_b = {(x, t) ∈ VF × RVʳ | ((b, x), t) ∈ X}` is definable over every
base `S'` containing `S` and the coordinates of `b` (`sliceSet`), and it is
proper invariant when `X` is (`sliceSet_properInvariant`).

Let `f : X → X'` be a definable map that fixes the first `m` VF coordinates.
Then `f` sends `X_b` into `X'_b`, and its restriction `f_b` (`sliceMap`) is
again definable. If `f` is bijective, so is `f_b`. If `f` is a proper
covariant homeomorphism, so is `f_b`: its graph fibres are the slices of those
of `f`, so the radii of `f` in the last coordinate serve for `f_b`. The
inverse of `f_b` is the restriction of the inverse of `f`.

A chart of `f` at a point of the slice agrees with the coordinate
projections in the first `m` coordinates on a ball. So the first `m` rows of
the derivative are unit rows, the derivative matrix is lower triangular, and
its determinant is its last diagonal entry, which is the derivative of the
restriction (`sliceMap_derivative`).

A definable set `Bad` of VF dimension `< m + 1` lies in the zero set of a
nonzero polynomial `Q`. A nonzero coefficient `P` of `Q`, viewed as a
polynomial in the last variable, gives the good points: if `P(b) ≠ 0`, then
`Q(b, ·)` is a nonzero polynomial over the VF parameter field of `S'`. So
every point of the slice `Bad_b` is algebraic over that field, and `Bad_b`
has VF dimension `0` (`exists_good_polynomial`).

Finally the slice of an object of `μVF^◇[m + 1]` with slice form covariance
is an object of `μVF^◇[1]` over `S'` (`sliceObject`), and at a good point the
restriction of a morphism is a morphism of `μVF^◇[1]` over `S'`
(`sliceMorphism`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.FibreRestriction
open DiamondIntegral.Section6 DiamondIntegral.Section2
open SpecialTransformations.Section9 DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S S' : Set M} {m r s : ℕ}

/-! ### The slice of a mixed set -/

section Slice

/-- The real codes of `(x, t) ↦ ((b, x), t)`. -/
def liftCodes (b : Fin m → VF M) (z : Fin 1 ⊕ Fin r → M) : Fin (m + 1) ⊕ Fin r → M :=
  Sum.elim (Fin.snoc (α := fun _ => M) (vfValues b) (z (.inl 0))) (z ∘ Sum.inr)

omit [M ⊨ Axioms.ACVF] in
theorem liftCodes_definable (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    S'.DefinableMap LRV (liftCodes (r := r) b) := by
  rintro (i | i)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · have he : (fun z : Fin 1 ⊕ Fin r → M => liftCodes b z (.inl (Fin.last m))) =
          fun z => z (.inl 0) := by
        funext z
        simp [liftCodes]
      rw [he]
      exact Set.DefinableFun.proj LRV
    · have he : (fun z : Fin 1 ⊕ Fin r → M => liftCodes b z (.inl j.castSucc)) =
          fun _ => (b j).val := by
        funext z
        simp [liftCodes, vfValues]
      rw [he]
      exact LRV.definableFun_const _ (hS (Or.inr ⟨j, rfl⟩))
  · exact Set.DefinableFun.proj LRV

omit [M ⊨ Axioms.ACVF] in
theorem liftCodes_mixedValues (b : Fin m → VF M) (p : Mixed M 1 r) :
    liftCodes b (mixedValues p) = mixedValues ((Fin.snoc b (p.1 0), p.2) : Mixed M (m + 1) r) := by
  funext i
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [liftCodes, mixedValues, vfValues]
    · simp [liftCodes, mixedValues, vfValues]
  · rfl

omit [M ⊨ Axioms.ACVF] in
theorem liftCodes_decode (b : Fin m → VF M) (c : (rawMixedSpace (M := M) 1 r).domain) :
    liftCodes b c.val = mixedValues
      ((Fin.snoc b (((rawMixedSpace (M := M) 1 r).decode c).1 0),
        ((rawMixedSpace (M := M) 1 r).decode c).2) : Mixed M (m + 1) r) := by
  rw [← liftCodes_mixedValues, mixedValues_decode]

/-- The definable map `(x, t) ↦ ((b, x), t)` over `S'`. -/
def liftMap (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    Map (DefSet.univ (rawMixedSpace (M := M) 1 r) S')
      (DefSet.univ (rawMixedSpace (M := M) (m + 1) r) S') :=
  Map.ofCodes _ (fun p : Mixed M 1 r => ((Fin.snoc b (p.1 0), p.2) : Mixed M (m + 1) r))
    (liftCodes b) (liftCodes_definable b hS)
    (fun c => (liftCodes_decode b c) ▸ mixedValues_mem_domain _)
    (fun c => mixedValues_injective ((mixedValues_decode _).trans (liftCodes_decode b c)))

/-- The slice `X_b = {(x, t) | ((b, x), t) ∈ X}`, over a base `S'` containing
`S` and the coordinates of `b`. -/
def sliceSet (X : DefSet (rawMixedSpace (M := M) (m + 1) r) S) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') : DefSet (rawMixedSpace (M := M) 1 r) S' where
  carrier := {p | ((Fin.snoc b (p.1 0), p.2) : Mixed M (m + 1) r) ∈ X.carrier}
  definable := by
    have h := (liftMap (r := r) b hS).definable_preimage
      (X.definable.mono _ (Set.subset_union_left.trans hS))
    convert h using 1
    ext p
    constructor
    · intro hp
      exact ⟨⟨p, Set.mem_univ _⟩, rfl, hp⟩
    · rintro ⟨a, rfl, ha⟩
      exact ha

variable {X : DefSet (rawMixedSpace (M := M) (m + 1) r) S} {b : Fin m → VF M}
  {hS : S ∪ Set.range (vfValues b) ⊆ S'}

omit [M ⊨ Axioms.ACVF] in
theorem mem_sliceSet (p : Mixed M 1 r) :
    p ∈ (sliceSet X b hS).carrier ↔ ((Fin.snoc b (p.1 0), p.2) : Mixed M (m + 1) r) ∈ X.carrier :=
  Iff.rfl

omit [M ⊨ Axioms.ACVF] in
theorem sliceSet_mono {Y : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
    (h : Y.carrier ⊆ X.carrier) :
    (sliceSet Y b hS).carrier ⊆ (sliceSet X b hS).carrier :=
  fun _ hp => h hp

/-- The point of `X` over a point of the slice. -/
def liftElem (q : sliceSet X b hS) : X := ⟨(Fin.snoc b (q.val.1 0), q.val.2), q.property⟩

omit [M ⊨ Axioms.ACVF] in
@[simp] theorem liftElem_val (q : sliceSet X b hS) :
    (liftElem q).val = ((Fin.snoc b (q.val.1 0), q.val.2) : Mixed M (m + 1) r) := rfl

/-- The definable map `X_b → X`, `(x, t) ↦ ((b, x), t)`, over `S'`. -/
def liftElemMap (X : DefSet (rawMixedSpace (M := M) (m + 1) r) S) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    Map (sliceSet X b hS) (extendDefSetBase (Set.subset_union_left.trans hS) X) :=
  ((liftMap (r := r) b hS).comp (Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict
    (fun q => q.property)

omit [M ⊨ Axioms.ACVF] in
@[simp] theorem liftElemMap_val (q : sliceSet X b hS) :
    (liftElemMap X b hS q).val = ((Fin.snoc b (q.val.1 0), q.val.2) : Mixed M (m + 1) r) := rfl

omit [M ⊨ Axioms.ACVF] in
theorem fin_one_ext {x y : Fin 1 → VF M} (h : x 0 = y 0) : x = y := by
  funext i
  rw [Subsingleton.elim i 0]
  exact h

omit [M ⊨ Axioms.ACVF] in
theorem snoc_last_eq_iff {x y : Fin 1 → VF M} :
    (Fin.snoc b (x 0) : Fin (m + 1) → VF M) = Fin.snoc b (y 0) ↔ x = y := by
  constructor
  · intro h
    apply fin_one_ext
    simpa using congrFun h (Fin.last m)
  · rintro rfl
    rfl

omit [M ⊨ Axioms.ACVF] in
/-- A tuple whose first `m` coordinates are `b` is `(b, x)`. -/
theorem eq_snoc_of_init {a : Fin (m + 1) → VF M} (h : Fin.init a = b) :
    a = Fin.snoc b (a (Fin.last m)) := by
  conv_lhs => rw [← Fin.snoc_init_self a]
  rw [h]

theorem congruent_snoc {α : Fin (m + 1) → Gamma M} {x y : Fin 1 → VF M}
    (h : Congruent (fun _ => α (Fin.last m)) x y) :
    Congruent α (Fin.snoc b (x 0)) (Fin.snoc b (y 0)) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h 0
  · simpa using DiamondIntegral.Section6.Congruent.refl α (Fin.snoc b (x 0) : Fin (m + 1) → VF M)
      j.castSucc

theorem congruent_of_snoc {α : Fin (m + 1) → Gamma M} {x y : Fin 1 → VF M}
    (h : Congruent α (Fin.snoc b (x 0)) (Fin.snoc b (y 0))) :
    Congruent (fun _ => α (Fin.last m)) x y := by
  intro i
  rw [Subsingleton.elim i 0]
  simpa using h (Fin.last m)

theorem namedRadii_mono {t : Fin r → RVInfinity M} {n : ℕ} {α : Fin n → Gamma M}
    (h : NamedRadii S t α) (hST : S ⊆ S') : NamedRadii S' t α :=
  fun i => (h i).mono (Set.union_subset_union_left _ hST)

theorem sliceSet_vfBounded (hX : VFBounded X.carrier) : VFBounded (sliceSet X b hS).carrier := by
  obtain ⟨γ, hγ⟩ := hX
  refine ⟨γ, fun p hp i => ?_⟩
  rw [Subsingleton.elim i 0]
  simpa using hγ _ hp (Fin.last m)

theorem sliceSet_rvBounded (hX : RVSupportDoublyBounded X.carrier) :
    RVSupportDoublyBounded (sliceSet X b hS).carrier := by
  obtain ⟨γ, hγ⟩ := hX
  exact ⟨γ, fun p hp i => hγ _ hp i⟩

/-- The slice of a proper invariant set is proper invariant: the radius of
`X` in the last coordinate serves for the slice. -/
theorem sliceSet_properInvariant (hX : ProperInvariant S X.carrier) :
    ProperInvariant S' (sliceSet X b hS).carrier := by
  refine ⟨(sliceSet X b hS).definable, sliceSet_vfBounded hX.vfBounded,
    sliceSet_rvBounded hX.rvBounded, fun t => ?_⟩
  obtain ⟨α, hα, hInv⟩ := hX.radii t
  refine ⟨fun _ => α (Fin.last m), fun _ => (hα (Fin.last m)).mono
    (Set.union_subset_union_left _ (Set.subset_union_left.trans hS)), fun x y hxy => ?_⟩
  exact hInv _ _ (congruent_snoc hxy)

theorem continuous_snoc_const (b : Fin m → VF M) {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VF M) G] :
    Continuous (fun x : Fin 1 → VF M => (Fin.snoc b (x 0) : Fin (m + 1) → VF M)) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact continuous_apply 0
  · simp only [Fin.snoc_castSucc]
    exact continuous_const

end Slice

/-! ### Restricting a map that fixes the first `m` coordinates -/

section SliceMap

/-- The real codes of `(y, v) ↦ (y_{m+1}, v)`. -/
def lastCodes (z : Fin (m + 1) ⊕ Fin s → M) : Fin 1 ⊕ Fin s → M :=
  Sum.elim (fun _ => z (.inl (Fin.last m))) (z ∘ Sum.inr)

omit [M ⊨ Axioms.ACVF] in
theorem lastCodes_mixedValues (p : Mixed M (m + 1) s) :
    lastCodes (mixedValues p) = mixedValues ((fun _ => p.1 (Fin.last m), p.2) : Mixed M 1 s) := by
  funext i
  rcases i with i | i <;> rfl

omit [M ⊨ Axioms.ACVF] in
theorem lastCodes_decode (c : (rawMixedSpace (M := M) (m + 1) s).domain) :
    lastCodes c.val = mixedValues
      ((fun _ => ((rawMixedSpace (M := M) (m + 1) s).decode c).1 (Fin.last m),
        ((rawMixedSpace (M := M) (m + 1) s).decode c).2) : Mixed M 1 s) := by
  rw [← lastCodes_mixedValues, mixedValues_decode]

/-- The definable map `(y, v) ↦ (y_{m+1}, v)`. -/
def lastMap {T : Set M} (A : DefSet (rawMixedSpace (M := M) (m + 1) s) T) :
    Map A (DefSet.univ (rawMixedSpace (M := M) 1 s) T) :=
  Map.ofCodes A (fun p : Mixed M (m + 1) s => ((fun _ => p.1 (Fin.last m), p.2) : Mixed M 1 s))
    lastCodes (by rintro (i | i) <;> exact Set.DefinableFun.proj LRV)
    (fun c => (lastCodes_decode c) ▸ mixedValues_mem_domain _)
    (fun c => mixedValues_injective ((mixedValues_decode _).trans (lastCodes_decode c)))

variable {X : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
  {X' : DefSet (rawMixedSpace (M := M) (m + 1) s) S} {b : Fin m → VF M}
  {hS : S ∪ Set.range (vfValues b) ⊆ S'}

omit [M ⊨ Axioms.ACVF] in
theorem fix_init {f : Map X X'} (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
    (q : sliceSet X b hS) : Fin.init (f (liftElem q)).val.1 = b := by
  rw [hfix]
  exact Fin.init_snoc _ _

omit [M ⊨ Axioms.ACVF] in
theorem fix_snoc {f : Map X X'} (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
    (q : sliceSet X b hS) :
    (Fin.snoc b ((f (liftElem q)).val.1 (Fin.last m)) : Fin (m + 1) → VF M) =
      (f (liftElem q)).val.1 :=
  (eq_snoc_of_init (fix_init hfix q)).symm

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap_mem {f : Map X X'} (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
    (q : sliceSet X b hS) :
    ((fun _ => (f (liftElem q)).val.1 (Fin.last m), (f (liftElem q)).val.2) : Mixed M 1 s) ∈
      (sliceSet X' b hS).carrier := by
  show ((Fin.snoc b ((f (liftElem q)).val.1 (Fin.last m)), (f (liftElem q)).val.2) :
    Mixed M (m + 1) s) ∈ X'.carrier
  rw [fix_snoc hfix q]
  exact (f (liftElem q)).property

/-- The restriction `f_b : X_b → X'_b` of a map fixing the first `m` VF
coordinates, `(x, t) ↦ (y_{m+1}, v)` where `f((b, x), t) = ((b, y_{m+1}), v)`. -/
def sliceMap (f : Map X X') (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1) :
    Map (sliceSet X b hS) (sliceSet X' b hS) :=
  ((lastMap _).comp ((extendMapBase (Set.subset_union_left.trans hS) f).comp
    (liftElemMap X b hS))).corestrict (fun q => sliceMap_mem hfix q)

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap_val (f : Map X X') (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
    (q : sliceSet X b hS) :
    (sliceMap f hfix q).val =
      ((fun _ => (f ⟨(Fin.snoc b (q.val.1 0), q.val.2), q.property⟩).val.1 (Fin.last m),
        (f ⟨(Fin.snoc b (q.val.1 0), q.val.2), q.property⟩).val.2) : Mixed M 1 s) := rfl

variable {f : Map X X'} (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
include hfix

omit [M ⊨ Axioms.ACVF] in
theorem liftElem_sliceMap (q : sliceSet X b hS) : liftElem (sliceMap f hfix q) = f (liftElem q) :=
  Subtype.ext (Prod.ext (fix_snoc hfix q) rfl)

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap_injective (hf : Function.Injective f) :
    Function.Injective (sliceMap (b := b) (hS := hS) f hfix) := by
  intro q q' h
  have h1 : f (liftElem q) = f (liftElem q') := by
    rw [← liftElem_sliceMap hfix q, ← liftElem_sliceMap hfix q', h]
  have h2 : ((Fin.snoc b (q.val.1 0), q.val.2) : Mixed M (m + 1) r) =
      (Fin.snoc b (q'.val.1 0), q'.val.2) := congrArg Subtype.val (hf h1)
  have h3 := congrArg Prod.snd h2
  apply Subtype.ext
  exact Prod.ext (snoc_last_eq_iff.mp (congrArg Prod.fst h2)) h3

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (sliceMap (b := b) (hS := hS) f hfix) := by
  intro q'
  obtain ⟨p, hp⟩ := hf (liftElem q')
  have hinit : Fin.init p.val.1 = b := by
    rw [← hfix p, hp]
    exact Fin.init_snoc _ _
  have hpX : ((Fin.snoc b (p.val.1 (Fin.last m)), p.val.2) : Mixed M (m + 1) r) ∈ X.carrier := by
    rw [← eq_snoc_of_init hinit]
    exact p.property
  refine ⟨⟨(fun _ => p.val.1 (Fin.last m), p.val.2), hpX⟩, ?_⟩
  have hl : liftElem (⟨(fun _ => p.val.1 (Fin.last m), p.val.2), hpX⟩ : sliceSet X b hS) = p :=
    Subtype.ext (Prod.ext (eq_snoc_of_init hinit).symm rfl)
  apply Subtype.ext
  change ((fun _ => (f (liftElem (⟨(fun _ => p.val.1 (Fin.last m), p.val.2), hpX⟩ :
    sliceSet X b hS))).val.1 (Fin.last m), (f (liftElem (⟨(fun _ => p.val.1 (Fin.last m), p.val.2),
      hpX⟩ : sliceSet X b hS))).val.2) : Mixed M 1 s) = q'.val
  rw [hl, hp]
  exact Prod.ext (fin_one_ext (by simp)) rfl

omit [M ⊨ Axioms.ACVF] in
/-- The restriction of a bijection is a bijection. -/
theorem sliceMap_bijective (hf : Function.Bijective f) :
    Function.Bijective (sliceMap (b := b) (hS := hS) f hfix) :=
  ⟨sliceMap_injective hfix hf.1, sliceMap_surjective hfix hf.2⟩

omit [M ⊨ Axioms.ACVF] in
theorem graphFibre_init {u : Fin r → RVInfinity M} {v : Fin s → RVInfinity M}
    {a c : Fin (m + 1) → VF M} (h : graphFibre f u v a c) : Fin.init c = Fin.init a := by
  obtain ⟨p, hp, hfp⟩ := h
  simpa [hfp, hp] using hfix p

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap_graphFibre_iff (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (x y : Fin 1 → VF M) :
    graphFibre (sliceMap (b := b) (hS := hS) f hfix) u v x y ↔
      graphFibre f u v (Fin.snoc b (x 0)) (Fin.snoc b (y 0)) := by
  constructor
  · rintro ⟨q, hq, hgq⟩
    refine ⟨liftElem q, ?_, ?_⟩
    · rw [liftElem_val, hq]
    · rw [← liftElem_sliceMap hfix q, liftElem_val, hgq]
  · rintro ⟨p, hp, hfp⟩
    have hq : ((Fin.snoc b (x 0), u) : Mixed M (m + 1) r) ∈ X.carrier := hp ▸ p.property
    refine ⟨⟨(x, u), hq⟩, rfl, ?_⟩
    have hl : liftElem (⟨(x, u), hq⟩ : sliceSet X b hS) = p := Subtype.ext hp.symm
    change ((fun _ => (f (liftElem (⟨(x, u), hq⟩ : sliceSet X b hS))).val.1 (Fin.last m),
      (f (liftElem (⟨(x, u), hq⟩ : sliceSet X b hS))).val.2) : Mixed M 1 s) = (y, v)
    rw [hl, hfp]
    exact Prod.ext (fin_one_ext (by simp)) rfl

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap_graphFibreSource (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (sliceMap (b := b) (hS := hS) f hfix) u v =
      {x | (Fin.snoc b (x 0) : Fin (m + 1) → VF M) ∈ graphFibreSource f u v} := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, (sliceMap_graphFibre_iff hfix u v x y).mp hy⟩
  · rintro ⟨c, hc⟩
    have hinit : Fin.init c = b := by
      rw [graphFibre_init hfix hc]
      exact Fin.init_snoc _ _
    refine ⟨fun _ => c (Fin.last m), (sliceMap_graphFibre_iff hfix u v x _).mpr ?_⟩
    show graphFibre f u v (Fin.snoc b (x 0)) (Fin.snoc b (c (Fin.last m)))
    rw [← eq_snoc_of_init hinit]
    exact hc

omit [M ⊨ Axioms.ACVF] in
theorem sliceMap_graphFibreRange (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange (sliceMap (b := b) (hS := hS) f hfix) u v =
      {y | (Fin.snoc b (y 0) : Fin (m + 1) → VF M) ∈ graphFibreRange f u v} := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (sliceMap_graphFibre_iff hfix u v x y).mp hx⟩
  · rintro ⟨a, ha⟩
    have hinit : Fin.init a = b := by
      rw [← graphFibre_init hfix ha]
      exact Fin.init_snoc _ _
    refine ⟨fun _ => a (Fin.last m), (sliceMap_graphFibre_iff hfix u v _ y).mpr ?_⟩
    show graphFibre f u v (Fin.snoc b (a (Fin.last m))) (Fin.snoc b (y 0))
    rw [← eq_snoc_of_init hinit]
    exact ha

theorem sliceMap_graphFibreMap (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    {x : Fin 1 → VF M} (hx : x ∈ graphFibreSource (sliceMap (b := b) (hS := hS) f hfix) u v) :
    graphFibreMap (sliceMap (b := b) (hS := hS) f hfix) u v x =
      fun _ => graphFibreMap f u v (Fin.snoc b (x 0)) (Fin.last m) := by
  have h1 := (sliceMap_graphFibre_iff hfix u v x _).mp (graphFibreMap_graph _ u v hx)
  have hx' : (Fin.snoc b (x 0) : Fin (m + 1) → VF M) ∈ graphFibreSource f u v := ⟨_, h1⟩
  have h2 := graphFibre_functional f u v h1 (graphFibreMap_graph f u v hx')
  apply fin_one_ext
  simpa using congrFun h2 (Fin.last m)

/-- The restriction of a proper covariant map is proper covariant: the radii
of `f` in the last coordinate serve for `f_b`. -/
theorem sliceMap_properCovariant (hf : ProperCovariant f) :
    ProperCovariant (sliceMap (b := b) (hS := hS) f hfix) := by
  refine ⟨sliceSet_vfBounded hf.sourceVFBounded, ?_, sliceSet_rvBounded hf.sourceRVBounded, ?_,
    fun u v => ?_⟩
  · obtain ⟨γ, hγ⟩ := hf.imageVFBounded
    refine ⟨γ, ?_⟩
    rintro _ ⟨q, rfl⟩ i
    rw [Subsingleton.elim i 0]
    exact hγ _ ⟨liftElem q, rfl⟩ (Fin.last m)
  · obtain ⟨γ, hγ⟩ := hf.imageRVBounded
    refine ⟨γ, ?_⟩
    rintro _ ⟨q, rfl⟩ i
    exact hγ _ ⟨liftElem q, rfl⟩ i
  · obtain ⟨α, β, hα, hβ, hInvα, hInvβ, hcov⟩ := hf.radii u v
    have hbase : graphFibreBase S u v ⊆ graphFibreBase S' u v :=
      Set.union_subset_union_left _ (Set.union_subset_union_left _ (Set.subset_union_left.trans hS))
    refine ⟨fun _ => α (Fin.last m), fun _ => β (Fin.last m), fun _ => (hα _).mono hbase,
      fun _ => (hβ _).mono hbase, ?_, ?_, ?_⟩
    · rw [sliceMap_graphFibreSource hfix]
      intro x y hxy
      exact hInvα _ _ (congruent_snoc hxy)
    · rw [sliceMap_graphFibreRange hfix]
      intro x y hxy
      exact hInvβ _ _ (congruent_snoc hxy)
    · intro x hx y hy hxy
      have hx' : (Fin.snoc b (x 0) : Fin (m + 1) → VF M) ∈ graphFibreSource f u v := by
        have h := hx
        rwa [sliceMap_graphFibreSource hfix] at h
      have hy' : (Fin.snoc b (y 0) : Fin (m + 1) → VF M) ∈ graphFibreSource f u v := by
        have h := hy
        rwa [sliceMap_graphFibreSource hfix] at h
      have h := hcov _ hx' _ hy' (congruent_snoc hxy)
      rw [sliceMap_graphFibreMap hfix u v hx, sliceMap_graphFibreMap hfix u v hy]
      exact fun _ => h (Fin.last m)

/-- The restriction of a map continuous on its graph fibres is continuous on
its graph fibres. -/
theorem sliceMap_continuous {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (hf : ContinuousOnGraphFibres (G := G) f) :
    ContinuousOnGraphFibres (G := G) (sliceMap (b := b) (hS := hS) f hfix) := by
  intro u v
  have hπ : Continuous (fun w : Fin (m + 1) → VF M => (fun _ : Fin 1 => w (Fin.last m))) :=
    continuous_pi fun _ => continuous_apply _
  have hmaps : Set.MapsTo (fun x : Fin 1 → VF M => (Fin.snoc b (x 0) : Fin (m + 1) → VF M))
      (graphFibreSource (sliceMap (b := b) (hS := hS) f hfix) u v) (graphFibreSource f u v) := by
    intro x hx
    rw [sliceMap_graphFibreSource hfix] at hx
    exact hx
  refine (hπ.comp_continuousOn ((hf u v).comp (continuous_snoc_const b (G := G)).continuousOn
    hmaps)).congr ?_
  intro x hx
  exact sliceMap_graphFibreMap hfix u v hx

omit [M ⊨ Axioms.ACVF] in
theorem fix_inverse (hf : Function.Bijective f) :
    ∀ p : X', Fin.init ((f.inverse hf) p).val.1 = Fin.init p.val.1 := by
  intro p
  have h := hfix (f.inverse hf p)
  rw [Map.apply_inverse] at h
  exact h.symm

omit [M ⊨ Axioms.ACVF] in
/-- The inverse of the restriction is the restriction of the inverse. -/
theorem sliceMap_inverse (hf : Function.Bijective f)
    (hbij : Function.Bijective (sliceMap (b := b) (hS := hS) f hfix)) :
    (sliceMap (b := b) (hS := hS) f hfix).inverse hbij =
      sliceMap (b := b) (hS := hS) (f.inverse hf) (fix_inverse hfix hf) := by
  apply Map.ext
  intro q'
  apply hbij.1
  rw [Map.apply_inverse]
  apply Subtype.ext
  change q'.val = ((fun _ => (f (liftElem (sliceMap (f.inverse hf) (fix_inverse hfix hf) q'))).val.1
    (Fin.last m), (f (liftElem (sliceMap (f.inverse hf) (fix_inverse hfix hf) q'))).val.2) :
      Mixed M 1 s)
  rw [liftElem_sliceMap (fix_inverse hfix hf) q', Map.apply_inverse]
  exact Prod.ext (fin_one_ext (by simp)) rfl

/-- The restriction of a proper covariant homeomorphism fixing the first `m`
VF coordinates is a proper covariant homeomorphism over `S'`. -/
theorem sliceMap_homeomorphism {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (hf : ProperCovariantHomeomorphism (G := G) f) :
    ProperCovariantHomeomorphism (G := G) (sliceMap (b := b) (hS := hS) f hfix) := by
  have hbij := sliceMap_bijective (b := b) (hS := hS) hfix hf.bijective
  refine ⟨hbij, sliceMap_properCovariant hfix hf.covariant, sliceMap_continuous hfix hf.continuous,
    ?_, ?_⟩
  · rw [sliceMap_inverse hfix hf.bijective hbij]
    exact sliceMap_properCovariant _ hf.inverseCovariant
  · rw [sliceMap_inverse hfix hf.bijective hbij]
    exact sliceMap_continuous _ hf.inverseContinuous

end SliceMap

/-! ### The derivative of the restriction -/

section Derivative

variable {X : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
  {X' : DefSet (rawMixedSpace (M := M) (m + 1) s) S} {b : Fin m → VF M}
  {hS : S ∪ Set.range (vfValues b) ⊆ S'}

/-- The linear map `x ↦ (0, …, 0, x)`. -/
def lastEmbedding : (Fin 1 → VF M) →ₗ[VF M] (Fin (m + 1) → VF M) :=
  (LinearMap.single (VF M) (fun _ : Fin (m + 1) => VF M) (Fin.last m)).comp (LinearMap.proj 0)

/-- The `i`-th coordinate, as a linear map to `VF¹`. -/
def coordProj (i : Fin (m + 1)) : (Fin (m + 1) → VF M) →ₗ[VF M] (Fin 1 → VF M) :=
  LinearMap.pi (fun _ => LinearMap.proj i)

theorem lastEmbedding_apply (x : Fin 1 → VF M) :
    lastEmbedding (m := m) x = Pi.single (Fin.last m) (x 0) := rfl

theorem coordProj_apply (i : Fin (m + 1)) (y : Fin (m + 1) → VF M) :
    coordProj i y = fun _ => y i := rfl

theorem snoc_eq_affine (b : Fin m → VF M) (x : Fin 1 → VF M) :
    (Fin.snoc b (x 0) : Fin (m + 1) → VF M) = lastEmbedding x + Fin.snoc b 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [lastEmbedding_apply]
  · simp [lastEmbedding_apply]

theorem hasVFDerivativeAt_coordProj (i : Fin (m + 1)) (a : Fin (m + 1) → VF M) :
    HasVFDerivativeAt (coordProj i) a (coordProj i) := by
  have h := hasVFDerivativeAt_affine (coordProj (M := M) i) 0 a
  have he : (fun x => coordProj (M := M) i x + 0) = coordProj i := funext fun x => add_zero _
  rwa [he] at h

theorem hasVFDerivativeAt_snoc (b : Fin m → VF M) (x : Fin 1 → VF M) :
    HasVFDerivativeAt (fun x : Fin 1 → VF M => (Fin.snoc b (x 0) : Fin (m + 1) → VF M)) x
      lastEmbedding := by
  have h := hasVFDerivativeAt_affine (lastEmbedding (M := M) (m := m)) (Fin.snoc b 0) x
  have he : (fun x => lastEmbedding x + Fin.snoc b 0) =
      fun x : Fin 1 → VF M => (Fin.snoc b (x 0) : Fin (m + 1) → VF M) :=
    funext fun x => (snoc_eq_affine b x).symm
  rwa [he] at h

theorem snoc_mem_vfBall {x y : Fin 1 → VF M} {ρ : Gamma M} (h : x ∈ vfBall y ρ) :
    (Fin.snoc b (x 0) : Fin (m + 1) → VF M) ∈ vfBall (Fin.snoc b (y 0)) ρ := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h 0
  · simpa using mem_vfBall_self (Fin.snoc b (y 0) : Fin (m + 1) → VF M) ρ j.castSucc

/-- The derivative of the restriction. A chart of `f` agrees with the
coordinate projections in the first `m` coordinates on a ball, so the first
`m` rows of `L` are unit rows; `L` is lower triangular and its determinant is
its last diagonal entry, the derivative of `f_b`. -/
theorem sliceMap_derivative (f : Map X X') (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
    (q : sliceSet X b hS) {L : (Fin (m + 1) → VF M) →ₗ[VF M] (Fin (m + 1) → VF M)}
    (hL : HasMixedVFDerivativeAt f ⟨(Fin.snoc b (q.val.1 0), q.val.2), q.property⟩ L) :
    ∃ L₁ : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M),
      HasMixedVFDerivativeAt (sliceMap f hfix) q L₁ ∧
        (LinearMap.toMatrix' L₁).det = (LinearMap.toMatrix' L).det := by
  obtain ⟨F, ⟨ρ, hρ⟩, hFL⟩ := hL
  have hFL' : HasVFDerivativeAt F (Fin.snoc b (q.val.1 0)) L := hFL
  -- The first `m` rows of `L` are unit rows.
  have hrow : ∀ (j : Fin m) (w : Fin (m + 1) → VF M), L w j.castSucc = w j.castSucc := by
    intro j w
    have hcomp : HasVFDerivativeAt (coordProj j.castSucc ∘ F) (Fin.snoc b (q.val.1 0))
        ((coordProj j.castSucc).comp L) :=
      HasVFDerivativeAt.comp (hasVFDerivativeAt_coordProj j.castSucc _) hFL'
    have heq : Set.EqOn (coordProj j.castSucc ∘ F) (coordProj j.castSucc)
        (vfBall (Fin.snoc b (q.val.1 0)) ρ) := by
      intro y hy
      obtain ⟨hyX, hfy⟩ := hρ y hy
      have h1 : (f ⟨(y, q.val.2), hyX⟩).val.1 = F y := congrArg Prod.fst hfy
      have h2 : (f ⟨(y, q.val.2), hyX⟩).val.1 j.castSucc = y j.castSucc :=
        congrFun (hfix ⟨(y, q.val.2), hyX⟩) j
      rw [h1] at h2
      funext k
      simp [coordProj_apply, h2]
    have hD := (hcomp.congr_on_vfBall heq).unique (hasVFDerivativeAt_coordProj j.castSucc _)
    have h := congrFun (LinearMap.congr_fun hD w) 0
    simpa [coordProj_apply] using h
  refine ⟨(coordProj (Fin.last m)).comp (L.comp lastEmbedding),
    ⟨fun x => coordProj (Fin.last m) (F (Fin.snoc b (x 0))), ⟨ρ, fun x hx => ?_⟩, ?_⟩, ?_⟩
  · -- the chart
    obtain ⟨hxX, hfx⟩ := hρ _ (snoc_mem_vfBall (b := b) hx)
    refine ⟨hxX, ?_⟩
    have e1 : (f ⟨(Fin.snoc b (x 0), q.val.2), hxX⟩).val.1 = F (Fin.snoc b (x 0)) :=
      congrArg Prod.fst hfx
    have e2 : (f ⟨(Fin.snoc b (x 0), q.val.2), hxX⟩).val.2 =
        (f ⟨(Fin.snoc b (q.val.1 0), q.val.2), q.property⟩).val.2 := by
      have h := congrArg Prod.snd hfx
      exact h
    have e3 : (fun _ : Fin 1 => (f ⟨(Fin.snoc b (x 0), q.val.2), hxX⟩).val.1 (Fin.last m)) =
        coordProj (Fin.last m) (F (Fin.snoc b (x 0))) := by
      rw [e1]
      rfl
    exact Prod.ext e3 e2
  · -- the derivative of the chart
    have h1 : HasVFDerivativeAt
        (F ∘ fun x : Fin 1 → VF M => (Fin.snoc b (x 0) : Fin (m + 1) → VF M))
        q.val.1 (L.comp lastEmbedding) :=
      HasVFDerivativeAt.comp hFL' (hasVFDerivativeAt_snoc b q.val.1)
    exact HasVFDerivativeAt.comp (hasVFDerivativeAt_coordProj (Fin.last m) _) h1
  · -- the determinant
    have h1 : (LinearMap.toMatrix' ((coordProj (Fin.last m)).comp (L.comp lastEmbedding))).det =
        LinearMap.toMatrix' L (Fin.last m) (Fin.last m) := by
      rw [Matrix.det_fin_one, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]
      simp [coordProj_apply, lastEmbedding_apply]
    have hlow : (LinearMap.toMatrix' L).IsLowerTriangular := by
      intro i k hik
      have hik' : i < k := OrderDual.toDual_lt_toDual.mp hik
      have hi : i ≠ Fin.last m := by
        rintro rfl
        exact (Fin.le_last k).not_gt hik'
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      rw [LinearMap.toMatrix'_apply, hrow j]
      exact Pi.single_eq_of_ne (ne_of_lt hik') _
    have hdiag : ∀ j : Fin m, LinearMap.toMatrix' L j.castSucc j.castSucc = 1 := by
      intro j
      rw [LinearMap.toMatrix'_apply, hrow j]
      exact Pi.single_eq_same _ _
    rw [h1, Matrix.det_of_isLowerTriangular _ hlow, Fin.prod_univ_castSucc]
    simp only [hdiag, Finset.prod_const_one, one_mul]

end Derivative

/-! ### Good points -/

section GoodPoints

set_option backward.isDefEq.respectTransparency true in
/-- Evaluation at `(x, b)` through `finSuccEquiv`: first evaluate the
coefficients at `b`, then the polynomial in the first variable at `x`. -/
theorem eval₂_cons_eq_eval₂_finSuccEquiv {K F : Type*} [CommRing K] [CommRing F] (φ : K →+* F)
    (x : F) (b : Fin m → F) (Q : MvPolynomial (Fin (m + 1)) K) :
    MvPolynomial.eval₂ φ (Fin.cons x b : Fin (m + 1) → F) Q =
      Polynomial.eval₂ (MvPolynomial.eval₂Hom φ b) x (MvPolynomial.finSuccEquiv K m Q) := by
  have h : MvPolynomial.eval₂Hom φ (Fin.cons x b : Fin (m + 1) → F) =
      (Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom φ b) x).comp
        (MvPolynomial.finSuccEquiv K m).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, Polynomial.coe_eval₂RingHom]
      change φ a = Polynomial.eval₂ _ x (MvPolynomial.finSuccEquiv K m (MvPolynomial.C a))
      rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        Polynomial.eval₂_C, MvPolynomial.eval₂Hom_C]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Polynomial.coe_eval₂RingHom]
      change (Fin.cons x b : Fin (m + 1) → F) i =
        Polynomial.eval₂ _ x (MvPolynomial.finSuccEquiv K m (MvPolynomial.X i))
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval₂_X, Fin.cons_zero]
      · rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval₂_C, MvPolynomial.eval₂Hom_X',
          Fin.cons_succ]
  exact RingHom.congr_fun h Q

/-- Let `K ≤ L` be subfields of `F`, `b ∈ Lᵐ`, and `R` a polynomial in one
variable over `K[X₁, …, Xₘ]` whose leading coefficient does not vanish at `b`.
Then every root of `R(b, ·)` is algebraic over `L`. -/
theorem isAlgebraic_of_finSucc_root {F : Type*} [Field F] {K L : Subfield F} (hKL : K ≤ L)
    (b : Fin m → F) (hb : ∀ j, b j ∈ L) (R : Polynomial (MvPolynomial (Fin m) K))
    (hlead : MvPolynomial.eval₂ K.subtype b R.leadingCoeff ≠ 0) (x : F)
    (hx : Polynomial.eval₂ (MvPolynomial.eval₂Hom K.subtype b) x R = 0) : IsAlgebraic L x := by
  let bL : Fin m → L := fun j => ⟨b j, hb j⟩
  let φ : MvPolynomial (Fin m) K →+* L := MvPolynomial.eval₂Hom (Subfield.inclusion hKL) bL
  have hφR : L.subtype.comp φ = MvPolynomial.eval₂Hom K.subtype b := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, φ, MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply, φ, MvPolynomial.eval₂Hom_X']
      rfl
  refine ⟨R.map φ, ?_, ?_⟩
  · intro h0
    apply hlead
    have h1 : φ R.leadingCoeff = 0 := by
      have h := Polynomial.coeff_map (p := R) φ R.natDegree
      rw [h0, Polynomial.coeff_zero] at h
      exact h.symm
    have h2 := RingHom.congr_fun hφR R.leadingCoeff
    rw [RingHom.comp_apply, h1, map_zero] at h2
    exact h2.symm
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, Subfield.algebraMap_ofSubfield, hφR]
    exact hx

/-- Good points for a set `Bad` of VF dimension `< m + 1`: there is a nonzero
polynomial `P` over the VF parameter field of `S` such that, for every point
`b` with `P(b) ≠ 0`, the slice `Bad_b` has VF dimension `0` over any small base
`S'` containing `S` and `b`. Here `P` is the leading coefficient of a nonzero
polynomial vanishing on `Bad`, viewed as a polynomial in the last variable. -/
theorem exists_good_polynomial (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Bad : DefSet (rawMixedSpace (M := M) (m + 1) r) S)
    (hBad : vfDim (rawRVSpace (M := M) 1) Bad < m + 1) :
    ∃ P : MvPolynomial (Fin m) (vfParameterField S), P ≠ 0 ∧
      ∀ (b : Fin m → VF M) {S' : Set M} (hS : S ∪ Set.range (vfValues b) ⊆ S'),
        Cardinal.mk S' < κ → P.eval₂ (vfParameterField S).subtype b ≠ 0 →
          vfDim (rawRVSpace (M := M) 1) (sliceSet Bad b hS) < 1 := by
  obtain ⟨Q, hQ0, hQ⟩ := GoodPoints.exists_polynomial_vanishing_of_dim_lt hc hs hsmall Bad hBad
  obtain ⟨R, hR⟩ : ∃ R, MvPolynomial.finSuccEquiv (vfParameterField S) m
      (MvPolynomial.rename (finRotate (m + 1)) Q) = R := ⟨_, rfl⟩
  have hR0 : R ≠ 0 := by
    rintro rfl
    apply hQ0
    apply MvPolynomial.rename_injective _ (finRotate (m + 1)).injective
    rw [map_zero]
    exact (MvPolynomial.finSuccEquiv _ m).injective (hR.trans (map_zero _).symm)
  refine ⟨R.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hR0, ?_⟩
  intro b S' hS hsmall' hPb
  have hKL : vfParameterField (M := M) S ≤ vfParameterField S' :=
    Subfield.closure_mono (fun x hx => hS (Or.inl hx))
  have hbL : ∀ j, b j ∈ vfParameterField (M := M) S' :=
    fun j => Subfield.subset_closure (hS (Or.inr ⟨j, rfl⟩))
  apply mixed_vfDim_lt_of_no_independent hc hs hsmall' _ (rawRVSpace_rvCoded 1) Nat.zero_lt_one
  intro p hInd
  apply hInd.transcendental 0
  have hx : MvPolynomial.eval₂ (vfParameterField S).subtype
      (Fin.snoc b (p.val.1 0) : Fin (m + 1) → VF M) Q = 0 := hQ ⟨_, p.property⟩
  have hx' : MvPolynomial.eval₂ (vfParameterField S).subtype
      (Fin.cons (p.val.1 0) b : Fin (m + 1) → VF M)
      (MvPolynomial.rename (finRotate (m + 1)) Q) = 0 := by
    rw [MvPolynomial.eval₂_rename]
    rw [Fin.snoc_eq_cons_rotate] at hx
    exact hx
  rw [eval₂_cons_eq_eval₂_finSuccEquiv, hR] at hx'
  exact isAlgebraic_of_finSucc_root hKL b hbL R hPb (p.val.1 0) hx'

omit [M ⊨ Axioms.ACVF] in
theorem sliceSet_carrier_eq_empty {Bad : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
    (h : Bad.carrier = ∅) (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    (sliceSet Bad b hS).carrier = ∅ := by
  ext p
  constructor
  · intro hp
    have h' : ((Fin.snoc b (p.1 0), p.2) : Mixed M (m + 1) r) ∈ Bad.carrier := hp
    rw [h] at h'
    exact h'.elim
  · intro hp
    exact hp.elim

/-- `exists_good_polynomial` in the form of `Morphism.bad_small`: a set that
has VF dimension `< m + 1` or is empty has good points with slices of VF
dimension `0` or empty. -/
theorem exists_good_polynomial_or_empty (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Bad : DefSet (rawMixedSpace (M := M) (m + 1) r) S)
    (hBad : vfDim (rawRVSpace (M := M) 1) Bad < m + 1 ∨ Bad.carrier = ∅) :
    ∃ P : MvPolynomial (Fin m) (vfParameterField S), P ≠ 0 ∧
      ∀ (b : Fin m → VF M) {S' : Set M} (hS : S ∪ Set.range (vfValues b) ⊆ S'),
        Cardinal.mk S' < κ → P.eval₂ (vfParameterField S).subtype b ≠ 0 →
          vfDim (rawRVSpace (M := M) 1) (sliceSet Bad b hS) < 1 ∨
            (sliceSet Bad b hS).carrier = ∅ := by
  rcases hBad with hBad | hBad
  · obtain ⟨P, hP0, hP⟩ := exists_good_polynomial hc hs hsmall Bad hBad
    exact ⟨P, hP0, fun b S' hS h1 h2 => Or.inl (hP b hS h1 h2)⟩
  · exact ⟨1, one_ne_zero, fun b S' hS _ _ => Or.inr (sliceSet_carrier_eq_empty hBad b hS)⟩

end GoodPoints

/-! ### Slice objects and morphisms of `μVF^◇[1]` -/

section Objects

variable {X : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
  {X' : DefSet (rawMixedSpace (M := M) (m + 1) s) S}

/-- The form `(x, t) ↦ ω((b, x), t)` on the slice, over `S'`. -/
def sliceForm (X : DefSet (rawMixedSpace (M := M) (m + 1) r) S)
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    Map (sliceSet X b hS) (DefSet.univ (rawGammaPresentation (M := M)) S') :=
  (extendMapBase (Set.subset_union_left.trans hS) ω).comp (liftElemMap X b hS)

theorem sliceForm_apply (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S))
    {b : Fin m → VF M} {hS : S ∪ Set.range (vfValues b) ⊆ S'} (q : sliceSet X b hS) :
    gammaMapValue (sliceForm X ω b hS) q =
      gammaMapValue ω ⟨(Fin.snoc b (q.val.1 0), q.val.2), q.property⟩ := rfl

/-- Form covariance of `X` (as in `VFObject.formCovariant`) gives form
covariance of the slice, with the radius of the last coordinate. -/
theorem sliceFormCovariant_of (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hcov : ∀ t : Fin r → RVInfinity M, ∃ α : Fin (m + 1) → Gamma M, NamedRadii S t α ∧
      ∀ x y (hx : (x, t) ∈ X.carrier) (hy : (y, t) ∈ X.carrier), Congruent α x y →
        gammaMapValue ω ⟨(x, t), hx⟩ = gammaMapValue ω ⟨(y, t), hy⟩)
    (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S') :
    ∀ t : Fin r → RVInfinity M, ∃ α : Fin 1 → Gamma M, NamedRadii S' t α ∧
      ∀ x y (hx : ((Fin.snoc b (x 0), t) : Mixed M (m + 1) r) ∈ X.carrier)
        (hy : ((Fin.snoc b (y 0), t) : Mixed M (m + 1) r) ∈ X.carrier),
        Congruent α x y → gammaMapValue ω ⟨_, hx⟩ = gammaMapValue ω ⟨_, hy⟩ := by
  intro t
  obtain ⟨α, hα, h⟩ := hcov t
  exact ⟨fun _ => α (Fin.last m), fun _ => (hα (Fin.last m)).mono
    (Set.union_subset_union_left _ (Set.subset_union_left.trans hS)),
    fun x y hx hy hxy => h _ _ hx hy (congruent_snoc hxy)⟩

/-- The slice `(X_b, ω((b, ·), ·))` of a proper invariant measured VF set, as
an object of `μVF^◇[1]` over `S'`. It needs finite RV fibres of `X` and form
covariance on the slice (`sliceFormCovariant_of` derives the latter from form
covariance of `X`). -/
def sliceObject (X : DefSet (rawMixedSpace (M := M) (m + 1) r) S)
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hX : ProperInvariant S X.carrier)
    (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S')
    (hcov : ∀ t : Fin r → RVInfinity M, ∃ α : Fin 1 → Gamma M, NamedRadii S' t α ∧
      ∀ x y (hx : ((Fin.snoc b (x 0), t) : Mixed M (m + 1) r) ∈ X.carrier)
        (hy : ((Fin.snoc b (y 0), t) : Mixed M (m + 1) r) ∈ X.carrier),
        Congruent α x y → gammaMapValue ω ⟨_, hx⟩ = gammaMapValue ω ⟨_, hy⟩)
    (hfin : ∀ x : Fin (m + 1) → VF M, {u | (x, u) ∈ X.carrier}.Finite) :
    VFObject (M := M) S' 1 where
  labels := r
  carrier := sliceSet X b hS
  form := sliceForm X ω b hS
  proper := sliceSet_properInvariant hX
  formCovariant t := hcov t
  finiteRV x := hfin (Fin.snoc b (x 0))

/-- The slice of an object of `μVF^◇[m + 1]` over `S`, as an object of
`μVF^◇[1]` over `S'`. -/
def sliceVFObject (A : VFObject (M := M) S (m + 1)) (b : Fin m → VF M)
    (hS : S ∪ Set.range (vfValues b) ⊆ S') : VFObject (M := M) S' 1 :=
  sliceObject A.carrier A.form A.proper b hS (sliceFormCovariant_of A.form A.formCovariant b hS)
    A.finiteRV

/-- The measure identity for the restriction at a point of the slice outside
`Bad_b`, from the measure identity for `f` outside `Bad`. -/
theorem sliceMap_measure {b : Fin m → VF M} {hS : S ∪ Set.range (vfValues b) ⊆ S'}
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S))
    (ω' : Map X' (DefSet.univ (rawGammaPresentation (M := M)) S))
    (f : Map X X') (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
    (Bad : DefSet (rawMixedSpace (M := M) (m + 1) r) S)
    (hmeasure : ∀ p : X, p.val ∉ Bad.carrier → ∃ L, HasMixedVFDerivativeAt f p L ∧
      vfValue (LinearMap.toMatrix' L).det = (gammaMapValue ω p / gammaMapValue ω' (f p)).val)
    (q : sliceSet X b hS) (hq : q.val ∉ (sliceSet Bad b hS).carrier) :
    ∃ L₁ : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M),
      HasMixedVFDerivativeAt (sliceMap f hfix) q L₁ ∧
        vfValue (LinearMap.toMatrix' L₁).det =
          (gammaMapValue (sliceForm X ω b hS) q /
            gammaMapValue (sliceForm X' ω' b hS) (sliceMap f hfix q)).val := by
  obtain ⟨L, hL, hdet⟩ := hmeasure (liftElem q) hq
  obtain ⟨L₁, hL₁, hdet₁⟩ := sliceMap_derivative f hfix q hL
  refine ⟨L₁, hL₁, ?_⟩
  rw [hdet₁, hdet]
  change (gammaMapValue ω (liftElem q) / gammaMapValue ω' (f (liftElem q))).val =
    (gammaMapValue ω (liftElem q) / gammaMapValue ω' (liftElem (sliceMap f hfix q))).val
  rw [liftElem_sliceMap hfix q]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

variable (G) in
/-- The restriction of a map fixing the first `m` VF coordinates to the slices
over a good point `b` is a morphism of `μVF^◇[1]` over `S'`. The map is a proper
covariant homeomorphism with the measure identity outside `Bad`; the point `b`
is good for `Bad` (`hgood`, given by `exists_good_polynomial`). -/
def sliceMorphism (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S')
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hX : ProperInvariant S X.carrier)
    (hcov : ∀ t : Fin r → RVInfinity M, ∃ α : Fin 1 → Gamma M, NamedRadii S' t α ∧
      ∀ x y (hx : ((Fin.snoc b (x 0), t) : Mixed M (m + 1) r) ∈ X.carrier)
        (hy : ((Fin.snoc b (y 0), t) : Mixed M (m + 1) r) ∈ X.carrier),
        Congruent α x y → gammaMapValue ω ⟨_, hx⟩ = gammaMapValue ω ⟨_, hy⟩)
    (hfin : ∀ x : Fin (m + 1) → VF M, {u | (x, u) ∈ X.carrier}.Finite)
    (ω' : Map X' (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hX' : ProperInvariant S X'.carrier)
    (hcov' : ∀ t : Fin s → RVInfinity M, ∃ α : Fin 1 → Gamma M, NamedRadii S' t α ∧
      ∀ x y (hx : ((Fin.snoc b (x 0), t) : Mixed M (m + 1) s) ∈ X'.carrier)
        (hy : ((Fin.snoc b (y 0), t) : Mixed M (m + 1) s) ∈ X'.carrier),
        Congruent α x y → gammaMapValue ω' ⟨_, hx⟩ = gammaMapValue ω' ⟨_, hy⟩)
    (hfin' : ∀ x : Fin (m + 1) → VF M, {u | (x, u) ∈ X'.carrier}.Finite)
    (f : Map X X') (hf : ProperCovariantHomeomorphism (G := G) f)
    (hfix : ∀ p : X, Fin.init (f p).val.1 = Fin.init p.val.1)
    (Bad : DefSet (rawMixedSpace (M := M) (m + 1) r) S) (hBadX : Bad.carrier ⊆ X.carrier)
    (hmeasure : ∀ p : X, p.val ∉ Bad.carrier → ∃ L, HasMixedVFDerivativeAt f p L ∧
      vfValue (LinearMap.toMatrix' L).det = (gammaMapValue ω p / gammaMapValue ω' (f p)).val)
    (hgood : vfDim (rawRVSpace (M := M) 1) (sliceSet Bad b hS) < 1 ∨
      (sliceSet Bad b hS).carrier = ∅) :
    Morphism G (sliceObject X ω hX b hS hcov hfin) (sliceObject X' ω' hX' b hS hcov' hfin') where
  map := sliceMap f hfix
  bijective := sliceMap_bijective hfix hf.bijective
  chain := ObjectFactorization.step ⟨sliceMap_homeomorphism hfix hf,
    Or.inr ⟨0, fun _ k hk => absurd (Subsingleton.elim k 0) hk⟩,
    ⟨sliceSet Bad b hS, sliceSet_mono hBadX, hgood, fun q hq => sliceMap_measure ω ω' f hfix Bad hmeasure q hq⟩⟩
  bad := sliceSet Bad b hS
  bad_subset := sliceSet_mono hBadX
  bad_small := hgood
  measure q hq := sliceMap_measure ω ω' f hfix Bad hmeasure q hq

end Objects

end DiamondIntegral.Section7.FibreRestriction
