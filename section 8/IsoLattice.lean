import «section 8».GaloisLattice
import «section 8».HmCharts

/-! Isomorphisms preserve the lattice part (the key step of Lemma 8.2).

Let `F : a ≅ b` be an isomorphism of bounded charts over the base of Section 8. If `u` lies in the
lattice part of `a` at level `m`, then `F u` lies in the lattice part of `b`.

The paper argues in `ℂ{{t}}`, where the points with values in `m⁻¹ℤ` are the points over
`ℂ((t^{1/m}))`, a functionally closed subfield. In the ambient model the residue field is larger,
and we argue as follows. The set of lattice points `u` of `a` with `F u` outside the lattice part
of `b` is definable over the base (`b` is bounded, so its lattice part is definable). If it were
nonempty, then by elementarity it would contain the image of a point `w₀ = (u₀, v₀)` of the
concrete model (`exists_concrete_point`). The automorphism of the concrete model given by
`levelRoots m` fixes the base, hence the concrete trace of the graph of `F`; it fixes `u₀`, whose
values lie in `m⁻¹ℤ`, and moves `v₀`, one of whose values does not. As the graph is functional,
this is impossible (`iso_lattice`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues
open DiamondIntegral.Section8.Galois
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

local instance isoSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance isoSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient)

local notation "π" => uniformizerValue P

/-! ### Transfer along the elementary embedding -/

/-- A set definable over the base of Section 8 is definable, in the raw structure, over the image
of the Laurent coefficients. -/
theorem raw_definable_of_base {n : ℕ} {A : Set (Fin n → P.N)}
    (hA : DefinableOverBase (base P) (fun _ : Fin n => .rv) A) :
    (Set.range (P.e ∘ laurentCoefficientEnumeration)).Definable LRV A := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  cases k with
  | succ k => exact absurd (hγ 0) (Set.notMem_empty _)
  | zero =>
    have hA' := (GammaParameters.with_zero_iff _ γ _ _).mp hA
    have hraw := ((definableOver_iff_normalized_raw _ _ _).mp hA').1
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical P.hc] at hraw
    have hB : (base P).real = Set.range (P.e ∘ laurentCoefficientEnumeration) := P.hB
    rw [hB] at hraw
    exact hraw

/-- The concrete trace of such a set is definable over the base of the concrete model. -/
theorem trace_definable {n : ℕ} {A : Set (Fin n → P.N)}
    (hA : DefinableOverBase (base P) (fun _ : Fin n => .rv) A) :
    {c | baseCarrier c}.Definable LRV {x : Fin n → Carrier | P.e ∘ x ∈ A} := by
  have h := (elementaryActualDefinableEquiv P.e laurentCoefficientEnumeration
    (⟨A, raw_definable_of_base P hA⟩ : LRV.DefinableSet _ (Fin n))).property
  have h' : (Set.range laurentCoefficientEnumeration).Definable LRV
      {x : Fin n → Carrier | P.e ∘ x ∈ A} := h
  rw [laurentCoefficientEnumeration_range] at h'
  exact h'

/-- **Transfer.** A nonempty set definable over the base contains the image of a concrete point. -/
theorem exists_concrete_point {n : ℕ} {A : Set (Fin n → P.N)}
    (hA : DefinableOverBase (base P) (fun _ : Fin n => .rv) A) (hne : A.Nonempty) :
    ∃ x : Fin n → Carrier, P.e ∘ x ∈ A := by
  by_contra hno
  push Not at hno
  let E := elementaryActualDefinableEquiv P.e laurentCoefficientEnumeration (n := n)
  let S : LRV.DefinableSet _ (Fin n) := ⟨A, raw_definable_of_base P hA⟩
  have h1 : E S = E ⊥ := by
    apply Subtype.ext
    change {x | P.e ∘ x ∈ A} = {x | P.e ∘ x ∈ ((⊥ : LRV.DefinableSet
      (Set.range (P.e ∘ laurentCoefficientEnumeration)) (Fin n)) : Set (Fin n → P.N))}
    rw [DefinableSet.coe_bot]
    exact Set.ext fun x => ⟨fun h => hno x h, fun h => h.elim⟩
  have h2 : S = ⊥ := E.injective h1
  obtain ⟨x, hx⟩ := hne
  have : x ∈ ((⊥ : LRV.DefinableSet (Set.range (P.e ∘ laurentCoefficientEnumeration)) (Fin n)) :
      Set (Fin n → P.N)) := by
    rw [← h2]; exact hx
  rw [DefinableSet.coe_bot] at this
  exact this

/-! ### RV points of the concrete model -/

theorem concrete_rv {x : Carrier} (hx : iRV (P.e x)) : x = Sum.inr (rvPart x) := by
  have h := P.e.map_rel Rel.memRV ![x]
  have ht : (P.e ∘ (![x] : Fin 1 → Carrier)) = ![P.e x] := by
    funext i; fin_cases i; rfl
  rw [ht] at h
  have hx' : iRV x := h.mp hx
  exact (rvSort_tag ⟨x, hx'⟩).symm

/-- `levelRoots m` fixes a concrete RV point whose image is a lattice point. -/
theorem fixed_of_lattice (m : ℕ+) {x : Carrier} (hx : iRV (P.e x))
    (hl : InLattice π m (codeValue (P.e x))) : carrierAction (levelRoots m) x = x := by
  rw [concrete_rv P hx, PuiseuxOriginal.carrierAction_inr]
  congr 1
  cases hr : rvPart x with
  | none => rfl
  | some u =>
    rw [concrete_rv P hx, hr] at hl
    exact (inLattice_iff_fixed P m u).mp hl

/-- `levelRoots m` moves a concrete RV point whose image is not a lattice point. -/
theorem moved_of_not_lattice (m : ℕ+) {x : Carrier} (hx : iRV (P.e x))
    (hl : ¬ InLattice π m (codeValue (P.e x))) : carrierAction (levelRoots m) x ≠ x := by
  rw [concrete_rv P hx, PuiseuxOriginal.carrierAction_inr]
  intro h
  apply hl
  rw [concrete_rv P hx]
  cases hr : rvPart x with
  | none =>
    rw [codeValue_rv_none]; exact inLattice_one _ _
  | some u =>
    rw [hr] at h
    exact (inLattice_iff_fixed P m u).mpr (Sum.inr_injective h)

/-! ### Isomorphisms preserve the lattice part -/

/-- The graph of an isomorphism of charts. -/
def isoGraph {k : ℕ} {a b : Chart (base P) k} (F : Iso a b) : Set (Fin (b.arity + a.arity) → P.N) :=
  {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F.equiv u).val}

theorem isoGraph_functional {k : ℕ} {a b : Chart (base P) k} (F : Iso a b)
    {w w' : Fin (b.arity + a.arity) → P.N} (hw : w ∈ isoGraph P F) (hw' : w' ∈ isoGraph P F)
    (h : w ∘ headIndex b.arity a.arity = w' ∘ headIndex b.arity a.arity) : w = w' := by
  obtain ⟨u, rfl⟩ := hw
  obtain ⟨u', rfl⟩ := hw'
  have hu : u = u' := by
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa only [Function.comp_apply, join_head] using this
  rw [hu]

/-- **Isomorphisms preserve the lattice part.** -/
theorem iso_lattice {k : ℕ} {a b : Chart (base P) k} (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (F : Iso a b) (m : ℕ+) (u : a.domain)
    (hu : u.val ∈ latticeDomain P a m) : (F.equiv u).val ∈ latticeDomain P b m := by
  by_contra hF
  let n := a.arity
  let n' := b.arity
  let Bad : Set (Fin (n' + n) → P.N) :=
    (isoGraph P F ∩ {w | w ∘ headIndex n' n ∈ latticeDomain P a m ∧
      w ∈ sortedUniverse (fun _ : Fin (n' + n) => SortTag.rv)}) ∩
    {w | w ∘ tailIndex n' n ∈ (sortedUniverse (fun _ : Fin n' => SortTag.rv) \ latticeDomain P b m) ∧
      w ∈ sortedUniverse (fun _ : Fin (n' + n) => SortTag.rv)}
  have hBad : DefinableOverBase (base P) (fun _ : Fin (n' + n) => .rv) Bad :=
    DefinableOverBase.inter (DefinableOverBase.inter F.graph_definable
      ((latticeDomain_definable P (bdd P a ha) m.ne_zero).preimage_real _ (headIndex n' n)))
      ((latticeDomain_definable P (bdd P b hb) m.ne_zero).compl.preimage_real _ (tailIndex n' n))
  have hw : join n' n u.val (F.equiv u).val ∈ Bad := by
    have hs : join n' n u.val (F.equiv u).val ∈ sortedUniverse (fun _ : Fin (n' + n) => SortTag.rv) :=
      F.graph_definable.proper _ ⟨u, rfl⟩
    have hh : join n' n u.val (F.equiv u).val ∘ headIndex n' n = u.val := funext fun i => join_head _ _ _ _ i
    have ht : join n' n u.val (F.equiv u).val ∘ tailIndex n' n = (F.equiv u).val :=
      funext fun i => join_tail _ _ _ _ i
    refine ⟨⟨⟨u, rfl⟩, ?_, hs⟩, ?_, hs⟩
    · rw [hh]; exact hu
    · rw [ht]
      exact ⟨fun j => b.domain_definable.proper _ (F.equiv u).property j, hF⟩
  obtain ⟨w₀, hw₀⟩ := exists_concrete_point P hBad ⟨_, hw⟩
  obtain ⟨⟨hgr, hhead, -⟩, ⟨htail, htailnot⟩, -⟩ := hw₀
  have hsorted : ∀ i, iRV (P.e (w₀ i)) := fun i =>
    F.graph_definable.proper _ hgr i
  let σ := carrierAction (levelRoots m)
  -- `σ` preserves the concrete trace of the graph.
  have hσgr : P.e ∘ (σ ∘ w₀) ∈ isoGraph P F := by
    have hD := trace_definable P F.graph_definable
    exact (raw_original_definable_invariant (levelRoots m) _ hD w₀).mpr hgr
  -- `σ` fixes the head of `w₀`.
  have hhead_fixed : (σ ∘ w₀) ∘ headIndex n' n = w₀ ∘ headIndex n' n := by
    funext i
    exact fixed_of_lattice P m (hsorted _) (hhead.2 i)
  -- Hence `σ` fixes `w₀`.
  have hfix : P.e ∘ (σ ∘ w₀) = P.e ∘ w₀ := by
    refine isoGraph_functional P F hσgr hgr ?_
    funext i
    exact congrArg P.e (congrFun hhead_fixed i)
  have hfix' : σ ∘ w₀ = w₀ := funext fun i => P.e.injective (congrFun hfix i)
  -- But `σ` moves a coordinate of the tail.
  have hnot : ¬ ∀ j, InLattice π m (codeValue (P.e (w₀ (tailIndex n' n j)))) := fun hall =>
    htailnot ⟨by
      obtain ⟨v, hv⟩ := hgr
      have : (P.e ∘ w₀) ∘ tailIndex n' n = (F.equiv v).val := by
        rw [hv]; exact funext fun i => join_tail _ _ _ _ i
      rw [this]; exact (F.equiv v).property, hall⟩
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  exact moved_of_not_lattice P m (hsorted _) hj (congrFun hfix' (tailIndex n' n j))

end DiamondIntegral.Section8.Hm
