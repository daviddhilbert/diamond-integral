import «section 8».IsoLattice

/-! `h_m` is invariant under isomorphisms of bounded charts.

An isomorphism `F : a ≅ b` preserves weights and, by `iso_lattice` (applied to `F` and its inverse),
the lattice parts. So it restricts to a definable bijection between the lattice parts of a given
weight (`fibre_bijOn`), the two RES charts have the same class, and `hmValue a = hmValue b`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal DiamondIntegral.Section8.PuiseuxValues

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)

/-- The total extension of an isomorphism. -/
abbrev isoMap {k : ℕ} {a b : Chart (base P) k} (F : Iso a b) : (Fin a.arity → P.N) → (Fin b.arity → P.N) :=
  RVUnderlyingIsomorphisms.Iso.extension (RVMeasuredIsomorphisms.underlying F)

theorem isoMap_on {k : ℕ} {a b : Chart (base P) k} (F : Iso a b) (u : a.domain) :
    isoMap P F u.val = (F.equiv u).val :=
  RVUnderlyingIsomorphisms.Iso.extension_on (RVMeasuredIsomorphisms.underlying F) u

/-- An isomorphism restricts to a bijection between the lattice parts of a given weight. -/
theorem fibre_bijOn {k : ℕ} {a b : Chart (base P) k} (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (F : Iso a b) (m : ℕ+) (w : Γ) :
    Set.BijOn (isoMap P F) (latticeFibre P a m w) (latticeFibre P b m w) := by
  refine ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ h => ?_, fun v hv => ?_⟩
  · have hu' : u ∈ a.domain := hu.1.1
    rw [show u = (⟨u, hu'⟩ : a.domain).val from rfl, isoMap_on]
    refine ⟨iso_lattice P ha hb F m ⟨u, hu'⟩ hu.1, ?_⟩
    rw [← F.weight_eq ⟨u, hu'⟩]
    exact hu.2
  · have h₁ : u₁ ∈ a.domain := hu₁.1.1
    have h₂ : u₂ ∈ a.domain := hu₂.1.1
    rw [show u₁ = (⟨u₁, h₁⟩ : a.domain).val from rfl, show u₂ = (⟨u₂, h₂⟩ : a.domain).val from rfl,
      isoMap_on, isoMap_on] at h
    exact congrArg Subtype.val (F.equiv.injective (Subtype.ext h))
  · have hv' : v ∈ b.domain := hv.1.1
    let u := F.equiv.symm ⟨v, hv'⟩
    have hlat : u.val ∈ latticeDomain P a m :=
      iso_lattice P hb ha (RVMeasuredIsomorphisms.symm F) m ⟨v, hv'⟩ hv.1
    refine ⟨u.val, ⟨hlat, ?_⟩, ?_⟩
    · rw [F.weight_eq u, F.equiv.apply_symm_apply]
      exact hv.2
    · rw [isoMap_on, F.equiv.apply_symm_apply]

theorem fibre_graph_definable {k : ℕ} {a b : Chart (base P) k} (ha : RVMeasuredBounds.DomainBounded a)
    (F : Iso a b) (m : ℕ+) (w : Γ) :
    DefinableOverBase (base P) (fun _ : Fin (b.arity + a.arity) => .rv)
      (graphOn (latticeFibre P a m w) (isoMap P F)) := by
  have h := DefinableOverBase.inter
    (RVUnderlyingIsomorphisms.Iso.extension_graph (RVMeasuredIsomorphisms.underlying F))
    ((latticeFibre_definable' P a ha m w).preimage_real (fun _ : Fin (b.arity + a.arity) => .rv)
      (headIndex b.arity a.arity))
  convert h using 1
  refine Set.ext fun z => ⟨fun ⟨h1, h2⟩ => ⟨⟨h1.1.1, h2⟩, h1, ?_⟩, fun ⟨⟨_, h2⟩, h3, _⟩ => ⟨h3, h2⟩⟩
  exact (RVUnderlyingIsomorphisms.Iso.extension_graph (RVMeasuredIsomorphisms.underlying F)).proper z
    ⟨h1.1.1, h2⟩

/-- The RES charts of an isomorphism's lattice parts of a given weight are isomorphic. -/
def fibreIso {k : ℕ} {a b : Chart (base P) k} (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (F : Iso a b) (m : ℕ+) (w : Γ) :
    RVUnderlyingIsomorphisms.Iso (fibreChart P a ha m w).toChart (fibreChart P b hb m w).toChart :=
  RVUnderlyingIsomorphisms.ofMap _ _ (isoMap P (a := a) (b := b) F) (fibre_graph_definable P ha F m w)
    (fibre_bijOn P ha hb F m w)

/-- **`h_m` is invariant under isomorphisms.** -/
theorem hmValue_iso {k : ℕ} {a b : Chart (base P) k} (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (F : Iso a b) (m : ℕ+) :
    hmValue P a ha m = hmValue P b hb m := by
  have hbij := fibre_bijOn P ha hb F m
  have hw : weights P a ha m = weights P b hb m := Finset.ext fun w => by
    rw [mem_weights, mem_weights]
    constructor
    · rintro ⟨u, hu⟩; exact ⟨_, (hbij w).mapsTo hu⟩
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu, -⟩ := (hbij w).surjOn hv
      exact ⟨u, hu⟩
  unfold hmValue
  rw [hw]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold hmTerm
  rw [nativeRESChartClass_iso _ _ (fibreIso P ha hb F m w)]

end DiamondIntegral.Section8.Hm
