import «section 7».Lemma714OneVar
import «section 7».Corollary715Fibres

/-! Lemma 7.14, part 35: label translations.

A bijection `f : X → Y` of mixed sets that keeps the RV labels and translates
the VF coordinates by an amount determined by the labels is a proper covariant
homeomorphism when `X` and `Y` are proper invariant (`transl_homeo`), and it has
unit derivative everywhere (`transl_unit`). Such maps arise when the
first-stage sets of the reduction are pulled back along the zero-centred
normalization (GAP-REPAIRS 11). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The translation amount of `f` at `p`. -/
def trAt {S : Set M} {m q q' : ℕ} {X : DefSet (rawMixedSpace (M := M) m q) S}
    {Y : DefSet (rawMixedSpace (M := M) m q') S} (f : Map X Y) (p : X) : Fin m → VF M :=
  fun i => (f p).val.1 i - p.val.1 i

section Transl
variable {S : Set M} {m q : ℕ} {X Y : DefSet (rawMixedSpace (M := M) m q) S} (f : Map X Y)
  (hlab : ∀ p : X, (f p).val.2 = p.val.2)
  (htr : ∀ p p' : X, p.val.2 = p'.val.2 → trAt f p = trAt f p')

include hlab htr in
/-- On a label fibre, the map is a translation. -/
theorem transl_value (p : X) (a : Fin m → VF M) (ha : (a, p.val.2) ∈ X.carrier) :
    (f ⟨(a, p.val.2), ha⟩).val = (a + trAt f p, (f p).val.2) := by
  have h := htr ⟨(a, p.val.2), ha⟩ p rfl
  refine Prod.ext ?_ ?_
  · change (f ⟨(a, p.val.2), ha⟩).val.1 = a + trAt f p
    rw [← h]
    funext i
    change (f ⟨(a, p.val.2), ha⟩).val.1 i = a i + ((f ⟨(a, p.val.2), ha⟩).val.1 i - a i)
    abel
  · rw [hlab, hlab]

include hlab htr in
theorem transl_graphFibre (u v : Fin q → RVInfinity M) (a b : Fin m → VF M) :
    graphFibre f u v a b ↔ ∃ ha : (a, u) ∈ X.carrier, u = v ∧ b = (f ⟨(a, u), ha⟩).val.1 := by
  constructor
  · rintro ⟨p, hp, hfp⟩
    have ha : (a, u) ∈ X.carrier := by
      rw [← hp]
      exact p.property
    have hpe : p = ⟨(a, u), ha⟩ := Subtype.ext hp
    subst hpe
    refine ⟨ha, ?_, (congrArg Prod.fst hfp).symm⟩
    have := congrArg Prod.snd hfp
    rw [hlab] at this
    exact this
  · rintro ⟨ha, rfl, rfl⟩
    exact ⟨⟨(a, u), ha⟩, rfl, Prod.ext rfl (hlab _)⟩

include hlab htr in
theorem transl_source (u v : Fin q → RVInfinity M) :
    graphFibreSource f u v = if u = v then vfFibre X.carrier u else ∅ := by
  ext a
  simp only [graphFibreSource, Set.mem_setOf_eq, transl_graphFibre f hlab htr]
  split_ifs with h
  · subst h
    exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨_, ha, rfl, rfl⟩⟩
  · exact ⟨fun ⟨_, _, he, _⟩ => (h he).elim, fun ha => (Set.notMem_empty a ha).elim⟩

include hlab htr in
theorem transl_range (hf : Function.Bijective f) (u v : Fin q → RVInfinity M) :
    graphFibreRange f u v = if u = v then vfFibre Y.carrier u else ∅ := by
  ext b
  simp only [graphFibreRange, Set.mem_setOf_eq, transl_graphFibre f hlab htr]
  split_ifs with h
  · subst h
    constructor
    · rintro ⟨a, ha, -, rfl⟩
      have := (f ⟨(a, u), ha⟩).property
      rw [show (f ⟨(a, u), ha⟩).val = ((f ⟨(a, u), ha⟩).val.1, u) from Prod.ext rfl (hlab _)] at this
      exact this
    · intro hb
      obtain ⟨p, hp⟩ := hf.2 ⟨(b, u), hb⟩
      have hpu : p.val.2 = u := by
        rw [← hlab p, hp]
      have ha : (p.val.1, u) ∈ X.carrier := by
        rw [← hpu]
        exact p.property
      refine ⟨p.val.1, ha, rfl, ?_⟩
      have hpe : (⟨(p.val.1, u), ha⟩ : X) = p := Subtype.ext (Prod.ext rfl hpu.symm)
      rw [hpe, hp]
  · exact ⟨fun ⟨_, _, he, _⟩ => (h he).elim, fun hb => (Set.notMem_empty b hb).elim⟩

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
  (hX : ProperInvariant S X.carrier) (hY : ProperInvariant S Y.carrier)

include hlab htr in
theorem transl_continuous : ContinuousOnGraphFibres (G := G) f := by
  intro u v
  by_cases huv : u = v
  · subst huv
    by_cases hne : ∃ a, (a, u) ∈ X.carrier
    · obtain ⟨a₀, h₀⟩ := hne
      let p₀ : X := ⟨(a₀, u), h₀⟩
      have hcont : Continuous (fun a : Fin m → VF M => a + trAt f p₀) :=
        continuous_id.add continuous_const
      refine hcont.continuousOn.congr fun a ha => ?_
      have hg := graphFibreMap_graph f u u ha
      obtain ⟨ha', -, hb⟩ := (transl_graphFibre f hlab htr u u a _).mp hg
      rw [hb]
      have := transl_value f hlab htr p₀ a ha'
      exact congrArg Prod.fst this
    · have he : graphFibreSource f u u = ∅ := by
        rw [transl_source f hlab htr, if_pos rfl]
        exact Set.eq_empty_of_forall_notMem fun a ha => hne ⟨a, ha⟩
      rw [he]
      exact continuousOn_empty _
  · have he : graphFibreSource f u v = ∅ := by
      rw [transl_source f hlab htr, if_neg huv]
    rw [he]
    exact continuousOn_empty _

include hlab htr h00 hc hκ hs hv hsmall hΓ hX hY in
/-- **A label translation is a proper covariant homeomorphism.** -/
theorem transl_homeo (hf : Function.Bijective f) : ProperCovariantHomeomorphism (G := G) f := by
  have hcont := transl_continuous (G := G) f hlab htr
  have hcov : ProperCovariant f := by
    refine properCovariant_of_clopen_ranges h00 hc hκ hs hv f hX hY hcont (fun u v => ?_) (fun u v => ?_)
    · rw [transl_source f hlab htr]
      split_ifs
      · exact (hX.clopen_fibres hv u).isOpen
      · exact isOpen_empty
    · rw [transl_range f hlab htr hf]
      split_ifs
      · exact hY.clopen_fibres hv u
      · exact isClopen_empty
  exact properHomeomorphism_of_properCovariant h00 hc lin hκ hs hv hsmall hΓ _ hcov hf hcont

include hlab htr hv hX in
/-- **A label translation has unit derivative everywhere.** -/
theorem transl_unit (p : X) : HasMixedUnitDerivativeAt f p := by
  obtain ⟨σ, hσ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((hX.clopen_fibres hv p.val.2).isOpen.mem_nhds p.property)
  refine ⟨LinearMap.id, ⟨fun x => LinearMap.id x + trAt f p, ⟨σ, fun x hx => ?_⟩,
    hasVFDerivativeAt_affine _ _ _⟩, by rw [LinearMap.toMatrix'_id, Matrix.det_one]⟩
  have hxX : (x, p.val.2) ∈ X.carrier := hσ hx
  exact ⟨hxX, transl_value f hlab htr p x hxX⟩

end Transl

end DiamondIntegral.Section7.Lemma714Reduce
