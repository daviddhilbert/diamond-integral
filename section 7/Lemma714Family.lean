import «section 7».Lemma714PromoteMoves

/-! Lemma 7.14, part 8: the chart schema of a family of RV fibres.

For a `T`-definable mixed set `A ⊆ VFᵐ × RVʳ` with a Γ-form `ω` and head-start
labels `π : Fin k → Fin r`, `famSchema` is the chart schema over `BT T` with
VF parameters whose row at `a` is the fibre `A_a`:

* structural map `u ↦ u ∘ π`;
* volume `u ↦ ω(a, u)`.

This is the chart of `fibreObject T A ω a π` (Section 7, `FibreObjects`). The
family is valid at every point with a doubly bounded fibre, for a fibre bound
chosen by saturation (`famSchema_valid`). The fibre object over `S⟨a⟩` is
identified with the extended row by the identity map (`fibre_iso_famRow`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {m r k : ℕ}

/-- VF parameter sorts. -/
abbrev vfs (m : ℕ) : Fin m → SortTag := fun _ => .vf

/-- The raw domain of the family. -/
def famDomain (A : DefSet (rawMixedSpace (M := M) m r) S) : Set (Fin (m + r) → M) := mixedTuple '' A.carrier

theorem mixedTuple_sorted (x : Mixed M m r) : ∀ i, sortEval (Fin.append (vfs m) (rvs r) i) (mixedTuple x i) := by
  intro i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [mixedTuple, Fin.append_left]
    exact (x.1 l).property
  · simp only [mixedTuple, Fin.append_right]
    exact (x.2 l).property

include hc in
theorem famDomain_definable (A : DefSet (rawMixedSpace (M := M) m r) S) :
    DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (Fin.append (vfs m) (rvs r)) (famDomain A) :=
  real_base hc ((mixedTuple_image_definable_iff _).mpr A.definable) (by
    rintro _ ⟨x, -, rfl⟩
    exact mixedTuple_sorted x)

/-- The index map `(z, u) ↦ (z, u, u ∘ π)`. -/
def famCoordIdx (m r k : ℕ) (π : Fin k → Fin r) : Fin ((m + r) + k) → Fin (m + r) :=
  Fin.append id (fun i => Fin.natAdd m (π i))

/-- The raw graph of the structural map `u ↦ u ∘ π` of the family. -/
def famCoord (A : DefSet (rawMixedSpace (M := M) m r) S) (π : Fin k → Fin r) : Set (Fin ((m + r) + k) → M) :=
  (fun x => x ∘ famCoordIdx m r k π) '' famDomain A

include hc in
theorem famCoord_definable (A : DefSet (rawMixedSpace (M := M) m r) S) (π : Fin k → Fin r) :
    DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (Fin.append (Fin.append (vfs m) (rvs r)) (rvs k)) (famCoord A π) := by
  have h := (famDomain_definable hc A).image_real (famCoordIdx m r k π)
  have e : Fin.append (vfs m) (rvs r) ∘ famCoordIdx m r k π = Fin.append (Fin.append (vfs m) (rvs r)) (rvs k) := by
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [famCoordIdx]
  rw [e] at h
  exact h

/-- The index map from the append layout to the layout of `mixedGammaGraph`. -/
def famVolIdx (m r : ℕ) : Fin (m + r) ⊕ Fin 1 → Fin ((m + r) + 1) :=
  Sum.elim (Fin.castAdd 1) (fun _ => Fin.natAdd (m + r) 0)

/-- The raw graph of the volume of the family. -/
def famVol (A : DefSet (rawMixedSpace (M := M) m r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) : Set (Fin ((m + r) + 1) → M) :=
  (fun w => w ∘ famVolIdx m r) ⁻¹' mixedGammaGraph A.carrier (gammaFormExtension ω)

include hc in
theorem famVol_definable (A : DefSet (rawMixedSpace (M := M) m r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (Fin.append (Fin.append (vfs m) (rvs r)) (rvs 1)) (famVol A ω) := by
  refine real_base hc ((gammaFormExtension_graph_definable ω).preimage_comp (famVolIdx m r)) ?_
  rintro w ⟨hnz, x, -, hx, -⟩ i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · have := mixedTuple_sorted x l
    rw [hx] at this
    simpa [famVolIdx] using this
  · fin_cases l
    rw [Fin.append_right]
    exact hnz.1

/-- **The chart schema of the family of fibres** `a ↦ (A_a, u ↦ u ∘ π, ω(a, ·))`. -/
def famSchema (A : DefSet (rawMixedSpace (M := M) m r) S) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (π : Fin k → Fin r) (N : ℕ) : ChartSchema (⟨S, ∅⟩ : Base (M := M)) (vfs m) k where
  arity := r
  domain := famDomain A
  domain_definable := famDomain_definable hc A
  coord := famCoord A π
  coord_definable := famCoord_definable hc A π
  volume := famVol A ω
  volume_definable := famVol_definable hc A ω
  bound := N

/-! ### Rows of the family -/

section Rows
variable (A : DefSet (rawMixedSpace (M := M) m r) S) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
  (π : Fin k → Fin r) (N : ℕ)

theorem append_eq_mixedTuple_iff (x : Mixed M m r) (a : Fin m → VF M) (u : Fin r → M) :
    mixedTuple x = Fin.append (vfValues a) u ↔ x.1 = a ∧ rvValues x.2 = u := by
  constructor
  · intro he
    refine ⟨vfValues_injective (funext fun i => ?_), funext fun i => ?_⟩
    · simpa [mixedTuple] using congrFun he (Fin.castAdd r i)
    · simpa [mixedTuple] using congrFun he (Fin.natAdd m i)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mem_famDomain_append (a : Fin m → VF M) (u : Fin r → M) :
    Fin.append (vfValues a) u ∈ famDomain A ↔ ∃ t, (a, t) ∈ A.carrier ∧ rvValues t = u := by
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨h1, h2⟩ := (append_eq_mixedTuple_iff x a u).mp he
    refine ⟨x.2, ?_, h2⟩
    rw [← h1]
    exact hx
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(a, t), ht, rfl⟩

theorem famSchema_mem_row (a : Fin m → VF M) (u : Fin r → M) :
    u ∈ (famSchema hc A ω π N).row (vfValues a) ↔ ∃ t, (a, t) ∈ A.carrier ∧ rvValues t = u :=
  mem_famDomain_append A a u

theorem famSchema_coordRow (a : Fin m → VF M) (u : Fin r → M) (y : Fin k → M) :
    (famSchema hc A ω π N).coordRow (vfValues a) u y ↔
      u ∈ (famSchema hc A ω π N).row (vfValues a) ∧ y = fun i => u (π i) := by
  change Fin.append (Fin.append (vfValues a) u) y ∈ famCoord A π ↔ Fin.append (vfValues a) u ∈ famDomain A ∧ _
  constructor
  · rintro ⟨x, hx, he⟩
    have h1 : x = Fin.append (vfValues a) u := by
      funext i
      have := congrFun he (Fin.castAdd k i)
      simpa [famCoordIdx] using this
    subst h1
    refine ⟨hx, funext fun i => ?_⟩
    have := congrFun he (Fin.natAdd (m + r) i)
    simp [famCoordIdx] at this
    exact this.symm
  · rintro ⟨hx, rfl⟩
    refine ⟨_, hx, funext fun i => ?_⟩
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [famCoordIdx]

theorem famSchema_volRow (a : Fin m → VF M) (t : Fin r → RVInfinity M) (ht : (a, t) ∈ A.carrier) (c : M) :
    (famSchema hc A ω π N).volRow (vfValues a) (rvValues t) c ↔
      NonzeroRV c ∧ codeValue c = (ω ⟨(a, t), ht⟩).val := by
  change Fin.append (Fin.append (vfValues a) (rvValues t)) (fun _ : Fin 1 => c) ∘ famVolIdx m r ∈
    mixedGammaGraph A.carrier (gammaFormExtension ω) ↔ _
  have h0 : (Fin.append (Fin.append (vfValues a) (rvValues t)) (fun _ : Fin 1 => c) ∘ famVolIdx m r) (.inr 0) = c := by
    simp [famVolIdx]
  have h1 : (Fin.append (Fin.append (vfValues a) (rvValues t)) (fun _ : Fin 1 => c) ∘ famVolIdx m r) ∘ Sum.inl =
      Fin.append (vfValues a) (rvValues t) := by
    funext i; simp [famVolIdx]
  unfold mixedGammaGraph
  simp only [Set.mem_setOf_eq, h0, h1]
  constructor
  · rintro ⟨hc0, x, hx, he, hv⟩
    obtain ⟨rfl, h2⟩ := (append_eq_mixedTuple_iff x a _).mp he
    have hx2 : x.2 = t := rvValues_injective h2
    have hxe : x = (x.1, t) := Prod.ext rfl hx2
    refine ⟨hc0, ?_⟩
    rw [hv]
    exact (congrArg (gammaFormExtension ω) hxe).trans (gammaFormExtension_at ω ⟨(x.1, t), ht⟩)
  · rintro ⟨hc0, hv⟩
    refine ⟨hc0, (a, t), ht, rfl, ?_⟩
    rw [hv, gammaFormExtension_at ω ⟨(a, t), ht⟩]

end Rows

/-! ### The fibre objects -/

section Fibres
variable {T : LRV.Substructure M} (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
  (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (π : Fin k → Fin r) (a : Fin m → VF M)
  (hFin : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
  (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero)

theorem fibre_mem_domain (t : Fin r → RVInfinity M) :
    t ∈ (fibreObject T A ω a π hFin hNZ).object.domain.carrier ↔ (a, t) ∈ A.carrier :=
  mem_fibreDomain A a t

theorem fibre_rawDom :
    rawDom (fibreObject T A ω a π hFin hNZ) = {u | ∃ t, (a, t) ∈ A.carrier ∧ rvValues t = u} := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, (fibre_mem_domain A ω π a hFin hNZ t).mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, (fibre_mem_domain A ω π a hFin hNZ t).mpr ht, rfl⟩

theorem fibre_rawCoord (t : Fin r → RVInfinity M) (ht : (a, t) ∈ A.carrier) :
    rawCoord (fibreObject T A ω a π hFin hNZ) (rvValues t) = fun i => rvValues t (π i) := by
  have h := rawCoord_of (fibreObject T A ω a π hFin hNZ) ⟨t, (fibre_mem_domain A ω π a hFin hNZ t).mpr ht⟩
  rw [h]
  rfl

theorem fibre_rawVol (t : Fin r → RVInfinity M) (ht : (a, t) ∈ A.carrier) :
    rawVol (fibreObject T A ω a π hFin hNZ) (rvValues t) = (ω ⟨(a, t), ht⟩).val := by
  have h := rawVol_of (fibreObject T A ω a π hFin hNZ) ⟨t, (fibre_mem_domain A ω π a hFin hNZ t).mpr ht⟩
  rw [h]
  exact fibreForm_apply A ω a t ht

end Fibres

/-! ### Validity of the family -/

section Valid
variable {T : LRV.Substructure M} (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
  (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (π : Fin k → Fin r) (N : ℕ)
  (a : Fin m → VF M)

theorem famSchema_volRow_row {u : Fin r → M} {c : M} (h : (famSchema hc A ω π N).volRow (vfValues a) u c) :
    u ∈ (famSchema hc A ω π N).row (vfValues a) := by
  change Fin.append (Fin.append (vfValues a) u) (fun _ : Fin 1 => c) ∘ famVolIdx m r ∈
    mixedGammaGraph A.carrier (gammaFormExtension ω) at h
  obtain ⟨-, x, hx, he, -⟩ := h
  have h1 : (Fin.append (Fin.append (vfValues a) u) (fun _ : Fin 1 => c) ∘ famVolIdx m r) ∘ Sum.inl =
      Fin.append (vfValues a) u := by
    funext i; simp [famVolIdx]
  rw [h1] at he
  exact ⟨x, hx, he⟩

theorem famSchema_valid (hFin : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero)
    (hN : ∀ y : Fin k → M, (∀ j, sortEval SortTag.rv (y j)) →
      {u | (famSchema hc A ω π N).coordRow (vfValues a) u y}.ncard ≤ N)
    (hU : (fibreObject T A ω a π hFin hNZ).doublyBounded) :
    (famSchema hc A ω π N).Valid (vfValues a) := by
  let W := famSchema hc A ω π N
  refine ⟨⟨fun i => (a i).property, fun u hu => ?_, fun u y h => ?_, fun y hy => ?_⟩, fun u y h => ?_,
    fun u hu => ?_, fun u c h => ⟨famSchema_volRow_row hc A ω π N a h, ?_⟩, fun u c c' h _ hc' => ?_, ?_⟩
  · exact ⟨fun i => u (π i), (famSchema_coordRow hc A ω π N a u _).mpr ⟨hu, rfl⟩,
      fun y h => ((famSchema_coordRow hc A ω π N a u y).mp h).2⟩
  · exact ((famSchema_coordRow hc A ω π N a u y).mp h).1
  · refine ⟨?_, hN y hy⟩
    let t' : Fin k → RVInfinity M := fun j => ⟨y j, hy j⟩
    apply ((hFin t').image rvValues).subset
    intro u hu
    obtain ⟨hu', rfl⟩ := (famSchema_coordRow hc A ω π N a u y).mp hu
    obtain ⟨t, ht, rfl⟩ := (famSchema_mem_row hc A ω π N a u).mp hu'
    exact ⟨t, ⟨ht, funext fun j => Subtype.ext rfl⟩, rfl⟩
  · obtain ⟨hu, rfl⟩ := (famSchema_coordRow hc A ω π N a u y).mp h
    obtain ⟨t, ht, rfl⟩ := (famSchema_mem_row hc A ω π N a u).mp hu
    intro i
    exact ⟨(t (π i)).property, hNZ _ ht i⟩
  · obtain ⟨t, ht, rfl⟩ := (famSchema_mem_row hc A ω π N a u).mp hu
    exact ⟨_, (famSchema_volRow hc A ω π N a t ht _).mpr ⟨ChartSchema.nonzero_raw _,
      ChartSchema.codeValue_raw_representative _⟩⟩
  · obtain ⟨t, ht, rfl⟩ := (famSchema_mem_row hc A ω π N a u).mp (famSchema_volRow_row hc A ω π N a h)
    exact ((famSchema_volRow hc A ω π N a t ht c).mp h).1
  · obtain ⟨t, ht, rfl⟩ := (famSchema_mem_row hc A ω π N a u).mp (famSchema_volRow_row hc A ω π N a h)
    have h1 := ((famSchema_volRow hc A ω π N a t ht c).mp h).2
    rw [famSchema_volRow hc A ω π N a t ht c', h1]
    exact ⟨fun h2 => h2.2, fun h2 => ⟨hc', h2⟩⟩
  · obtain ⟨β, hβ⟩ := chartOf_bounded hc (fibreObject T A ω a π hFin hNZ) hU
    refine ⟨β⁻¹, β, fun u hu i hi => hβ u ?_ i hi⟩
    have h := (famSchema_mem_row hc A ω π N a u).mp hu
    have e := fibre_rawDom A ω π a hFin hNZ
    show u ∈ rawDom (fibreObject T A ω a π hFin hNZ)
    rw [e]
    exact h

end Valid

/-! ### The fibre object is the extended row -/

section FibreIso
variable {T : LRV.Substructure M} (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
  (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (π : Fin k → Fin r) (N : ℕ)
  (a : Fin m → VF M)
  (hFin : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
  (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero)

theorem baseAt_adjoin_real :
    (baseAt (⟨(T : Set M), ∅⟩ : Base (M := M)) (vfValues a)).real ⊆ (KernelBaseChange.adjoin T a : Set M) := by
  rintro x (hx | ⟨i, rfl⟩)
  · exact KernelBaseChange.subset_adjoin a hx
  · exact KernelBaseChange.coordinate_mem_adjoin a i

theorem baseAt_adjoin_gamma :
    (baseAt (⟨(T : Set M), ∅⟩ : Base (M := M)) (vfValues a)).gamma ⊆ (∅ : Set (Values.Gamma (M := M))) :=
  subset_refl _

theorem fibre_domain_eq :
    (famSchema hc A ω π N).row (vfValues a) = rawDom (fibreObject T A ω a π hFin hNZ) := by
  rw [fibre_rawDom]
  ext u
  exact famSchema_mem_row hc A ω π N a u

theorem fibre_weight_eq (hF : (famSchema hc A ω π N).Valid (vfValues a)) (t : Fin r → RVInfinity M)
    (ht : (a, t) ∈ A.carrier) :
    rawVol (fibreObject T A ω a π hFin hNZ) (rvValues t) *
        ∏ i, codeValue (rawCoord (fibreObject T A ω a π hFin hNZ) (rvValues t) i) =
      (famSchema hc A ω π N).weightAt (vfValues a) (rvValues t) := by
  have hrow : rvValues t ∈ (famSchema hc A ω π N).row (vfValues a) :=
    (famSchema_mem_row hc A ω π N a _).mpr ⟨t, ht, rfl⟩
  have hco : (famSchema hc A ω π N).coordAt (vfValues a) (rvValues t) = fun i => rvValues t (π i) :=
    ((famSchema_coordRow hc A ω π N a _ _).mp (ChartSchema.coordRow_coordAt hF hrow)).2
  obtain ⟨c, hcv⟩ := hF.vol_total _ hrow
  have hv1 := ((ChartSchema.volRow_iff hF _ c).mp hcv).2.2
  have hv2 := ((famSchema_volRow hc A ω π N a t ht c).mp hcv).2
  unfold ChartSchema.weightAt
  rw [fibre_rawVol A ω π a hFin hNZ t ht, fibre_rawCoord A ω π a hFin hNZ t ht, hco, ← hv1, hv2]

/-- The chart of the fibre object over `S⟨a⟩` is the extended row of the family,
by the identity map. -/
def fibreIso (hF : (famSchema hc A ω π N).Valid (vfValues a)) :
    Iso (chartOf hc (fibreObject T A ω a π hFin hNZ))
      (extChart (C := ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩) (baseAt_adjoin_real a) (baseAt_adjoin_gamma a)
        (famSchema hc A ω π N) hF) :=
  isoOfMap (chartOf hc (fibreObject T A ω a π hFin hNZ))
    (extChart (C := ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩) (baseAt_adjoin_real a) (baseAt_adjoin_gamma a)
      (famSchema hc A ω π N) hF) (fun u => u)
    (RVCoordinateMaps.coordinate_graph_definable _ _ (chartOf hc (fibreObject T A ω a π hFin hNZ)).domain_definable
      (id : Fin r → Fin r))
    (by
      have he := fibre_domain_eq hc A ω π N a hFin hNZ
      change Set.BijOn (fun u => u) (rawDom (fibreObject T A ω a π hFin hNZ)) ((famSchema hc A ω π N).row (vfValues a))
      rw [he]
      exact Set.bijOn_id _)
    (by
      intro u hu
      have hu' : u ∈ rawDom (fibreObject T A ω a π hFin hNZ) := hu
      rw [fibre_rawDom] at hu'
      obtain ⟨t, ht, he⟩ := hu'
      subst he
      exact fibre_weight_eq hc A ω π N a hFin hNZ hF t ht)

theorem cls_fibre_eq (hF : (famSchema hc A ω π N).Valid (vfValues a))
    (hU : (fibreObject T A ω a π hFin hNZ).doublyBounded) :
    cls (objOf hc (KernelBaseChange.adjoin T a) (fibreObject T A ω a π hFin hNZ) hU) =
      cls (extObj (C := ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩) (baseAt_adjoin_real a) (baseAt_adjoin_gamma a)
        (famSchema hc A ω π N) hF) :=
  cls_eq_of_iso (fibreIso hc A ω π N a hFin hNZ hF)

end FibreIso

/-! ### A uniform fibre bound for the family -/

section Bound
variable {T : LRV.Substructure M} (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
  (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (π : Fin k → Fin r)

include hc ω in
theorem famCoord_rows_finite
    (hFin : ∀ (a : Fin m → VF M) (t : Fin k → RVInfinity M), {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (a : Fin m → VF M) (y : Fin k → M) (hy : ∀ j, sortEval SortTag.rv (y j)) :
    {u : Fin r → M | Fin.append (Fin.append (vfValues a) u) y ∈ famCoord A π}.Finite := by
  let t' : Fin k → RVInfinity M := fun j => ⟨y j, hy j⟩
  apply ((hFin a t').image rvValues).subset
  intro u hu
  obtain ⟨hu', rfl⟩ := (famSchema_coordRow hc A ω π 0 a u y).mp hu
  obtain ⟨t, ht, rfl⟩ := (famSchema_mem_row hc A ω π 0 a u).mp hu'
  exact ⟨t, ⟨ht, funext fun j => Subtype.ext rfl⟩, rfl⟩

include hc ω in
theorem exists_fam_bound {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk (T : Set M) < κ)
    (hFin : ∀ (a : Fin m → VF M) (t : Fin k → RVInfinity M), {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    ∃ N : ℕ, ∀ (a : Fin m → VF M) (y : Fin k → M), (∀ j, sortEval SortTag.rv (y j)) →
      {u : Fin r → M | Fin.append (Fin.append (vfValues a) u) y ∈ famCoord A π}.ncard ≤ N := by
  let sa := Fin.append (vfs m) (rvs k)
  let R : Set ((Fin (m + k) → M) × (Fin r → M)) :=
    {q | Fin.append q.1 q.2 ∘ swapLastBlockCoordinates m k r ∈ famCoord A π ∧
      Fin.append q.1 q.2 ∈ sortedUniverse (Fin.append sa (rvs r))}
  have hR : DefinableOverBase (⟨(T : Set M), ∅⟩ : Base (M := M)) (Fin.append sa (rvs r))
      {v | ((fun i => v (Fin.castAdd r i)), fun j => v (Fin.natAdd (m + k) j)) ∈ R} := by
    convert (famCoord_definable hc A π).preimage_real (Fin.append sa (rvs r)) (swapLastBlockCoordinates m k r) using 1
    ext v
    simp only [R, Set.mem_setOf_eq, Fin.append_castAdd_natAdd]
  have hgamma : Cardinal.mk ((⟨(T : Set M), ∅⟩ : Base (M := M)).gamma) < κ := by
    rw [Cardinal.mk_eq_zero]
    exact lt_of_lt_of_le Cardinal.aleph0_pos hκ
  obtain ⟨N, hN⟩ := gamma_uniform_finite_tuple_rows hκ hs hsmall hgamma sa (rvs r) (sortedUniverse sa)
    (real_definableOverBase _ sa _ (sortedUniverse_definable _ sa)) R hR (by
      intro w hw
      let a : Fin m → VF M := fun i => ⟨w (Fin.castAdd k i), by
        have := hw (Fin.castAdd k i)
        rw [show sa (Fin.castAdd k i) = SortTag.vf from Fin.append_left _ _ i] at this
        exact this⟩
      have hy : ∀ j, sortEval SortTag.rv (w (Fin.natAdd m j)) := fun j => by
        have := hw (Fin.natAdd m j)
        rw [show sa (Fin.natAdd m j) = SortTag.rv from Fin.append_right _ _ j] at this
        exact this
      apply (famCoord_rows_finite hc A ω π hFin a _ hy).subset
      intro u hu
      have h1 := hu.1
      have he : Fin.append w u = Fin.append (Fin.append (vfValues a) (fun j => w (Fin.natAdd m j))) u := by
        congr 1
        funext i
        refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [a, vfValues]
      rw [he, append_swapLastBlocks] at h1
      exact h1)
  refine ⟨N, fun a y hy => ?_⟩
  have hw : Fin.append (vfValues a) y ∈ sortedUniverse sa := sorted_append (fun i => (a i).property) hy
  have h := (hN _ hw).2
  convert h using 2
  ext u
  simp only [R, Set.mem_setOf_eq, append_swapLastBlocks]
  constructor
  · intro hu
    refine ⟨hu, sorted_append hw (fun j => ?_)⟩
    have := (famCoord_definable hc A π).proper _ hu (Fin.castAdd k (Fin.natAdd m j))
    rw [Fin.append_left, Fin.append_right, Fin.append_left, Fin.append_right] at this
    exact this
  · exact fun h => h.1

end Bound

end DiamondIntegral.Section7.Lemma714Schema
