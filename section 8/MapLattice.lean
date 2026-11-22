import «section 8».IsoLattice

/-! Definable maps preserve the lattice.

Let `F` be a map on a definable set `A ⊆ RVⁿ` whose graph is definable over the base of Section 8.
If every coordinate of `u ∈ A` has value in `π^{m⁻¹ℤ}`, so does every coordinate of `F u`
(`map_lattice`). This is the functional closure of `ℂ((t^{1/m}))` used in the proofs of Lemmas 8.2
and 8.3 of the paper, here in the ambient model.

Proof. Let `γ` be the value tuple of `u` and `H` the points of `A` with values `γ`. By
residue–value-group orthogonality the `j`-th coordinate of `F` takes finitely many values on `H`
(`values_finite_of_volume`), so the value `δ` of `F u j` is definable. The points of the graph over
`H` whose `j`-th output has value `δ` form a definable set; if `δ` were not a lattice point, the
argument of `iso_lattice` (transfer to the concrete model and the action of `levelRoots m`) would
give a contradiction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps FiniteTupleBlocks
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.ValueMaps
open DiamondIntegral.Section8.Galois
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open IntegrationInACVF.Section3ACVF

local instance mapSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance mapSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-- **Orthogonality.** A definable map into `Γ` takes finitely many values on a definable set
whose coordinates lie in definable sets with finitely many values. -/
theorem values_finite_of_volume {n : ℕ} {H : Set (Fin n → P.N)}
    (hH : DefinableOverBase (base P) (fun _ : Fin n => .rv) H) {μ : (Fin n → P.N) → Γ}
    (hμ : VolumeDefinable (base P) H μ) (D : Fin n → Set P.N)
    (hD : ∀ i, DefinableAtBase (base P) .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort P.N | t.val ∈ D i}).Finite)
    (hsub : ∀ u ∈ H, ∀ i, u i ∈ D i) : (μ '' H).Finite := by
  let R : (Fin n → P.N) → (Fin 1 → Γ) → Prop := fun u γ => u ∈ H ∧ γ 0 = μ u
  let σ : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cons (Sum.inr 0) Sum.inl
  have hR : mixedGammaTupleDefinable (base P) R := by
    have h := FullRawDefinable.reindex (P := fun w : Fin (n + 1) → P.N => w ∈ volumeGraph H μ)
      (integrationGammaDefinable hμ) σ
    refine FullBaseAtomicity.OverBase.congr h fun z => ?_
    change (z ∘ σ) ∈ volumeGraph _ _ ↔ _
    have htail : Fin.tail (z ∘ σ) = z ∘ Sum.inl := funext fun i => rfl
    have h0 : (z ∘ σ) 0 = z (Sum.inr 0) := rfl
    rw [mem_volumeGraph, htail, h0]
    change _ ↔ (∀ i : Fin 1, NonzeroRV (z (Sum.inr i))) ∧ z ∘ Sum.inl ∈ H ∧
      codeValue (z (Sum.inr 0)) = μ (z ∘ Sum.inl)
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨fun i => by rw [Subsingleton.elim i 0]; exact h2, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1 0, h3⟩
  have hcols := residue_gamma_tuple_finite_columns P.G.uncountable.le P.G.saturated P.G.model00
    (base P) P.G.small_real (by simpa using Cardinal.aleph0_pos.trans P.G.uncountable)
    (base_nontrivial P) R hR (fun u _ h i => hH.proper u h.1 i) H hH D hD hvalues hsub
  refine (hcols.biUnion (t := fun S => (fun γ : Fin 1 → Γ => γ 0) '' S) fun S hS => ?_).subset ?_
  · obtain ⟨u, hu, rfl⟩ := hS
    refine (Set.finite_singleton (μ u)).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    exact hγ.2
  · rintro _ ⟨u, hu, rfl⟩
    refine Set.mem_biUnion (x := relationColumn (fun γ u => R u γ) u) ⟨u, hu, rfl⟩ ?_
    exact ⟨fun _ => μ u, ⟨hu, rfl⟩, rfl⟩

/-- A definable set of the RV sort with finitely many given values. -/
theorem valueSet_definable (c : Γ) (hc : GammaDefinableClosureAtBase (base P) c) :
    DefinableAtBase (base P) .rv {x : P.N | iRV x ∧ codeValue x = c} := by
  have hU := BlowupChart.rv_universe_definable (base P) 1
  have h := preimage_definable (base P) hU (coord_volume_definable (base P) hU 0) hc
  show DefinableOverBase (base P) (fun _ : Fin 1 => .rv) {z | z 0 ∈ {x : P.N | iRV x ∧ codeValue x = c}}
  convert h using 1
  refine Set.ext fun z => ?_
  change (iRV (z 0) ∧ codeValue (z 0) = c) ↔
    (z ∈ sortedUniverse (fun _ : Fin 1 => SortTag.rv) ∧ codeValue (z 0) ∈ ({c} : Set Γ))
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun j => by rw [Subsingleton.elim j 0]; exact h1, h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1 0, h2⟩⟩

theorem valueSet_finite (c : Γ) :
    (Values.vrv '' {t : CanonicalRV.RVSort P.N | t.val ∈ {x : P.N | iRV x ∧ codeValue x = c}}).Finite := by
  refine ((Set.finite_singleton c.val).insert Values.infinity).subset ?_
  rintro x ⟨t, ht, rfl⟩
  by_cases h0 : t.val = iRVZero
  · exact Or.inl ((Values.vrv_eq_infinity_iff t).mpr h0)
  · right
    have hf := RVMeasuredBounds.finiteValue_vrv t
    have hne : Values.vrv t ≠ Values.infinity := fun h => h0 ((Values.vrv_eq_infinity_iff t).mp h)
    rw [ht.2] at hf
    rw [← hf]
    simp only [RVMeasuredBounds.finiteValue, hne, ne_eq, not_false_eq_true, ↓reduceDIte]
    rfl

theorem forall_coord_eq_definable {n : ℕ} {I : Set (Fin n → P.N)}
    (hI : DefinableOverBase (base P) (fun _ : Fin n => .rv) I) (γ : Fin n → Γ)
    (hγ : ∀ i, GammaDefinableClosureAtBase (base P) (γ i)) (s : Finset (Fin n)) :
    DefinableOverBase (base P) (fun _ : Fin n => .rv) {u | u ∈ I ∧ ∀ i ∈ s, codeValue (u i) = γ i} := by
  induction s using Finset.induction_on with
  | empty => simpa using hI
  | insert j s hj ih =>
    have h := DefinableOverBase.inter ih (preimage_definable (base P) hI
      (coord_volume_definable (base P) hI j) (hγ j))
    convert h using 1
    refine Set.ext fun u => ⟨fun ⟨hu, hl⟩ => ⟨⟨hu, fun i hi => hl i (Finset.mem_insert_of_mem hi)⟩,
      hu, hl j (Finset.mem_insert_self j s)⟩, fun ⟨⟨hu, hl⟩, _, hj'⟩ => ⟨hu, fun i hi => ?_⟩⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hj'
    · exact hl i hi

theorem graphOn_functional {n n' : ℕ} {A : Set (Fin n → P.N)} {F : (Fin n → P.N) → (Fin n' → P.N)}
    {w w' : Fin (n' + n) → P.N} (hw : w ∈ graphOn A F) (hw' : w' ∈ graphOn A F)
    (h : w ∘ headIndex n' n = w' ∘ headIndex n' n) : w = w' := by
  rw [← join_reconstruct n' n w, ← join_reconstruct n' n w', ← hw.2, ← hw'.2, h]

theorem join_mem_graphOn {n n' : ℕ} {A : Set (Fin n → P.N)} (F : (Fin n → P.N) → (Fin n' → P.N))
    {u : Fin n → P.N} (hu : u ∈ A) : join n' n u (F u) ∈ graphOn A F := by
  have hh : join n' n u (F u) ∘ headIndex n' n = u := funext fun i => join_head _ _ _ _ i
  have ht : join n' n u (F u) ∘ tailIndex n' n = F u := funext fun i => join_tail _ _ _ _ i
  show join n' n u (F u) ∘ headIndex n' n ∈ A ∧
    F (join n' n u (F u) ∘ headIndex n' n) = join n' n u (F u) ∘ tailIndex n' n
  rw [hh, ht]
  exact ⟨hu, rfl⟩

/-- The value of a coordinate of a definable map is a definable map. -/
theorem map_coord_volume {n n' : ℕ} {A : Set (Fin n → P.N)}
    (hA : DefinableOverBase (base P) (fun _ : Fin n => .rv) A) (F : (Fin n → P.N) → (Fin n' → P.N))
    (hF : DefinableOverBase (base P) (fun _ : Fin (n' + n) => .rv) (graphOn A F)) (j : Fin n') :
    VolumeDefinable (base P) A (fun u => codeValue (F u j)) := by
  -- The value map on the graph, pulled back along `u ↦ join u (F u)`.
  have hG := coord_volume_definable (base P) hF (tailIndex n' n j)
  let ρ : Fin (n + 1) → Fin (n' + n + 1) := Fin.cases 0 (fun i => (headIndex n' n i).succ)
  have h : DefinableOverBase (base P) (fun _ : Fin (n + 1) => SortTag.rv) ((fun w => w ∘ ρ) ''
      volumeGraph (graphOn A F) (fun w => codeValue (w (tailIndex n' n j)))) :=
    DefinableOverBase.image_real hG ρ
  unfold VolumeDefinable
  convert h using 1
  refine Set.ext fun w => ⟨?_, ?_⟩
  · rintro ⟨hwA, h0, hwv⟩
    refine ⟨Fin.cons (w 0) (join n' n (Fin.tail w) (F (Fin.tail w))), ⟨?_, h0, ?_⟩, ?_⟩
    · exact join_mem_graphOn P F hwA
    · simp only [Fin.tail, Fin.cons_zero, Fin.cons_succ, join_tail]
      exact hwv
    · funext i
      refine Fin.cases rfl (fun i => ?_) i
      change (Fin.cons (w 0) (join n' n (Fin.tail w) (F (Fin.tail w))) : Fin (n' + n + 1) → P.N)
        ((headIndex n' n i).succ) = w i.succ
      rw [Fin.cons_succ, join_head]
      rfl
  · rintro ⟨v, ⟨hv1, hv2, hv3⟩, rfl⟩
    have hhead : Fin.tail v ∘ headIndex n' n ∈ A := hv1.1
    refine ⟨?_, hv2, ?_⟩
    · convert hhead using 1
      funext i
      rfl
    · have hF' : F (Fin.tail v ∘ headIndex n' n) = Fin.tail v ∘ tailIndex n' n := hv1.2
      change codeValue (v 0) = codeValue (F (fun i => v (headIndex n' n i).succ) j)
      have : (fun i => v (headIndex n' n i).succ) = Fin.tail v ∘ headIndex n' n := rfl
      rw [this, hF']
      exact hv3

/-- **Definable maps preserve the lattice.** -/
theorem map_lattice {n n' : ℕ} {A : Set (Fin n → P.N)}
    (hA : DefinableOverBase (base P) (fun _ : Fin n => .rv) A) (F : (Fin n → P.N) → (Fin n' → P.N))
    (hF : DefinableOverBase (base P) (fun _ : Fin (n' + n) => .rv) (graphOn A F)) (m : ℕ+)
    {u : Fin n → P.N} (hu : u ∈ A) (hl : ∀ i, InLattice π m (codeValue (u i))) (j : Fin n') :
    InLattice π m (codeValue (F u j)) := by
  -- The value tuple of `u` is definable.
  have hγ : ∀ i, GammaDefinableClosureAtBase (base P) (codeValue (u i)) := fun i => by
    obtain ⟨z, hz⟩ := eq_qpow_of_inLattice m.ne_zero (hl i)
    rw [hz]; exact qpow_definable P _
  let H : Set (Fin n → P.N) := {u' | u' ∈ A ∧ ∀ i ∈ Finset.univ, codeValue (u' i) = codeValue (u i)}
  have hH : DefinableOverBase (base P) (fun _ : Fin n => .rv) H :=
    forall_coord_eq_definable P hA _ hγ Finset.univ
  have huH : u ∈ H := ⟨hu, fun _ _ => rfl⟩
  have hμ : VolumeDefinable (base P) H (fun u' => codeValue (F u' j)) :=
    volume_restrict (base P) (map_coord_volume P hA F hF j) hH (fun _ h => h.1)
  have hfin := values_finite_of_volume P hH hμ (fun i => {x | iRV x ∧ codeValue x = codeValue (u i)})
    (fun i => valueSet_definable P _ (hγ i)) (fun i => valueSet_finite P _)
    (fun u' hu' i => ⟨hA.proper u' hu'.1 i, hu'.2 i (Finset.mem_univ i)⟩)
  have hδ : GammaDefinableClosureAtBase (base P) (codeValue (F u j)) := by
    refine gamma_finset_element_definable_base (base P) hfin.toFinset ?_ _
      (hfin.mem_toFinset.mpr ⟨u, huH, rfl⟩)
    rw [hfin.coe_toFinset]
    exact image_definable (base P) hμ
  by_contra hbad
  -- The bad set.
  have hGH : DefinableOverBase (base P) (fun _ : Fin (n' + n) => .rv) (graphOn H F) := by
    have h := DefinableOverBase.inter hF (hH.preimage_real (fun _ : Fin (n' + n) => .rv) (headIndex n' n))
    convert h using 1
    refine Set.ext fun w => ⟨fun h1 => ⟨⟨h1.1.1, h1.2⟩, h1.1, hF.proper w ⟨h1.1.1, h1.2⟩⟩,
      fun h1 => ⟨h1.2.1, h1.1.2⟩⟩
  let Bad : Set (Fin (n' + n) → P.N) :=
    {w | w ∈ graphOn H F ∧ codeValue (w (tailIndex n' n j)) ∈ ({codeValue (F u j)} : Set Γ)}
  have hBad : DefinableOverBase (base P) (fun _ : Fin (n' + n) => .rv) Bad :=
    preimage_definable (base P) hGH (coord_volume_definable (base P) hGH (tailIndex n' n j)) hδ
  have hw : join n' n u (F u) ∈ Bad := ⟨join_mem_graphOn P F huH, by simp [join_tail]⟩
  obtain ⟨w₀, ⟨hgr, hval⟩⟩ := exists_concrete_point P hBad ⟨_, hw⟩
  have hsorted : ∀ i, iRV (P.e (w₀ i)) := fun i => hGH.proper _ hgr i
  let σ := carrierAction (levelRoots m)
  have hσgr : P.e ∘ (σ ∘ w₀) ∈ graphOn H F :=
    (raw_original_definable_invariant (levelRoots m) _ (trace_definable P hGH) w₀).mpr hgr
  have hhead_fixed : (σ ∘ w₀) ∘ headIndex n' n = w₀ ∘ headIndex n' n := by
    funext i
    refine fixed_of_lattice P m (hsorted _) ?_
    have := hgr.1.2 i (Finset.mem_univ i)
    change InLattice π m (codeValue ((P.e ∘ w₀) (headIndex n' n i)))
    rw [show (P.e ∘ w₀) (headIndex n' n i) = ((P.e ∘ w₀) ∘ headIndex n' n) i from rfl, this]
    exact hl i
  have hfix : P.e ∘ (σ ∘ w₀) = P.e ∘ w₀ := by
    refine graphOn_functional P hσgr hgr ?_
    funext i
    exact congrArg P.e (congrFun hhead_fixed i)
  have hfix' : σ ∘ w₀ = w₀ := funext fun i => P.e.injective (congrFun hfix i)
  have hj : ¬ InLattice π m (codeValue (P.e (w₀ (tailIndex n' n j)))) := by
    have : codeValue ((P.e ∘ w₀) (tailIndex n' n j)) = codeValue (F u j) := hval
    change ¬ InLattice π m (codeValue ((P.e ∘ w₀) (tailIndex n' n j)))
    rw [this]; exact hbad
  exact moved_of_not_lattice P m (hsorted _) hj (congrFun hfix' (tailIndex n' n j))

end DiamondIntegral.Section8.Hm
