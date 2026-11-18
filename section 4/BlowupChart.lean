import «section 4».AnnularBlowup
import «section 4».VariableApertureAnnularDomains
import «section 4».RVVariableMultiplication
import «section 4».RVDefinableTupleMaps

/-! Definition 7.2 (`defn:blowup:coa`), second layer: the elementary annular
blowup as actual bounded charts.

The shell `{(u,s) : 0 < vrv s ≤ γ(u)}` and the separately tagged endpoint
graph `{(u, τ(u))}` are each an actual chart with domain definable over the
original base, structural map `f♭(u,s)`, which is `f` with `s · f_j(u)` in
position `j`, and volume `ω(u)`. The definability of the structural map is
proved once for an arbitrary domain carrying `u` and `s` as raw coordinates.
Both charts are doubly bounded, with the aperture bound of Remark 7.4. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.BlowupChart
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section4.AnnularBlowup

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem nonzero_mul {a b : M} (ha : NonzeroRV a) (hb : NonzeroRV b) :
    NonzeroRV (iRVMul a b) :=
  ⟨rv_mul_mem hM ha.1 hb.1, fun h => ((rv_mul_eq_zero_of_model hM ha.1 hb.1).mp h).elim ha.2 hb.2⟩

/-- `(c, s) ↦ c` with `s · c_j` in position `j`, on raw tuples `join 1 k c ![s]`. -/
def updateMap (j : Fin k) (v : Fin (1 + k) → M) : Fin k → M :=
  Function.update (v ∘ headIndex 1 k) j (iRVMul (v (tailIndex 1 k 0)) (v (headIndex 1 k j)))

omit hM in
theorem updateMap_join (j : Fin k) (c : Fin k → M) (s : M) :
    updateMap j (join 1 k c ![s]) = Function.update c j (iRVMul s (c j)) := by
  have hc : (join 1 k c ![s]) ∘ headIndex 1 k = c := funext (fun i => join_head 1 k c ![s] i)
  simp only [updateMap, hc, join_head, join_tail, Matrix.cons_val_zero]

theorem rv_universe_definable (B : Base (M := M)) (n : ℕ) :
    DefinableOverBase B (fun _ : Fin n => .rv) (sortedUniverse (fun _ : Fin n => SortTag.rv) : Set (Fin n → M)) :=
  real_definableOverBase B _ _ (sortedUniverse_definable B.real _)

theorem updateMap_graph_definable (B : Base (M := M)) (j : Fin k) :
    DefinableOverBase B (fun _ : Fin (k + (1 + k)) => .rv)
      (graphOn (sortedUniverse (fun _ : Fin (1 + k) => SortTag.rv)) (updateMap j)) := by
  have hU := rv_universe_definable B (1 + k)
  apply RVDefinableTupleMaps.graph_definable B _ hU (updateMap j)
  intro i
  by_cases hi : i = j
  · subst hi
    have he : (fun v : Fin (1 + k) → M => ![updateMap i v i]) =
        (fun v => ![iRVMul (v (tailIndex 1 k 0)) (v (headIndex 1 k i))]) := by
      funext v
      simp only [updateMap, Function.update_self]
    rw [he]
    exact RVVariableMultiplication.scalar_graph_definable B _ hU (tailIndex 1 k 0) (headIndex 1 k i)
  · have he : (fun v : Fin (1 + k) → M => ![updateMap j v i]) =
        (fun v => v ∘ (fun _ : Fin 1 => headIndex 1 k i)) := by
      funext v l
      fin_cases l
      simp only [updateMap, Function.update_of_ne hi, Function.comp_apply]
      rfl
    rw [he]
    exact RVCoordinateMaps.coordinate_graph_definable B _ hU (fun _ : Fin 1 => headIndex 1 k i)

/-- The pair `(f(u), s)` read off a raw tuple carrying `u` and `s`. -/
def pairMap (r : Chart B k) {a : ℕ} (xπ : Fin r.arity → Fin a) (sIdx : Fin a)
    (w : Fin a → M) : Fin (1 + k) → M :=
  join 1 k (r.coordinate (w ∘ xπ)) ![w sIdx]

theorem pairMap_graph_definable (r : Chart B k) {a : ℕ} (I : Set (Fin a → M))
    (hI : DefinableOverBase B (fun _ : Fin a => .rv) I)
    (xπ : Fin r.arity → Fin a) (sIdx : Fin a) (hx : ∀ w ∈ I, w ∘ xπ ∈ r.domain) :
    DefinableOverBase B (fun _ : Fin ((1 + k) + a) => .rv) (graphOn I (pairMap r xπ sIdx)) := by
  have hU := rv_universe_definable B k
  have hc : DefinableOverBase B (fun _ : Fin (k + a) => .rv)
      (graphOn I (r.coordinate ∘ (fun w => w ∘ xπ))) :=
    RVGraphComposition.graph_compose_definable B I r.domain (fun w => w ∘ xπ) r.coordinate
      (RVCoordinateMaps.coordinate_graph_definable B I hI xπ) r.coordinate_definable hx
  apply RVDefinableTupleMaps.graph_definable B I hI (pairMap r xπ sIdx)
  apply GammaBoundedProducts.all_coordinates 1 k
    (fun l => DefinableOverBase B (fun _ : Fin (1 + a) => .rv)
      (graphOn I (fun w => ![pairMap r xπ sIdx w l]))) id
  · intro i
    have h := RVGraphComposition.graph_compose_definable B I
      (sortedUniverse (fun _ : Fin k => SortTag.rv)) (r.coordinate ∘ (fun w => w ∘ xπ))
      (fun c => c ∘ (fun _ : Fin 1 => i)) hc
      (RVCoordinateMaps.coordinate_graph_definable B _ hU (fun _ : Fin 1 => i))
      (fun w hw l => (r.coordinate_proper _ (hx w hw) l).1)
    have he : (fun w => ![pairMap r xπ sIdx w (headIndex 1 k i)]) =
        (fun c => c ∘ (fun _ : Fin 1 => i)) ∘ (r.coordinate ∘ (fun w => w ∘ xπ)) := by
      funext w l
      fin_cases l
      simp only [pairMap, join_head, Function.comp_apply]
      rfl
    change DefinableOverBase B (fun _ : Fin (1 + a) => .rv)
      (graphOn I (fun w => ![pairMap r xπ sIdx w (headIndex 1 k i)]))
    rw [he]
    exact h
  · intro i
    fin_cases i
    have he : (fun w => ![pairMap r xπ sIdx w (tailIndex 1 k 0)]) =
        (fun w => w ∘ (fun _ : Fin 1 => sIdx)) := by
      funext w l
      fin_cases l
      simp only [pairMap, join_tail, Function.comp_apply]
      rfl
    change DefinableOverBase B (fun _ : Fin (1 + a) => .rv)
      (graphOn I (fun w => ![pairMap r xπ sIdx w (tailIndex 1 k 0)]))
    rw [he]
    exact RVCoordinateMaps.coordinate_graph_definable B I hI (fun _ : Fin 1 => sIdx)

/-- The blown-up structural map has a definable graph on any definable domain
carrying `u` and `s` as raw coordinates. -/
theorem blown_graph_definable (r : Chart B k) (j : Fin k) {a : ℕ} (I : Set (Fin a → M))
    (hI : DefinableOverBase B (fun _ : Fin a => .rv) I)
    (xπ : Fin r.arity → Fin a) (sIdx : Fin a) (hx : ∀ w ∈ I, w ∘ xπ ∈ r.domain)
    (hs : ∀ w ∈ I, iRV (w sIdx)) :
    DefinableOverBase B (fun _ : Fin (k + a) => .rv)
      (graphOn I (fun w => blownCoordinate r j (w ∘ xπ) (w sIdx))) := by
  have h := RVGraphComposition.graph_compose_definable B I
    (sortedUniverse (fun _ : Fin (1 + k) => SortTag.rv)) (pairMap r xπ sIdx) (updateMap j)
    (pairMap_graph_definable r I hI xπ sIdx hx) (updateMap_graph_definable B j)
    (by
      intro w hw
      apply GammaBoundedProducts.all_coordinates 1 k (fun t : M => iRV t)
      · intro i
        simp only [pairMap, join_head]
        exact (r.coordinate_proper _ (hx w hw) i).1
      · intro i
        fin_cases i
        simp only [pairMap, join_tail]
        exact hs w hw)
  have he : updateMap j ∘ pairMap r xπ sIdx = (fun w => blownCoordinate r j (w ∘ xπ) (w sIdx)) := by
    funext w
    simp only [Function.comp_apply, pairMap, updateMap_join, blownCoordinate]
  rw [he] at h
  exact h

/-- A piece of a blowup: a definable domain carrying `u` and `s` as raw
coordinates, injectively, landing in a set of points on which `f♭` is
finite-to-one. -/
def pieceChart (r : Chart B k) (j : Fin k) {a : ℕ} (I : Set (Fin a → M))
    (hI : DefinableOverBase B (fun _ : Fin a => .rv) I)
    (xπ : Fin r.arity → Fin a) (sIdx : Fin a) (hx : ∀ w ∈ I, w ∘ xπ ∈ r.domain)
    (hs : ∀ w ∈ I, NonzeroRV (w sIdx))
    (hinj : Set.InjOn (fun w => (w ∘ xπ, w sIdx)) I)
    (P : Set ((Fin r.arity → M) × M)) (hP : ∀ w ∈ I, (w ∘ xπ, w sIdx) ∈ P)
    (hfin : ∀ t, {p | p ∈ P ∧ blownCoordinate r j p.1 p.2 = t}.Finite) : Chart B k where
  arity := a
  domain := I
  domain_definable := hI
  coordinate := fun w => blownCoordinate r j (w ∘ xπ) (w sIdx)
  coordinate_definable := blown_graph_definable r j I hI xπ sIdx hx (fun w hw => (hs w hw).1)
  coordinate_proper := by
    intro w hw i
    by_cases hi : i = j
    · subst hi
      rw [blownCoordinate_at]
      exact nonzero_mul (hs w hw) (r.coordinate_proper _ (hx w hw) i)
    · simp only [blownCoordinate, Function.update_of_ne hi]
      exact r.coordinate_proper _ (hx w hw) i
  finite_fibres := by
    intro t
    refine Set.Finite.of_finite_image (f := fun w => (w ∘ xπ, w sIdx)) ?_ ?_
    · apply (hfin t).subset
      rintro p ⟨w, ⟨hw, he⟩, rfl⟩
      exact ⟨hP w hw, he⟩
    · exact hinj.mono (fun w hw => hw.1)
  volume := fun w => r.volume (w ∘ xπ)
  volume_definable := RVVolumeMaps.reindex_restrict_definable B r.domain I hI r.volume
    r.volume_definable xπ hx

theorem pieceChart_weight (r : Chart B k) (j : Fin k) {a : ℕ} (I : Set (Fin a → M))
    (hI : DefinableOverBase B (fun _ : Fin a => .rv) I)
    (xπ : Fin r.arity → Fin a) (sIdx : Fin a) (hx : ∀ w ∈ I, w ∘ xπ ∈ r.domain)
    (hs : ∀ w ∈ I, NonzeroRV (w sIdx))
    (hinj : Set.InjOn (fun w => (w ∘ xπ, w sIdx)) I)
    (P : Set ((Fin r.arity → M) × M)) (hP : ∀ w ∈ I, (w ∘ xπ, w sIdx) ∈ P)
    (hfin : ∀ t, {p | p ∈ P ∧ blownCoordinate r j p.1 p.2 = t}.Finite) (w : Fin a → M) :
    (pieceChart r j I hI xπ sIdx hx hs hinj P hP hfin).correctedWeight w =
      r.volume (w ∘ xπ) * ∏ l, codeValue (blownCoordinate r j (w ∘ xπ) (w sIdx) l) := rfl

/-! The aperture graph and the two pieces. -/

/-- The chart with the aperture adjoined as the raw coordinate `aIdx`. -/
def graphChart (r : Chart B k) (τ : Aperture r) : Chart B k :=
  RVDefinableGraphExtension.chart r τ.aperture τ.graph_definable

def aIdx (r : Chart B k) : Fin (1 + r.arity) := tailIndex 1 r.arity 0

theorem graph_canonical (r : Chart B k) (τ : Aperture r) {w : Fin (1 + r.arity) → M}
    (hw : w ∈ (graphChart r τ).domain) :
    w = join 1 r.arity (w ∘ headIndex 1 r.arity) ![τ.aperture (w ∘ headIndex 1 r.arity)] := by
  have h := join_reconstruct 1 r.arity w
  have ht : w ∘ tailIndex 1 r.arity = ![τ.aperture (w ∘ headIndex 1 r.arity)] := hw.2.symm
  rw [ht] at h
  exact h.symm

theorem graph_aperture (r : Chart B k) (τ : Aperture r) {w : Fin (1 + r.arity) → M}
    (hw : w ∈ (graphChart r τ).domain) : w (aIdx r) = τ.aperture (w ∘ headIndex 1 r.arity) :=
  (congrFun hw.2 0).symm

theorem graph_aperture_nonzero (r : Chart B k) (τ : Aperture r) :
    ∀ w ∈ (graphChart r τ).domain, NonzeroRV (w (aIdx r)) := by
  intro w hw
  rw [graph_aperture r τ hw]
  exact τ.nonzero _ hw.1

theorem graph_aperture_bounded (r : Chart B k) (τ : Aperture r) :
    ∀ w ∈ (graphChart r τ).domain, codeValue (w (aIdx r)) ≤ τ.bound := by
  intro w hw
  rw [graph_aperture r τ hw]
  exact τ.bounded _ hw.1

theorem graph_domain_bounded (r : Chart B k) (τ : Aperture r)
    (hr : RVMeasuredBounds.DomainBounded r) :
    RVMeasuredBounds.DomainBounded (graphChart r τ) := by
  obtain ⟨β, hβ⟩ := hr
  let η := max β (max τ.bound 1)
  have hβη : β ≤ η := le_max_left _ _
  have hΔη : τ.bound ≤ η := (le_max_left _ _).trans (le_max_right _ _)
  have h1η : (1 : Values.Gamma (M := M)) ≤ η := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨η, ?_⟩
  intro u hu i hi
  have hall : ∀ i : Fin (1 + r.arity), NonzeroRV (u i) →
      η⁻¹ ≤ codeValue (u i) ∧ codeValue (u i) ≤ η := by
    apply GammaBoundedProducts.all_coordinates 1 r.arity
      (fun t => NonzeroRV t → η⁻¹ ≤ codeValue t ∧ codeValue t ≤ η) u
    · intro l hl
      have hb := hβ (u ∘ headIndex 1 r.arity) hu.1 l hl
      exact ⟨(inv_le_inv_iff.mpr hβη).trans hb.1, hb.2.trans hβη⟩
    · intro l _
      fin_cases l
      change η⁻¹ ≤ codeValue (u (aIdx r)) ∧ codeValue (u (aIdx r)) ≤ η
      rw [graph_aperture r τ hu]
      have hl : η⁻¹ ≤ 1 := by simpa only [inv_one] using inv_le_inv_iff.mpr h1η
      exact ⟨hl.trans (τ.nonnegative _ hu.1), (τ.bounded _ hu.1).trans hΔη⟩
  exact hall i hi

/-- The endpoint piece: the aperture graph, with `s = τ(u)`. -/
def endpointChart (r : Chart B k) (j : Fin k) (hfin : InactiveFinite r j) (τ : Aperture r) :
    Chart B k :=
  pieceChart r j (graphChart r τ).domain (graphChart r τ).domain_definable
    (headIndex 1 r.arity) (aIdx r) (fun _ hw => hw.1) (graph_aperture_nonzero r τ)
    (by
      intro w hw v hv he
      have h1 : w ∘ headIndex 1 r.arity = v ∘ headIndex 1 r.arity := congrArg Prod.fst he
      rw [graph_canonical r τ hw, graph_canonical r τ hv, h1])
    (endpointPoints r τ) (fun w hw => ⟨hw.1, graph_aperture r τ hw⟩)
    (endpoint_finite_fibres r j hfin τ)

/-- The domain of the shell: Section 4's annulus over the aperture graph. -/
def shellDomain (r : Chart B k) (τ : Aperture r) : Set (Fin (1 + (1 + r.arity)) → M) :=
  (VariableApertureRayCancellation.annularChart (graphChart r τ) (aIdx r)).domain

def xIdx (r : Chart B k) : Fin r.arity → Fin (1 + (1 + r.arity)) :=
  fun i => headIndex 1 (1 + r.arity) (headIndex 1 r.arity i)

def sIdx (r : Chart B k) : Fin (1 + (1 + r.arity)) := tailIndex 1 (1 + r.arity) 0

theorem shell_mem (r : Chart B k) (τ : Aperture r) {w : Fin (1 + (1 + r.arity)) → M}
    (hw : w ∈ shellDomain r τ) :
    w ∘ headIndex 1 (1 + r.arity) ∈ (graphChart r τ).domain ∧ Proper (w ∘ tailIndex 1 (1 + r.arity)) ∧
      1 < codeValue (w (sIdx r)) ∧ codeValue (w (sIdx r)) ≤ codeValue ((w ∘ headIndex 1 (1 + r.arity)) (aIdx r)) := by
  have h := (VariableApertureRayCancellation.annularChart_join_iff (graphChart r τ) (aIdx r)
    (graph_aperture_nonzero r τ) (w ∘ headIndex 1 (1 + r.arity)) (w ∘ tailIndex 1 (1 + r.arity))).mp
    (by
      show join 1 (1 + r.arity) (w ∘ headIndex 1 (1 + r.arity)) (w ∘ tailIndex 1 (1 + r.arity)) ∈
        shellDomain r τ
      rw [join_reconstruct]
      exact hw)
  exact h

theorem shell_points (r : Chart B k) (τ : Aperture r) {w : Fin (1 + (1 + r.arity)) → M}
    (hw : w ∈ shellDomain r τ) : (w ∘ xIdx r, w (sIdx r)) ∈ shellPoints r τ := by
  obtain ⟨hg, hp, h1, h2⟩ := shell_mem r τ hw
  refine ⟨hg.1, hp 0, h1, ?_⟩
  rw [graph_aperture r τ hg] at h2
  exact h2

theorem shell_canonical (r : Chart B k) (τ : Aperture r) {w : Fin (1 + (1 + r.arity)) → M}
    (hw : w ∈ shellDomain r τ) :
    w = join 1 (1 + r.arity) (join 1 r.arity (w ∘ xIdx r) ![τ.aperture (w ∘ xIdx r)]) ![w (sIdx r)] := by
  have hg := (shell_mem r τ hw).1
  have h := join_reconstruct 1 (1 + r.arity) w
  have ht : w ∘ tailIndex 1 (1 + r.arity) = ![w (sIdx r)] := by
    funext l
    fin_cases l
    rfl
  have hh := graph_canonical r τ hg
  rw [ht, hh] at h
  exact h.symm

/-- The shell piece. -/
def shellChart (r : Chart B k) (j : Fin k) (hfin : InactiveFinite r j) (τ : Aperture r) :
    Chart B k :=
  pieceChart r j (shellDomain r τ)
    (VariableApertureRayCancellation.annularChart (graphChart r τ) (aIdx r)).domain_definable
    (xIdx r) (sIdx r) (fun _ hw => (shell_points r τ hw).1) (fun _ hw => (shell_points r τ hw).2.1)
    (by
      intro w hw v hv he
      have h1 : w ∘ xIdx r = v ∘ xIdx r := congrArg Prod.fst he
      have h2 : w (sIdx r) = v (sIdx r) := congrArg Prod.snd he
      rw [shell_canonical r τ hw, shell_canonical r τ hv, h1, h2])
    (shellPoints r τ) (fun _ hw => shell_points r τ hw)
    (shell_finite_fibres r j hfin τ)

theorem endpoint_domain_bounded (r : Chart B k) (j : Fin k) (hfin : InactiveFinite r j)
    (τ : Aperture r) (hr : RVMeasuredBounds.DomainBounded r) :
    RVMeasuredBounds.DomainBounded (endpointChart r j hfin τ) :=
  graph_domain_bounded r τ hr

theorem shell_domain_bounded (r : Chart B k) (j : Fin k) (hfin : InactiveFinite r j)
    (τ : Aperture r) (hr : RVMeasuredBounds.DomainBounded r) :
    RVMeasuredBounds.DomainBounded (shellChart r j hfin τ) :=
  VariableApertureRayCancellation.annularChart_domain_bounded (graphChart r τ) (aIdx r)
    (graph_aperture_nonzero r τ) (graph_domain_bounded r τ hr) τ.bound (graph_aperture_bounded r τ)

end DiamondIntegral.Section4.BlowupChart
