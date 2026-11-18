import «section 4».BlowupChart
import «section 4».FunctionalApertureCompatibility
import «section 4».VariableApertureMeasuredComparison
import «section 4».RVPointProductIsomorphisms
import «section 4».RVBoundedRing
import «section 4».RVPointChoices
import «section 4».RVRadiusGenerators

/-! Definition 7.2 and Notation 4.17: an elementary annular blowup of a doubly
bounded object differs from it by a generator of the relative annular ideal.

For `U = (U, f, ω)` in degree `1+k` blown up in coordinate `j` with aperture
`τ`, the base `W = (U with τ adjoined, f with j removed, ω + vrv f_j)` of
degree `k`, the aperture graph as source and the endpoint piece form a
Section 4 presentation. Its shell is the shell piece up to the identity
isomorphism, and its source is `U` up to projection. Hence
`[shell] + [endpoint] - [U]` is the corresponding generator of `J_var`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.BlowupRelation
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section4.AnnularBlowup DiamondIntegral.Section4.BlowupChart

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

/-- The value of a definable nonzero RV function is a definable volume. -/
theorem codeValue_volume_definable {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (F : (Fin n → M) → M)
    (hF : DefinableOverBase B (fun _ : Fin (1 + n) => .rv) (graphOn I (fun u => ![F u])))
    (hFn : ∀ u ∈ I, NonzeroRV (F u)) :
    RVVolumeMaps.VolumeDefinable B I (fun u => codeValue (F u)) := by
  let ρ : Fin (1 + n) → Fin (n + 2) := join 1 n (fun i : Fin n => i.succ.succ) ![(1 : Fin (n + 2))]
  let π2 : Fin 2 → Fin (n + 2) := ![0, 1]
  let σ : Fin (n + 1) → Fin (n + 2) := Fin.cons 0 (fun i : Fin n => i.succ.succ)
  have hQ := (hF.preimage_real (fun _ : Fin (n + 2) => .rv) ρ).inter
    ((VariableApertureMeasuredComparison.value_equality_definable B).preimage_real
      (fun _ : Fin (n + 2) => .rv) π2)
  have h := hQ.image_real σ
  have hρh : ∀ v : Fin (n + 2) → M, (v ∘ ρ) ∘ headIndex 1 n = fun i => v i.succ.succ := by
    intro v
    funext i
    simp only [Function.comp_apply, ρ, join_head]
  have hρt : ∀ v : Fin (n + 2) → M, (v ∘ ρ) ∘ tailIndex 1 n = ![v 1] := by
    intro v
    funext l
    fin_cases l
    simp only [Function.comp_apply, ρ, join_tail]
    rfl
  change DefinableOverBase B (fun _ : Fin (n + 1) => .rv)
    (RVVolumeMaps.volumeGraph I (fun u => codeValue (F u)))
  have hset : RVVolumeMaps.volumeGraph I (fun u => codeValue (F u)) =
      (fun x => x ∘ σ) '' ({z | (z ∘ ρ ∈ graphOn I fun u => ![F u]) ∧
        z ∈ sortedUniverse (fun _ : Fin (n + 2) => SortTag.rv)} ∩
        {z | z ∘ π2 ∈ {z | Proper z ∧ codeValue (z 0) = codeValue (z 1)} ∧
          z ∈ sortedUniverse (fun _ : Fin (n + 2) => SortTag.rv)}) := by
    apply Set.ext
    intro w
    constructor
    · rintro ⟨hu, h0, he⟩
      let v : Fin (n + 2) → M := Fin.cons (w 0) (Fin.cons (F (Fin.tail w)) (Fin.tail w))
      have hv : v ∈ sortedUniverse (fun _ : Fin (n + 2) => SortTag.rv) :=
        fun i => Fin.cases h0.1 (fun l => Fin.cases (hFn _ hu).1 (fun m => hI.proper _ hu m) l) i
      have hvh : (fun i : Fin n => v i.succ.succ) = Fin.tail w := rfl
      refine ⟨v, ⟨⟨⟨?_, ?_⟩, hv⟩, ⟨⟨?_, ?_⟩, hv⟩⟩, ?_⟩
      · rw [hρh v, hvh]
        exact hu
      · rw [hρh v, hρt v, hvh]
        rfl
      · intro i
        fin_cases i
        · exact h0
        · exact hFn _ hu
      · exact he
      · funext i
        exact Fin.cases rfl (fun l => rfl) i
    · rintro ⟨v, ⟨⟨⟨hg1, hg2⟩, _⟩, ⟨⟨hp, he⟩, _⟩⟩, rfl⟩
      rw [hρh v] at hg1 hg2
      rw [hρt v] at hg2
      have hF1 : F (fun i => v i.succ.succ) = v 1 := congrFun hg2 0
      refine ⟨hg1, hp 0, ?_⟩
      change codeValue (v 0) = codeValue (F (fun i => v i.succ.succ))
      rw [hF1]
      exact he
  rw [hset]
  exact h

variable {k : ℕ}

/-- The coordinate embedding of `Fin k` into `Fin (1+k)` that skips `j`. -/
def skip (j : Fin (1 + k)) (i : Fin k) : Fin (1 + k) :=
  Fin.cast (Nat.add_comm k 1) ((Fin.cast (Nat.add_comm 1 k) j).succAbove i)

theorem skip_ne (j : Fin (1 + k)) (i : Fin k) : skip j i ≠ j := by
  intro h
  apply Fin.succAbove_ne (Fin.cast (Nat.add_comm 1 k) j) i
  apply Fin.ext
  have := congrArg Fin.val h
  simpa only [skip, Fin.val_cast] using this

theorem exists_skip (j : Fin (1 + k)) (l : Fin (1 + k)) (hl : l ≠ j) : ∃ i, skip j i = l := by
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (x := Fin.cast (Nat.add_comm 1 k) l)
    (y := Fin.cast (Nat.add_comm 1 k) j) (by
      intro h
      exact hl (Fin.ext (by simpa only [Fin.val_cast] using congrArg Fin.val h)))
  refine ⟨i, Fin.ext ?_⟩
  simpa only [skip, Fin.val_cast] using congrArg Fin.val hi

theorem prod_split {α : Type*} [CommMonoid α] (j : Fin (1 + k)) (g : Fin (1 + k) → α) :
    ∏ l, g l = g j * ∏ i, g (skip j i) := by
  let e : Fin (k + 1) ≃ Fin (1 + k) := finCongr (Nat.add_comm k 1)
  have h1 : ∏ l, g l = ∏ m, g (e m) := (Equiv.prod_comp e g).symm
  rw [h1, Fin.prod_univ_succAbove (fun m => g (e m)) (Fin.cast (Nat.add_comm 1 k) j)]
  congr 1

variable (r : Chart B (1 + k)) (j : Fin (1 + k)) (hfin : InactiveFinite r j) (τ : Aperture r)

/-! The base `W` on the domain of `U`: coordinate `j` is removed and its value
moved into the volume, so `W` has the same total weight as `U`. -/

theorem coordJ_definable :
    DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv)
      (graphOn r.domain (fun x => ![r.coordinate x j])) := by
  have h : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv)
      (graphOn r.domain ((fun c => c ∘ (fun _ : Fin 1 => j)) ∘ r.coordinate)) :=
    RVGraphComposition.graph_compose_definable B r.domain
      (sortedUniverse (fun _ : Fin (1 + k) => SortTag.rv)) r.coordinate
      (fun c => c ∘ (fun _ : Fin 1 => j)) r.coordinate_definable
      (RVCoordinateMaps.coordinate_graph_definable B _ (rv_universe_definable B (1 + k))
        (fun _ : Fin 1 => j))
      (fun x hx l => (r.coordinate_proper x hx l).1)
  have he : ((fun c => c ∘ (fun _ : Fin 1 => j)) ∘ r.coordinate) =
      (fun x : Fin r.arity → M => ![r.coordinate x j]) := by
    funext x l
    fin_cases l
    rfl
  rw [he] at h
  exact h

include hfin in
theorem base_finite (t : Fin k → M) :
    {x | x ∈ r.domain ∧ r.coordinate x ∘ skip j = t}.Finite := by
  by_cases hne : {x | x ∈ r.domain ∧ r.coordinate x ∘ skip j = t}.Nonempty
  · obtain ⟨x0, hx0, ht0⟩ := hne
    apply (hfin (inactive r j x0)).subset
    rintro x ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    funext l
    by_cases hl : l = j
    · subst hl
      simp only [inactive, Function.update_self]
    · obtain ⟨i, rfl⟩ := exists_skip j l hl
      simp only [inactive, Function.update_of_ne hl]
      exact (congrFun ht i).trans (congrFun ht0 i).symm
  · refine Set.Finite.subset Set.finite_empty ?_
    intro x hx
    exact hne ⟨x, hx⟩

theorem baseCoord_definable :
    DefinableOverBase B (fun _ : Fin (k + r.arity) => .rv)
      (graphOn r.domain (fun x => r.coordinate x ∘ skip j)) := by
  have h : DefinableOverBase B (fun _ : Fin (k + r.arity) => .rv)
      (graphOn r.domain ((fun c => c ∘ skip j) ∘ r.coordinate)) :=
    RVGraphComposition.graph_compose_definable B r.domain
      (sortedUniverse (fun _ : Fin (1 + k) => SortTag.rv)) r.coordinate
      (fun c => c ∘ skip j) r.coordinate_definable
      (RVCoordinateMaps.coordinate_graph_definable B _ (rv_universe_definable B (1 + k)) (skip j))
      (fun x hx l => (r.coordinate_proper x hx l).1)
  exact h

theorem baseVol_definable :
    RVVolumeMaps.VolumeDefinable B r.domain (fun x => r.volume x * codeValue (r.coordinate x j)) :=
  RVVolumeMaps.multiply_definable B r.domain r.domain_definable r.volume
    (fun x => codeValue (r.coordinate x j)) r.volume_definable
    (codeValue_volume_definable r.domain r.domain_definable (fun x => r.coordinate x j)
      (coordJ_definable r j) (fun x hx => r.coordinate_proper x hx j))

/-- The base `W = (U, f_{~j}, ω + vrv f_j)` of degree `k`. -/
def baseChart : Chart B k where
  arity := r.arity
  domain := r.domain
  domain_definable := r.domain_definable
  coordinate := fun x => r.coordinate x ∘ skip j
  coordinate_definable := baseCoord_definable r j
  coordinate_proper := fun x hx i => r.coordinate_proper x hx (skip j i)
  finite_fibres := base_finite r j hfin
  volume := fun x => r.volume x * codeValue (r.coordinate x j)
  volume_definable := baseVol_definable r j

theorem baseChart_weight (x : Fin r.arity → M) :
    (baseChart r j hfin).correctedWeight x = r.correctedWeight x := by
  change r.volume x * codeValue (r.coordinate x j) * ∏ i, codeValue (r.coordinate x (skip j i)) =
    r.volume x * ∏ l, codeValue (r.coordinate x l)
  rw [prod_split j (fun l => codeValue (r.coordinate x l)), mul_assoc]

/-- The blown-up structural map at the endpoint, as a function of `u`. -/
def endpointCoord (x : Fin r.arity → M) : Fin (1 + k) → M :=
  blownCoordinate r j x (τ.aperture x)

theorem endpointCoord_definable :
    DefinableOverBase B (fun _ : Fin ((1 + k) + r.arity) => .rv)
      (graphOn r.domain (endpointCoord r j τ)) := by
  have hG : DefinableOverBase B (fun _ : Fin ((1 + r.arity) + r.arity) => .rv)
      (graphOn r.domain (fun x => join 1 r.arity x ![τ.aperture x])) := by
    apply RVDefinableTupleMaps.graph_definable B r.domain r.domain_definable
    apply GammaBoundedProducts.all_coordinates 1 r.arity
      (fun l => DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv)
        (graphOn r.domain (fun x => ![join 1 r.arity x ![τ.aperture x] l]))) id
    · intro i
      have he : (fun x : Fin r.arity → M => ![join 1 r.arity x ![τ.aperture x] (headIndex 1 r.arity i)]) =
          (fun x => x ∘ (fun _ : Fin 1 => i)) := by
        funext x l
        fin_cases l
        simp only [join_head]
        rfl
      change DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv)
        (graphOn r.domain (fun x => ![join 1 r.arity x ![τ.aperture x] (headIndex 1 r.arity i)]))
      rw [he]
      exact RVCoordinateMaps.coordinate_graph_definable B _ r.domain_definable (fun _ : Fin 1 => i)
    · intro i
      fin_cases i
      have he : (fun x : Fin r.arity → M => ![join 1 r.arity x ![τ.aperture x] (tailIndex 1 r.arity 0)]) =
          (fun x => ![τ.aperture x]) := by
        funext x l
        fin_cases l
        simp only [join_tail]
        rfl
      change DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv)
        (graphOn r.domain (fun x => ![join 1 r.arity x ![τ.aperture x] (tailIndex 1 r.arity 0)]))
      rw [he]
      exact τ.graph_definable
  have h : DefinableOverBase B (fun _ : Fin ((1 + k) + r.arity) => .rv)
      (graphOn r.domain ((fun w : Fin (1 + r.arity) → M =>
        blownCoordinate r j (w ∘ headIndex 1 r.arity) (w (aIdx r))) ∘
        (fun x => join 1 r.arity x ![τ.aperture x]))) :=
    RVGraphComposition.graph_compose_definable B r.domain (graphChart r τ).domain
    (fun x => join 1 r.arity x ![τ.aperture x])
    (fun w => blownCoordinate r j (w ∘ headIndex 1 r.arity) (w (aIdx r))) hG
    (blown_graph_definable r j (graphChart r τ).domain (graphChart r τ).domain_definable
      (headIndex 1 r.arity) (aIdx r) (fun _ hw => hw.1) (fun w hw => (graph_aperture_nonzero r τ w hw).1))
    (by
      intro x hx
      refine ⟨?_, ?_⟩
      · have : (join 1 r.arity x ![τ.aperture x]) ∘ headIndex 1 r.arity = x :=
          funext (fun i => join_head 1 r.arity x _ i)
        change (join 1 r.arity x ![τ.aperture x]) ∘ headIndex 1 r.arity ∈ r.domain
        rw [this]
        exact hx
      · have h1 : (join 1 r.arity x ![τ.aperture x]) ∘ headIndex 1 r.arity = x :=
          funext (fun i => join_head 1 r.arity x _ i)
        change ![τ.aperture ((join 1 r.arity x ![τ.aperture x]) ∘ headIndex 1 r.arity)] =
          (join 1 r.arity x ![τ.aperture x]) ∘ tailIndex 1 r.arity
        rw [h1]
        funext l
        fin_cases l
        simp only [Function.comp_apply, join_tail])
  have he : ((fun w : Fin (1 + r.arity) → M =>
      blownCoordinate r j (w ∘ headIndex 1 r.arity) (w (aIdx r))) ∘
      (fun x => join 1 r.arity x ![τ.aperture x])) = endpointCoord r j τ := by
    funext x
    have h1 : (join 1 r.arity x ![τ.aperture x]) ∘ headIndex 1 r.arity = x :=
      funext (fun i => join_head 1 r.arity x _ i)
    simp only [Function.comp_apply, h1, endpointCoord, aIdx, join_tail]
    rfl
  rw [he] at h
  exact h

/-- The endpoint piece on the domain of `U`. -/
def endpointBase : Chart B (1 + k) where
  arity := r.arity
  domain := r.domain
  domain_definable := r.domain_definable
  coordinate := endpointCoord r j τ
  coordinate_definable := endpointCoord_definable r j τ
  coordinate_proper := by
    intro x hx i
    by_cases hi : i = j
    · subst hi
      simp only [endpointCoord, blownCoordinate_at]
      exact nonzero_mul (τ.nonzero x hx) (r.coordinate_proper x hx i)
    · simp only [endpointCoord, blownCoordinate, Function.update_of_ne hi]
      exact r.coordinate_proper x hx i
  finite_fibres := by
    intro t
    refine Set.Finite.of_finite_image (f := fun x => (x, τ.aperture x)) ?_ ?_
    · apply (endpoint_finite_fibres r j hfin τ t).subset
      rintro p ⟨x, ⟨hx, he⟩, rfl⟩
      exact ⟨⟨hx, rfl⟩, he⟩
    · intro x _ y _ he
      exact congrArg Prod.fst he
  volume := r.volume
  volume_definable := r.volume_definable

theorem endpointBase_weight (x : Fin r.arity → M) (hx : x ∈ r.domain) :
    (endpointBase r j hfin τ).correctedWeight x =
      (baseChart r j hfin).correctedWeight x * codeValue (τ.aperture x) := by
  rw [baseChart_weight]
  simp only [Chart.correctedWeight, endpointBase, endpointCoord]
  rw [prod_split j, prod_split j (fun l => codeValue (r.coordinate x l)), blownCoordinate_at,
    GammaGroupNames.codeValue_mul _ _ (τ.nonzero _ hx) (r.coordinate_proper _ hx j)]
  have hs : ∀ i, blownCoordinate r j x (τ.aperture x) (skip j i) = r.coordinate x (skip j i) := by
    intro i
    simp only [blownCoordinate, Function.update_of_ne (skip_ne j i)]
  simp only [hs]
  ac_rfl

/-- The Section 4 presentation of the blowup. -/
def presentation (hr : RVMeasuredBounds.DomainBounded r) :
    FunctionalApertureCompatibility.Presentation B k where
  base := ⟨baseChart r j hfin, by
    obtain ⟨β, hβ⟩ := hr
    exact ⟨β, hβ⟩⟩
  aperture := τ.aperture
  graph_definable := τ.graph_definable
  aperture_nonzero := τ.nonzero
  aperture_nonnegative := τ.nonnegative
  upperBound := τ.bound
  aperture_bounded := τ.bounded
  source := RVChartDisjointUnion.ofChart r
  endpoint := RVChartDisjointUnion.ofChart (endpointBase r j hfin τ)
  source_domain := rfl
  endpoint_domain := rfl
  source_weight := fun x _ => (baseChart_weight r j hfin x).symm
  endpoint_weight := fun x hx => endpointBase_weight r j hfin τ x hx

variable (hr : RVMeasuredBounds.DomainBounded r)

/-- The coordinate presentation behind the Section 4 generator. -/
abbrev coordinatePresentation : VariableApertureCompatibility.Presentation B k :=
  (presentation r j hfin τ hr).toCoordinate

def shellBounded : RVBoundedCharts.BoundedChart B (1 + k) :=
  ⟨shellChart r j hfin τ, shell_domain_bounded r j hfin τ hr⟩

def endpointBounded : RVBoundedCharts.BoundedChart B (1 + k) :=
  ⟨endpointChart r j hfin τ, endpoint_domain_bounded r j hfin τ hr⟩

def sourceBounded : RVBoundedCharts.BoundedChart B (1 + k) := ⟨r, hr⟩

omit [LRV.Structure M] hM in
theorem idBij {n : ℕ} (I : Set (Fin n → M)) : Set.BijOn (fun u => u ∘ (id : Fin n → Fin n)) I I :=
  ⟨fun _ hu => hu, fun _ _ _ _ h => h, fun u hu => ⟨u, hu, rfl⟩⟩

theorem shell_weight (u : Fin (1 + (1 + r.arity)) → M) (hu : u ∈ shellDomain r τ) :
    (shellChart r j hfin τ).correctedWeight u =
      r.correctedWeight (u ∘ xIdx r) * codeValue (u (sIdx r)) := by
  have hp := shell_points r τ hu
  unfold shellChart
  rw [pieceChart_weight]
  simp only [Chart.correctedWeight]
  rw [prod_split j, prod_split j (fun l => codeValue (r.coordinate (u ∘ xIdx r) l)), blownCoordinate_at,
    GammaGroupNames.codeValue_mul _ _ hp.2.1 (r.coordinate_proper _ hp.1 j)]
  have hs : ∀ i, blownCoordinate r j (u ∘ xIdx r) (u (sIdx r)) (skip j i) =
      r.coordinate (u ∘ xIdx r) (skip j i) := by
    intro i
    simp only [blownCoordinate, Function.update_of_ne (skip_ne j i)]
  simp only [hs]
  ac_rfl

def shellIso :
    Iso (coordinatePresentation r j hfin τ hr).shell.toChart (shellBounded r j hfin τ hr).toChart :=
  RVCoordinateMaps.coordinateIso _ _ id (idBij (shellDomain r τ)) (by
    intro u hu
    have h1 : (coordinatePresentation r j hfin τ hr).shell.toChart.correctedWeight u =
        (RVMeasuredProduct.product (coordinatePresentation r j hfin τ hr).base.toChart
          (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B))).correctedWeight u := rfl
    rw [h1, RVPointProductIsomorphisms.product_weight_coordinates,
      VariableApertureMeasuredComparison.ray_weight]
    change (baseChart r j hfin).correctedWeight (u ∘ xIdx r) * codeValue (u (sIdx r)) =
      (shellChart r j hfin τ).correctedWeight u
    rw [baseChart_weight]
    exact (shell_weight r j hfin τ u hu).symm)

def endpointIso :
    Iso (coordinatePresentation r j hfin τ hr).endpointBounded.toChart
      (endpointBounded r j hfin τ hr).toChart :=
  RVCoordinateMaps.coordinateIso _ _ id (idBij (graphChart r τ).domain) (by
    intro u hu
    have h1 : (coordinatePresentation r j hfin τ hr).endpointBounded.toChart.correctedWeight u =
        (endpointBase r j hfin τ).correctedWeight (u ∘ headIndex 1 r.arity) := rfl
    have h2 : (endpointBounded r j hfin τ hr).toChart.correctedWeight (u ∘ id) =
        r.volume (u ∘ headIndex 1 r.arity) *
          ∏ l, codeValue (blownCoordinate r j (u ∘ headIndex 1 r.arity) (u (aIdx r)) l) := rfl
    rw [h1, h2, graph_aperture r τ hu]
    rfl)

def sourceIso :
    Iso (coordinatePresentation r j hfin τ hr).sourceBounded.toChart (sourceBounded r hr).toChart :=
  RVCoordinateMaps.coordinateIso _ _ (headIndex 1 r.arity)
    (RVDefinableGraphExtension.projection_bijective r τ.aperture) (fun _ _ => rfl)

/-- Definition 7.2 and Notation 4.17: the class difference of an elementary
annular blowup is the Section 4 generator of `J_var`. -/
theorem blowup_relation :
    RVBoundedRing.objectClass (shellBounded r j hfin τ hr) +
        RVBoundedRing.objectClass (endpointBounded r j hfin τ hr) -
        RVBoundedRing.objectClass (sourceBounded r hr) =
      (presentation r j hfin τ hr).relation := by
  change _ = RVBoundedRing.objectClass (coordinatePresentation r j hfin τ hr).shell +
      RVBoundedRing.objectClass (coordinatePresentation r j hfin τ hr).endpointBounded -
      RVBoundedRing.objectClass (coordinatePresentation r j hfin τ hr).sourceBounded
  rw [RVBoundedRing.objectClass_iso (shellIso r j hfin τ hr),
    RVBoundedRing.objectClass_iso (endpointIso r j hfin τ hr),
    RVBoundedRing.objectClass_iso (sourceIso r j hfin τ hr)]

/-- The class difference of an elementary annular blowup lies in `J_var`. -/
theorem blowup_mem_ideal :
    RVBoundedRing.objectClass (shellBounded r j hfin τ hr) +
        RVBoundedRing.objectClass (endpointBounded r j hfin τ hr) -
        RVBoundedRing.objectClass (sourceBounded r hr) ∈ FunctionalApertureCompatibility.ideal B := by
  rw [blowup_relation]
  exact Ideal.subset_span ⟨k, presentation r j hfin τ hr, rfl⟩

/-! Normalization of the blown-up coordinate: `U ≅ W × (1, 0)`. -/

/-- The structural unit point of degree one. -/
def unitPoint : Chart B 1 :=
  RVPointChoices.pointChart B RVRadiusGenerators.oneCode (RVRadiusGenerators.oneCode_definable B)

/-- `W × (1, 0)`: coordinate `j` of `U` replaced by the structural unit. -/
def normalized : Chart B (1 + k) := RVMeasuredProduct.product (baseChart r j hfin) unitPoint

theorem normalized_weight (u : Fin (1 + r.arity) → M) (hu : u ∈ (normalized r j hfin).domain) :
    (normalized r j hfin).correctedWeight u = r.correctedWeight (u ∘ headIndex 1 r.arity) := by
  unfold normalized
  rw [RVPointProductIsomorphisms.product_weight_coordinates]
  have h1 := RVPointChoices.pointChart_weight B RVRadiusGenerators.oneCode
    (RVRadiusGenerators.oneCode_definable B) ⟨u ∘ tailIndex 1 r.arity, hu.2⟩
  change (baseChart r j hfin).correctedWeight (u ∘ headIndex 1 r.arity) *
      unitPoint.correctedWeight (u ∘ tailIndex 1 r.arity) = _
  rw [show unitPoint.correctedWeight (u ∘ tailIndex 1 r.arity) = 1 from
    h1.trans RVRadiusGenerators.oneCode_value, mul_one, baseChart_weight]

/-- The normalization isomorphism `W × (1, 0) ≅ U`, by projection. -/
def normalizeIso : Iso (normalized r j hfin) r :=
  RVCoordinateMaps.coordinateIso (normalized r j hfin) r (headIndex 1 r.arity)
    (by
      refine ⟨fun u hu => hu.1, ?_, ?_⟩
      · intro u hu v hv he
        have hut : u ∘ tailIndex 1 r.arity = v ∘ tailIndex 1 r.arity := by
          have h1 : u ∘ tailIndex 1 r.arity = ![GammaParameters.raw RVRadiusGenerators.oneCode] := hu.2
          have h2 : v ∘ tailIndex 1 r.arity = ![GammaParameters.raw RVRadiusGenerators.oneCode] := hv.2
          rw [h1, h2]
        rw [← join_reconstruct 1 r.arity u, ← join_reconstruct 1 r.arity v]
        have he' : u ∘ headIndex 1 r.arity = v ∘ headIndex 1 r.arity := he
        rw [he', hut]
      · intro x hx
        refine ⟨join 1 r.arity x ![GammaParameters.raw RVRadiusGenerators.oneCode], ⟨?_, ?_⟩, ?_⟩
        · have : (join 1 r.arity x ![GammaParameters.raw RVRadiusGenerators.oneCode]) ∘ headIndex 1 r.arity = x :=
            funext (fun i => join_head 1 r.arity x _ i)
          change (join 1 r.arity x _) ∘ headIndex 1 r.arity ∈ r.domain
          rw [this]
          exact hx
        · change (join 1 r.arity x ![GammaParameters.raw RVRadiusGenerators.oneCode]) ∘ tailIndex 1 r.arity ∈
            ({![GammaParameters.raw RVRadiusGenerators.oneCode]} : Set (Fin 1 → M))
          funext i
          fin_cases i
          simp only [Function.comp_apply, join_tail]
        · exact funext (fun i => join_head 1 r.arity x _ i))
    (fun u hu => normalized_weight r j hfin u hu)

end DiamondIntegral.Section4.BlowupRelation
