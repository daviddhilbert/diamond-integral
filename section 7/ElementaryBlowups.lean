import «section 7».BoundedClasses
import «section 4».RelativeAnnularGenerators

/-! Definition 7.2 (`defn:blowup:coa`): elementary annular blowups with bounded
variable apertures, blowups of length one and finite blowup chains, on
isomorphism classes of `μRV^db[k]`.

The data of an elementary blowup are Section 4's `AnnularDatum`: a bounded chart
`U = (U, f, ω)` of degree `1+k`, a coordinate `j` with `pr_{~j} ↾ f(U)`
finite-to-one, and an aperture `τ` (an original-base definable nonzero RV
function on `U` with `0 ≤ vrv τ ≤ Δ`). Its blowup is the separately tagged union
of the shell `{(u,s) : 0 < vrv s ≤ vrv τ(u)}` and the endpoint graph
`{(u, τ(u))}`, which is literally the relative annular object `U^{τ,j}` of
Notation 4.17 (`AnnularDatum.annularObject`).

A blowup of length one of `V` via morphisms `F_i : U_i → C_i` onto disjoint
subobjects is `(V ∖ C) ⊎ ⊎ U_i^♭`. By the paper's own remark after
Corollary 7.8 these are relations on isomorphism classes; on classes, a length-one
blowup replaces summands `[U_i]` of `[V]` by `[U_i^♭]` (`Step`). The object-level
definition with literal disjoint subobjects is `Blowup`, and `Blowup.step` shows
it gives `Step`.

The main technical result here is restriction (`AnnularDatum.res`): an aperture
datum restricts to every definable piece of its source, and the blowup splits
accordingly (`cls_annular_split`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section4
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions FiniteTupleBlocks
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-! ### Restricting apertures and data to definable pieces -/

omit hM in
theorem graphOn_diff {m n : ℕ} (I J : Set (Fin m → M)) (F : (Fin m → M) → (Fin n → M)) :
    graphOn (I \ J) F = graphOn I F ∩ {w | w ∘ headIndex n m ∉ J} := by
  ext w
  exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩

theorem graph_diff_definable {m n : ℕ} (I J : Set (Fin m → M)) (F : (Fin m → M) → (Fin n → M))
    (hG : DefinableOverBase B (fun _ : Fin (n + m) => .rv) (graphOn I F))
    (hJ : DefinableOverBase B (fun _ : Fin m => .rv) J) :
    DefinableOverBase B (fun _ : Fin (n + m) => .rv) (graphOn (I \ J) F) := by
  have hP := hJ.preimage_real (fun _ : Fin (n + m) => .rv) (headIndex n m)
  have h := hG.inter hP.compl
  convert h using 1
  ext w
  constructor
  · intro hw
    have hg : w ∈ graphOn I F := ⟨hw.1.1, hw.2⟩
    exact ⟨hg, hG.proper w hg, fun hp => hw.1.2 hp.1⟩
  · intro hw
    exact ⟨⟨hw.1.1, fun hj => hw.2.2 ⟨hj, hw.2.1⟩⟩, hw.1.2⟩

/-- The restriction of a chart to a definable piece. -/
abbrev resChart (r : Chart B k) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) : Chart B k :=
  (inside (ofChart r) I hI).toChart

/-- The restriction of a chart to the complement of a definable piece. -/
abbrev cresChart (r : Chart B k) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) : Chart B k :=
  (outside (ofChart r) I hI).toChart

/-- An aperture restricts to a definable piece. -/
def apRes {r : Chart B k} (τ : Aperture r) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) : Aperture (resChart r I hI) where
  aperture := τ.aperture
  graph_definable := graph_inter_definable r.domain I (fun u => ![τ.aperture u]) τ.graph_definable hI
  nonzero := fun u hu => τ.nonzero u hu.1
  nonnegative := fun u hu => τ.nonnegative u hu.1
  bound := τ.bound
  bounded := fun u hu => τ.bounded u hu.1

/-- An aperture restricts to the complement of a definable piece. -/
def apCres {r : Chart B k} (τ : Aperture r) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) : Aperture (cresChart r I hI) where
  aperture := τ.aperture
  graph_definable := graph_diff_definable r.domain I (fun u => ![τ.aperture u]) τ.graph_definable hI
  nonzero := fun u hu => τ.nonzero u hu.1
  nonnegative := fun u hu => τ.nonnegative u hu.1
  bound := τ.bound
  bounded := fun u hu => τ.bounded u hu.1

theorem inactiveFinite_res {r : Chart B k} {j : Fin k} (h : InactiveFinite r j)
    (I : Set (Fin r.arity → M)) (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    InactiveFinite (resChart r I hI) j :=
  fun t => (h t).subset (fun _ hu => ⟨hu.1.1, hu.2⟩)

theorem inactiveFinite_cres {r : Chart B k} {j : Fin k} (h : InactiveFinite r j)
    (I : Set (Fin r.arity → M)) (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    InactiveFinite (cresChart r I hI) j :=
  fun t => (h t).subset (fun _ hu => ⟨hu.1.1, hu.2⟩)

/-- An aperture datum restricted to a definable piece of its source. -/
def datumRes (D : AnnularDatum B k) (I : Set (Fin D.chart.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin D.chart.arity => .rv) I) : AnnularDatum B k where
  chart := resChart D.chart I hI
  coordinate := D.coordinate
  finite := inactiveFinite_res D.finite I hI
  aperture := apRes D.aperture I hI
  bounded := restrict_domain_bounded _ _ _ _ D.bounded

/-- An aperture datum restricted to the complement of a definable piece. -/
def datumCres (D : AnnularDatum B k) (I : Set (Fin D.chart.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin D.chart.arity => .rv) I) : AnnularDatum B k where
  chart := cresChart D.chart I hI
  coordinate := D.coordinate
  finite := inactiveFinite_cres D.finite I hI
  aperture := apCres D.aperture I hI
  bounded := restrict_domain_bounded _ _ _ _ D.bounded

theorem res_source (D : AnnularDatum B k) (I : Set (Fin D.chart.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin D.chart.arity => .rv) I) :
    cls (datumRes D I hI).source = cls (piece D.source I hI) := rfl

theorem cres_source (D : AnnularDatum B k) (I : Set (Fin D.chart.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin D.chart.arity => .rv) I) :
    cls (datumCres D I hI).source = cls (cpiece D.source I hI) := rfl

/-! ### The shell and endpoint pieces over a restriction -/

theorem shell_iff (r : Chart B k) (τ : Aperture r) (w : Fin (1 + (1 + r.arity)) → M) :
    w ∈ shellDomain r τ ↔
      w ∘ headIndex 1 (1 + r.arity) ∈ (graphChart r τ).domain ∧ Proper (w ∘ tailIndex 1 (1 + r.arity)) ∧
        1 < codeValue (w (sIdx r)) ∧
          codeValue (w (sIdx r)) ≤ codeValue ((w ∘ headIndex 1 (1 + r.arity)) (aIdx r)) := by
  have h := VariableApertureRayCancellation.annularChart_join_iff (graphChart r τ) (aIdx r)
    (graph_aperture_nonzero r τ) (w ∘ headIndex 1 (1 + r.arity)) (w ∘ tailIndex 1 (1 + r.arity))
  rw [show join 1 (graphChart r τ).arity (w ∘ headIndex 1 (1 + r.arity)) (w ∘ tailIndex 1 (1 + r.arity)) = w
    from join_reconstruct 1 (1 + r.arity) w] at h
  exact h

theorem graphChart_domain (r : Chart B k) (τ : Aperture r) :
    (graphChart r τ).domain = graphOn r.domain (fun u => ![τ.aperture u]) := rfl

/-- The definable set of shell points whose base point lies in `I`. -/
def shellCut (r : Chart B k) (I : Set (Fin r.arity → M)) : Set (Fin (1 + (1 + r.arity)) → M) :=
  {w | w ∘ xIdx r ∈ I ∧ w ∈ sortedUniverse (fun _ : Fin (1 + (1 + r.arity)) => .rv)}

theorem shellCut_definable (r : Chart B k) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    DefinableOverBase B (fun _ : Fin (1 + (1 + r.arity)) => .rv) (shellCut r I) :=
  hI.preimage_real (fun _ : Fin (1 + (1 + r.arity)) => .rv) (xIdx r)

/-- The definable set of endpoint points whose base point lies in `I`. -/
def endCut (r : Chart B k) (I : Set (Fin r.arity → M)) : Set (Fin (1 + r.arity) → M) :=
  {w | w ∘ headIndex 1 r.arity ∈ I ∧ w ∈ sortedUniverse (fun _ : Fin (1 + r.arity) => .rv)}

theorem endCut_definable (r : Chart B k) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (endCut r I) :=
  hI.preimage_real (fun _ : Fin (1 + r.arity) => .rv) (headIndex 1 r.arity)

theorem shell_sorted (r : Chart B k) (τ : Aperture r) {w : Fin (1 + (1 + r.arity)) → M}
    (hw : w ∈ shellDomain r τ) : w ∈ sortedUniverse (fun _ : Fin (1 + (1 + r.arity)) => .rv) :=
  (VariableApertureRayCancellation.annularChart (graphChart r τ) (aIdx r)).domain_definable.proper w hw

theorem graph_sorted (r : Chart B k) (τ : Aperture r) {w : Fin (1 + r.arity) → M}
    (hw : w ∈ (graphChart r τ).domain) : w ∈ sortedUniverse (fun _ : Fin (1 + r.arity) => .rv) :=
  (graphChart r τ).domain_definable.proper w hw

theorem xIdx_eq (r : Chart B k) (w : Fin (1 + (1 + r.arity)) → M) :
    w ∘ xIdx r = (w ∘ headIndex 1 (1 + r.arity)) ∘ headIndex 1 r.arity := rfl

theorem shellDomain_res (r : Chart B k) (τ : Aperture r) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    shellDomain (resChart r I hI) (apRes τ I hI) = shellDomain r τ ∩ shellCut r I := by
  apply Set.ext
  intro w
  rw [Set.mem_inter_iff, shell_iff, shell_iff]
  constructor
  · rintro ⟨⟨⟨hd, hi⟩, he⟩, hp, h1, h2⟩
    have hw : w ∈ shellDomain r τ := (shell_iff r τ w).mpr ⟨⟨hd, he⟩, hp, h1, h2⟩
    exact ⟨⟨⟨hd, he⟩, hp, h1, h2⟩, hi, shell_sorted r τ hw⟩
  · rintro ⟨⟨⟨hd, he⟩, hp, h1, h2⟩, hi, _⟩
    exact ⟨⟨⟨hd, hi⟩, he⟩, hp, h1, h2⟩

theorem shellDomain_cres (r : Chart B k) (τ : Aperture r) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    shellDomain (cresChart r I hI) (apCres τ I hI) = shellDomain r τ \ shellCut r I := by
  apply Set.ext
  intro w
  rw [Set.mem_sdiff, shell_iff, shell_iff]
  constructor
  · rintro ⟨⟨⟨hd, hi⟩, he⟩, hp, h1, h2⟩
    exact ⟨⟨⟨hd, he⟩, hp, h1, h2⟩, fun hc => hi hc.1⟩
  · rintro ⟨⟨⟨hd, he⟩, hp, h1, h2⟩, hc⟩
    have hw : w ∈ shellDomain r τ := (shell_iff r τ w).mpr ⟨⟨hd, he⟩, hp, h1, h2⟩
    exact ⟨⟨⟨hd, fun hi => hc ⟨hi, shell_sorted r τ hw⟩⟩, he⟩, hp, h1, h2⟩

theorem graphDomain_res (r : Chart B k) (τ : Aperture r) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    (graphChart (resChart r I hI) (apRes τ I hI)).domain = (graphChart r τ).domain ∩ endCut r I := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hd, hi⟩, he⟩
    have hw : w ∈ (graphChart r τ).domain := ⟨hd, he⟩
    exact ⟨hw, hi, graph_sorted r τ hw⟩
  · rintro ⟨⟨hd, he⟩, hi, _⟩
    exact ⟨⟨hd, hi⟩, he⟩

theorem graphDomain_cres (r : Chart B k) (τ : Aperture r) (I : Set (Fin r.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin r.arity => .rv) I) :
    (graphChart (cresChart r I hI) (apCres τ I hI)).domain = (graphChart r τ).domain \ endCut r I := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hd, hi⟩, he⟩
    exact ⟨⟨hd, he⟩, fun hc => hi hc.1⟩
  · rintro ⟨⟨hd, he⟩, hc⟩
    have hw : w ∈ (graphChart r τ).domain := ⟨hd, he⟩
    exact ⟨⟨hd, fun hi => hc ⟨hi, graph_sorted r τ hw⟩⟩, he⟩

section Split
variable (D : AnnularDatum B k) (I : Set (Fin D.chart.arity → M))
  (hI : DefinableOverBase B (fun _ : Fin D.chart.arity => .rv) I)

/-- The shell piece of `D` over `I` is the shell of the restricted datum. -/
theorem cls_shell_res :
    cls (piece (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)
        (shellCut D.chart I) (shellCut_definable D.chart I hI)) =
      cls (shellBounded (datumRes D I hI).chart (datumRes D I hI).coordinate (datumRes D I hI).finite
        (datumRes D I hI).aperture (datumRes D I hI).bounded) :=
  cls_eq_of_iso (sameIso _ (ofChart (shellChart (datumRes D I hI).chart D.coordinate (datumRes D I hI).finite
      (datumRes D I hI).aperture))
    (shellDomain_res D.chart D.aperture I hI).symm (fun _ _ => rfl) (fun _ _ => rfl))

theorem cls_shell_cres :
    cls (cpiece (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)
        (shellCut D.chart I) (shellCut_definable D.chart I hI)) =
      cls (shellBounded (datumCres D I hI).chart (datumCres D I hI).coordinate (datumCres D I hI).finite
        (datumCres D I hI).aperture (datumCres D I hI).bounded) :=
  cls_eq_of_iso (sameIso _ (ofChart (shellChart (datumCres D I hI).chart D.coordinate (datumCres D I hI).finite
      (datumCres D I hI).aperture))
    (shellDomain_cres D.chart D.aperture I hI).symm (fun _ _ => rfl) (fun _ _ => rfl))

theorem cls_endpoint_res :
    cls (piece (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded)
        (endCut D.chart I) (endCut_definable D.chart I hI)) =
      cls (endpointBounded (datumRes D I hI).chart (datumRes D I hI).coordinate (datumRes D I hI).finite
        (datumRes D I hI).aperture (datumRes D I hI).bounded) :=
  cls_eq_of_iso (sameIso _ (ofChart (endpointChart (datumRes D I hI).chart D.coordinate (datumRes D I hI).finite
      (datumRes D I hI).aperture))
    (graphDomain_res D.chart D.aperture I hI).symm (fun _ _ => rfl) (fun _ _ => rfl))

theorem cls_endpoint_cres :
    cls (cpiece (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded)
        (endCut D.chart I) (endCut_definable D.chart I hI)) =
      cls (endpointBounded (datumCres D I hI).chart (datumCres D I hI).coordinate (datumCres D I hI).finite
        (datumCres D I hI).aperture (datumCres D I hI).bounded) :=
  cls_eq_of_iso (sameIso _ (ofChart (endpointChart (datumCres D I hI).chart D.coordinate (datumCres D I hI).finite
      (datumCres D I hI).aperture))
    (graphDomain_cres D.chart D.aperture I hI).symm (fun _ _ => rfl) (fun _ _ => rfl))

theorem cls_annular (D : AnnularDatum B k) :
    cls D.annularObject =
      cls (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded) +
        cls (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded) := rfl

/-- The blowup splits along a definable piece of the source. -/
theorem cls_annular_split :
    cls D.annularObject = cls (datumRes D I hI).annularObject + cls (datumCres D I hI).annularObject := by
  rw [cls_annular, cls_annular, cls_annular,
    cls_partition (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)
      (shellCut D.chart I) (shellCut_definable D.chart I hI),
    cls_partition (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded)
      (endCut D.chart I) (endCut_definable D.chart I hI),
    cls_shell_res D I hI, cls_shell_cres D I hI, cls_endpoint_res D I hI, cls_endpoint_cres D I hI]
  abel

end Split

/-! ### Decomposing data along class decompositions -/

/-- If the source is zero then so is the blowup. -/
theorem cls_annular_eq_zero (D : AnnularDatum B k) (h : cls D.source = 0) : cls D.annularObject = 0 := by
  have hD : D.chart.domain = ∅ := (cls_eq_zero_iff D.source).mp h
  have hs : cls (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded) = 0 := by
    apply (cls_eq_zero_iff _).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hx := (shell_points D.chart D.aperture hw).1
    rw [hD] at hx
    exact hx
  have he : cls (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded) = 0 := by
    apply (cls_eq_zero_iff _).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hx := hw.1
    rw [hD] at hx
    exact hx
  rw [cls_annular, hs, he, add_zero]

/-- A datum splits along a two-term class decomposition of its source. -/
theorem datum_split (D : AnnularDatum B k) (p q : Cls B (1 + k)) (h : cls D.source = p + q) :
    ∃ D₁ D₂ : AnnularDatum B k, cls D₁.source = p ∧ cls D₂.source = q ∧
      cls D.annularObject = cls D₁.annularObject + cls D₂.annularObject := by
  obtain ⟨I, hI, h1, h2⟩ := exists_split D.source p q h
  exact ⟨datumRes D I hI, datumCres D I hI, h1, h2, cls_annular_split D I hI⟩

/-- A datum splits along a finite class decomposition of its source. -/
theorem datum_split_fin (D : AnnularDatum B k) :
    ∀ (m : ℕ) (p : Fin m → Cls B (1 + k)), cls D.source = ∑ j, p j →
      ∃ E : Fin m → AnnularDatum B k, (∀ j, cls (E j).source = p j) ∧
        ∑ j, cls (E j).annularObject = cls D.annularObject := by
  intro m
  induction m generalizing D with
  | zero =>
    intro p h
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    exact ⟨Fin.elim0, fun j => j.elim0, (cls_annular_eq_zero D h).symm⟩
  | succ m ih =>
    intro p h
    rw [Fin.sum_univ_succ] at h
    obtain ⟨D₁, D₂, h1, h2, h3⟩ := datum_split D _ _ h
    obtain ⟨E, hE, hs⟩ := ih D₂ (fun j => p j.succ) h2
    refine ⟨Fin.cons D₁ E, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using h1
      · simpa using hE j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hs, h3]

/-! ### Blowups of length one on classes -/

/-- An elementary annular blowup on classes: `y = [U^{τ,j}]` for an aperture
datum on an object of class `x`. -/
def ElementaryStep (x y : Cls B (1 + k)) : Prop :=
  ∃ D : AnnularDatum B k, x = cls D.source ∧ y = cls D.annularObject

/-- A blowup of length one on classes (Definition 7.2): finitely many disjoint
summands of `x` are replaced by elementary blowups. Empty loci are allowed. -/
def Step (x y : Cls B (1 + k)) : Prop :=
  ∃ (n : ℕ) (D : Fin n → AnnularDatum B k) (z : Cls B (1 + k)),
    x = z + ∑ i, cls (D i).source ∧ y = z + ∑ i, cls (D i).annularObject

theorem step_refl (x : Cls B (1 + k)) : Step x x :=
  ⟨0, Fin.elim0, x, by simp, by simp⟩

theorem step_of_elementary {x y : Cls B (1 + k)} (h : ElementaryStep x y) : Step x y := by
  obtain ⟨D, rfl, rfl⟩ := h
  exact ⟨1, fun _ => D, 0, by simp, by simp⟩

theorem step_elem (D : AnnularDatum B k) : Step (cls D.source) (cls D.annularObject) :=
  step_of_elementary ⟨D, rfl, rfl⟩

theorem step_add {x y x' y' : Cls B (1 + k)} (h : Step x y) (h' : Step x' y') :
    Step (x + x') (y + y') := by
  obtain ⟨n, D, z, rfl, rfl⟩ := h
  obtain ⟨n', D', z', rfl, rfl⟩ := h'
  refine ⟨n + n', Fin.append D D', z + z', ?_, ?_⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    abel
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    abel

theorem step_add_left (w : Cls B (1 + k)) {x y : Cls B (1 + k)} (h : Step x y) :
    Step (w + x) (w + y) := step_add (step_refl w) h

theorem step_sum : ∀ {m : ℕ} (x y : Fin m → Cls B (1 + k)), (∀ i, Step (x i) (y i)) →
    Step (∑ i, x i) (∑ i, y i)
  | 0, _, _, _ => by simpa using step_refl (0 : Cls B (1 + k))
  | m + 1, x, y, h => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact step_add (h 0) (step_sum (fun i => x i.succ) (fun i => y i.succ) (fun i => h i.succ))

/-- An elementary blowup of any summand of a sum of data sources. -/
theorem step_of_data {n : ℕ} (D : Fin n → AnnularDatum B k) (z : Cls B (1 + k)) :
    Step (z + ∑ i, cls (D i).source) (z + ∑ i, cls (D i).annularObject) :=
  ⟨n, D, z, rfl, rfl⟩

/-! ### From the elementary comparison (Lemma 7.5) to the diamond (Corollary 7.6) -/

/-- The conclusion of Lemma 7.5 on classes: elementary blowups of isomorphic
objects, in possibly different coordinates, have blowups of length one with a
common class. -/
def ElementaryDiamond (B : Base (M := M)) (k : ℕ) : Prop :=
  ∀ D E : AnnularDatum B k, cls D.source = cls E.source →
    ∃ w : Cls B (1 + k), Step (cls D.annularObject) w ∧ Step (cls E.annularObject) w

theorem step_congr {x x' y y' : Cls B (1 + k)} (hx : x = x') (hy : y = y') (h : Step x y) :
    Step x' y' := hx ▸ hy ▸ h

/-- Corollary 7.6 (`eblowup:same:loci:iso`) on classes, from Lemma 7.5: two
blowups of length one of the same class have blowups of length one with a common
class. The loci are refined by matrix refinement in the class monoid. -/
theorem step_diamond (hE : ElementaryDiamond B k) {x y y' : Cls B (1 + k)}
    (h₁ : Step x y) (h₂ : Step x y') : ∃ w, Step y w ∧ Step y' w := by
  obtain ⟨n, D, z, hx, hy⟩ := h₁
  obtain ⟨m, E, z', hx', hy'⟩ := h₂
  let a : Fin (n + 1) → Cls B (1 + k) := Fin.cons z (fun i => cls (D i).source)
  let b : Fin (m + 1) → Cls B (1 + k) := Fin.cons z' (fun j => cls (E j).source)
  have hab : ∑ i, a i = ∑ j, b j := by
    simp only [a, b, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← hx, ← hx']
  obtain ⟨c, hrow, hcol⟩ := Refinement.refine_matrix (refine2 (B := B) (k := 1 + k))
    (eq_zero_of_add_eq_zero (B := B) (k := 1 + k)) (n + 1) (m + 1) a b hab
  have hrow' : ∀ i : Fin n, cls (D i).source = ∑ j, c i.succ j := fun i => by
    have := hrow i.succ
    simp only [a, Fin.cons_succ] at this
    exact this.symm
  have hcol' : ∀ j : Fin m, cls (E j).source = ∑ i, c i j.succ := fun j => by
    have := hcol j.succ
    simp only [b, Fin.cons_succ] at this
    exact this.symm
  choose Dsp hDsp hDann using fun i => datum_split_fin (D i) (m + 1) (c i.succ) (hrow' i)
  choose Esp hEsp hEann using fun j => datum_split_fin (E j) (n + 1) (fun i => c i j.succ) (hcol' j)
  have hsrc : ∀ (i : Fin n) (j : Fin m), cls (Dsp i j.succ).source = cls (Esp j i.succ).source :=
    fun i j => (hDsp i j.succ).trans (hEsp j i.succ).symm
  choose w hwD hwE using fun i j => hE (Dsp i j.succ) (Esp j i.succ) (hsrc i j)
  have hz : z = c 0 0 + ∑ j : Fin m, c 0 j.succ := by
    have := hrow 0
    simp only [a, Fin.cons_zero, Fin.sum_univ_succ] at this
    exact this.symm
  have hz' : z' = c 0 0 + ∑ i : Fin n, c i.succ 0 := by
    have := hcol 0
    simp only [b, Fin.cons_zero, Fin.sum_univ_succ] at this
    exact this.symm
  refine ⟨c 0 0 + ∑ j, cls (Esp j 0).annularObject + ∑ i, cls (Dsp i 0).annularObject +
    ∑ i, ∑ j, w i j, ?_, ?_⟩
  · -- `y`: blow up the summands of `z` met by the second loci, and the common pieces.
    have hy2 : y = c 0 0 + ∑ j : Fin m, c 0 j.succ + ∑ i, cls (Dsp i 0).annularObject +
        ∑ i, ∑ j : Fin m, cls (Dsp i j.succ).annularObject := by
      rw [hy, hz]
      simp only [← hDann, Fin.sum_univ_succ, Finset.sum_add_distrib]
      abel
    rw [hy2]
    refine step_add (step_add (step_add (step_refl _) ?_) (step_refl _)) ?_
    · exact step_sum _ _ fun j => step_congr (hEsp j 0) rfl (step_elem (Esp j 0))
    · exact step_sum _ _ fun i => step_sum _ _ fun j => hwD i j
  · -- `y'`: symmetrically.
    have hy2 : y' = c 0 0 + ∑ i : Fin n, c i.succ 0 + ∑ j, cls (Esp j 0).annularObject +
        ∑ j, ∑ i : Fin n, cls (Esp j i.succ).annularObject := by
      rw [hy', hz']
      simp only [← hEann, Fin.sum_univ_succ, Finset.sum_add_distrib]
      abel
    have hw2 : c 0 0 + ∑ j, cls (Esp j 0).annularObject + ∑ i, cls (Dsp i 0).annularObject +
        ∑ i, ∑ j, w i j =
        c 0 0 + ∑ i, cls (Dsp i 0).annularObject + ∑ j, cls (Esp j 0).annularObject +
          ∑ j, ∑ i, w i j := by
      rw [Finset.sum_comm (f := fun i j => w i j)]
      abel
    rw [hy2, hw2]
    refine step_add (step_add (step_add (step_refl _) ?_) (step_refl _)) ?_
    · exact step_sum _ _ fun i => step_congr (hDsp i 0) rfl (step_elem (Dsp i 0))
    · exact step_sum _ _ fun j => step_sum _ _ fun i => hwE i j

end DiamondIntegral.Section7.ElementaryBlowups
