import «section 7».Lemma714Indexed

/-! Lemma 7.14, part 12: descent of witness schemata over RV keys.

Step 3 of the proof ("descent"). Let `Q` be a `B`-definable key set whose keys,
rows and apertures are uniformly bounded (`KeySet.Bounds`; these bounds come
from Lemma 2.41 on a doubly bounded key set). Then:

* every chart schema valid at all keys realizes as a bounded object over `B`
  (`indObj`), and an isomorphism schema valid at all keys gives equal classes
  (`cls_indObj_iso`);
* a move schema valid at all keys gives a single-datum blowup over `B`
  (`step1_ind`), with the indexed aperture datum `indDatumK`;
* hence a witness schema valid at all keys gives `μIsp^db` over `B`
  (`muIsp_ind`), and in degree `0` equal classes (`cls_ind0`);
* if finitely many witness schemata cover the keys, the key set is cut by the
  first valid schema, and the pieces are added by `muIsp_add`
  (`muIsp_ind_cover`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.Iteration
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open RVChartDisjointUnion RVChartRestrictions

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {q : ℕ}

namespace KeySet
variable (Q : KeySet B q)

/-- Uniform bounds on a key set: on the keys, on the rows of every chart
schema valid at all keys, and on the apertures of every datum schema valid at
all keys. -/
structure Bounds : Prop where
  keys : ∃ β : Values.Gamma (M := M), ∀ x ∈ Q.carrier, ∀ i, NonzeroRV (x i) →
    β⁻¹ ≤ codeValue (x i) ∧ codeValue (x i) ≤ β
  rows : ∀ {d : ℕ} (W : ChartSchema B (rvs q) d), (∀ x ∈ Q.carrier, W.Valid x) →
    ∃ β : Values.Gamma (M := M), ∀ x ∈ Q.carrier, ∀ u ∈ W.row x, ∀ i, NonzeroRV (u i) →
      β⁻¹ ≤ codeValue (u i) ∧ codeValue (u i) ≤ β
  apertures : ∀ {k : ℕ} (D : DatumSchema B (rvs q) k), (∀ x ∈ Q.carrier, D.Valid x) →
    ∃ Δ : Values.Gamma (M := M), ∀ x ∈ Q.carrier, ∀ u t, D.apRow x u t → codeValue t ≤ Δ

variable {Q}

theorem indChart_domainBounded (hK : Q.Bounds) {d : ℕ} {W : ChartSchema B (rvs q) d}
    (hW : ∀ x ∈ Q.carrier, W.Valid x) : RVMeasuredBounds.DomainBounded (Q.indChart W hW) := by
  obtain ⟨β₁, h₁⟩ := hK.keys
  obtain ⟨β₂, h₂⟩ := hK.rows W hW
  have key : ∀ β : Values.Gamma (M := M), β ≤ max β₁ β₂ → ∀ c : Values.Gamma (M := M),
      β⁻¹ ≤ c ∧ c ≤ β → (max β₁ β₂)⁻¹ ≤ c ∧ c ≤ max β₁ β₂ :=
    fun β hβ c hc => ⟨(inv_le_inv_iff.mpr hβ).trans hc.1, hc.2.trans hβ⟩
  refine ⟨max β₁ β₂, fun w hw i => ?_⟩
  have hw' : w ∈ Q.indDom W := hw
  refine Fin.addCases (fun l hi => ?_) (fun l hi => ?_) i
  · exact key β₁ (le_max_left _ _) _ (h₁ _ (Q.indDom_key hw') l hi)
  · exact key β₂ (le_max_right _ _) _ (h₂ _ (Q.indDom_key hw') _ (Q.indDom_row hw') l hi)

variable (Q) in
/-- **The indexed object** of a chart schema valid at all keys. -/
def indObj (hK : Q.Bounds) {d : ℕ} (W : ChartSchema B (rvs q) d) (hW : ∀ x ∈ Q.carrier, W.Valid x) :
    Obj B (1 + d) :=
  ⟨Q.indChart W hW, indChart_domainBounded hK hW⟩

variable (hK : Q.Bounds)

theorem cls_indObj_iso {d : ℕ} {X Y : ChartSchema B (rvs q) d} (hX : ∀ x ∈ Q.carrier, X.Valid x)
    (hY : ∀ x ∈ Q.carrier, Y.Valid x) (Φ : IsoSchema X Y) (hΦ : ∀ x ∈ Q.carrier, Φ.Valid x) :
    cls (Q.indObj hK X hX) = cls (Q.indObj hK Y hY) :=
  cls_eq_of_iso (Q.indIso hX hY Φ hΦ)

/-! ### Restrictions and pieces -/

section Pieces
variable {d : ℕ} {X : ChartSchema B (rvs q) d} (hX : ∀ x ∈ Q.carrier, X.Valid x)

theorem indDom_sorted {w : Fin (q + X.arity) → M} (hw : w ∈ Q.indDom X) :
    w ∈ sortedUniverse (Fin.append (rvs q) (rvs X.arity)) :=
  X.domain_definable.proper w hw.2

theorem indDom_inter_compl (P : Set (Fin (q + X.arity) → M)) :
    Q.indDom X ∩ compl (Fin.append (rvs q) (rvs X.arity)) P = Q.indDom X \ P := by
  ext w
  constructor
  · rintro ⟨hw, -, hP⟩
    exact ⟨hw, hP⟩
  · rintro ⟨hw, hP⟩
    exact ⟨hw, indDom_sorted hw, hP⟩

/-- The indexed chart of a complementary restriction is the complementary piece
of the indexed chart, by the identity map. -/
def indRestrictComplIso {P : Set (Fin (q + X.arity) → M)}
    (hP : DefinableOverBase B (Fin.append (rvs q) (rvs X.arity)) P) :
    Iso (Q.indChart (X.restrict (compl _ P) hP.compl) (Q.indRestrict_valid hX hP.compl))
      (outside (ofChart (Q.indChart X hX)) P (definable_rvs_of_append hP)).toChart :=
  isoOfMap _ _ (fun w => w)
    (RVCoordinateMaps.coordinate_graph_definable B _ (Q.indDom_definable (X.restrict (compl _ P) hP.compl))
      (id : Fin (q + X.arity) → Fin (q + X.arity)))
    (by
      change Set.BijOn (fun w => w) (Q.indDom (X.restrict (compl _ P) hP.compl)) (Q.indDom X \ P)
      rw [indDom_restrict, indDom_inter_compl]
      exact Set.bijOn_id _)
    (by
      intro w hw
      change (Q.indChart (X.restrict (compl _ P) hP.compl) _).correctedWeight w = (Q.indChart X hX).correctedWeight w
      rw [indChart_weight, indChart_weight]
      congr 1
      apply ChartSchema.restrict_weightAt (hX _ (Q.indDom_key hw))
      exact Q.indDom_row hw)

/-- A definable piece splits the class of an indexed object into the classes of
the indexed restrictions. -/
theorem cls_indObj_split {P : Set (Fin (q + X.arity) → M)}
    (hP : DefinableOverBase B (Fin.append (rvs q) (rvs X.arity)) P) :
    cls (Q.indObj hK X hX) = cls (Q.indObj hK (X.restrict P hP) (Q.indRestrict_valid hX hP)) +
      cls (Q.indObj hK (X.restrict (compl _ P) hP.compl) (Q.indRestrict_valid hX hP.compl)) := by
  rw [cls_partition (Q.indObj hK X hX) P (definable_rvs_of_append hP)]
  congr 1
  · exact (cls_eq_of_iso (Q.indRestrictIso hX hP)).symm
  · exact (cls_eq_of_iso (Q.indRestrictComplIso hX hP)).symm

/-- Iterated restrictions with the same effective domain have the same class. -/
theorem cls_indObj_restrict2 {P P' P'' : Set (Fin (q + X.arity) → M)}
    (hP : DefinableOverBase B (Fin.append (rvs q) (rvs X.arity)) P)
    (hP' : DefinableOverBase B (Fin.append (rvs q) (rvs X.arity)) P')
    (hP'' : DefinableOverBase B (Fin.append (rvs q) (rvs X.arity)) P'')
    (h : ∀ w ∈ Q.indDom X, (w ∈ P ∧ w ∈ P') ↔ w ∈ P'') :
    cls (Q.indObj hK ((X.restrict P hP).restrict P' hP')
        (Q.indRestrict_valid (Q.indRestrict_valid hX hP) hP')) =
      cls (Q.indObj hK (X.restrict P'' hP'') (Q.indRestrict_valid hX hP'')) := by
  have hdom : Q.indDom ((X.restrict P hP).restrict P' hP') = Q.indDom (X.restrict P'' hP'') := by
    rw [indDom_restrict, indDom_restrict, indDom_restrict]
    ext w
    constructor
    · rintro ⟨⟨hw, h1⟩, h2⟩
      exact ⟨hw, (h w hw).mp ⟨h1, h2⟩⟩
    · rintro ⟨hw, h3⟩
      obtain ⟨h1, h2⟩ := (h w hw).mpr h3
      exact ⟨⟨hw, h1⟩, h2⟩
  apply cls_eq_of_iso
  refine isoOfMap _ _ (fun w => w)
    (RVCoordinateMaps.coordinate_graph_definable B _
      (Q.indDom_definable ((X.restrict P hP).restrict P' hP')) (id : Fin (q + X.arity) → Fin (q + X.arity)))
    (by
      change Set.BijOn (fun w => w) (Q.indDom ((X.restrict P hP).restrict P' hP')) (Q.indDom (X.restrict P'' hP''))
      rw [hdom]
      exact Set.bijOn_id _) ?_
  intro w hw
  have hw1 : w ∈ Q.indDom ((X.restrict P hP).restrict P' hP') := hw
  have hw2 : w ∈ Q.indDom (X.restrict P hP) := by
    rw [indDom_restrict] at hw1
    exact hw1.1
  have hw3 : w ∈ Q.indDom (X.restrict P'' hP'') := hdom ▸ hw1
  change (Q.indChart ((X.restrict P hP).restrict P' hP')
      (Q.indRestrict_valid (Q.indRestrict_valid hX hP) hP')).correctedWeight w =
    (Q.indChart (X.restrict P'' hP'') (Q.indRestrict_valid hX hP'')).correctedWeight w
  rw [indChart_weight, indChart_weight]
  congr 1
  rw [ChartSchema.restrict_weightAt ((hX _ (Q.indDom_key hw1)).restrict (P := P) (hP := hP)) (Q.indDom_row hw1),
    ChartSchema.restrict_weightAt (hX _ (Q.indDom_key hw1)) (Q.indDom_row hw2),
    ChartSchema.restrict_weightAt (hX _ (Q.indDom_key hw1)) (Q.indDom_row hw3)]

end Pieces

/-! ### The indexed aperture datum and its blowup -/

section Datum
open AnnularBlowup BlowupChart
variable {k : ℕ} {D : DatumSchema B (rvs q) k} (hD : ∀ x ∈ Q.carrier, D.Valid x)

/-- The indexed aperture datum, with the uniform bounds. -/
def indDatumK : RelativeAnnularGenerators.AnnularDatum B (1 + k) :=
  Q.indDatum hD (hK.apertures D hD) (indChart_domainBounded hK (Q.indDatum_chart_valid hD))

theorem cls_indDatumK_source :
    cls (Q.indDatumK hK hD).source = cls (Q.indObj hK D.chart (Q.indDatum_chart_valid hD)) := rfl

theorem cls_indDatumK_annular :
    cls (Q.indDatumK hK hD).annularObject =
      cls (Q.indObj hK D.shellSchema (Q.indShell_valid hD)) + cls (Q.indObj hK D.endSchema (Q.indEnd_valid hD)) := by
  refine (cls_coprod _ _).trans ?_
  congr 1
  · exact cls_eq_of_iso (Q.indShellIso hD (hK.apertures D hD) (indChart_domainBounded hK (Q.indDatum_chart_valid hD)))
  · exact cls_eq_of_iso (Q.indEndIso hD (hK.apertures D hD) (indChart_domainBounded hK (Q.indDatum_chart_valid hD)))

end Datum

/-! ### Moves, chains and witnesses -/

section Moves
variable {k : ℕ}

/-- **A move schema valid at all keys is a single-datum blowup over `B`.** -/
theorem step1_ind {X : ChartSchema B (rvs q) (1 + k)} (hX : ∀ x ∈ Q.carrier, X.Valid x) (μ : MoveSchema X)
    (hμ : ∀ x ∈ Q.carrier, μ.Valid x) :
    Lemma714Witness.Step1 (cls (Q.indObj hK X hX)) (cls (Q.indObj hK μ.result (fun x hx => (hμ x hx).result))) := by
  have hrest : ∀ x ∈ Q.carrier, μ.rest.Valid x := fun x hx => (hμ x hx).rest
  have hdat : ∀ x ∈ Q.carrier, μ.datum.Valid x := fun x hx => (hμ x hx).datum
  have hres : ∀ x ∈ Q.carrier, μ.result.Valid x := fun x hx => (hμ x hx).result
  refine ⟨Q.indDatumK hK hdat, cls (Q.indObj hK μ.rest hrest), ?_, ?_⟩
  · rw [Q.cls_indObj_split hK hX μ.piece_definable,
      Q.cls_indObj_iso hK _ hrest μ.isoRest (fun x hx => (hμ x hx).isoRest),
      Q.cls_indObj_iso hK _ (Q.indDatum_chart_valid hdat) μ.isoSrc (fun x hx => (hμ x hx).isoSrc)]
    rfl
  · have e3 := Q.cls_indObj_restrict2 hK hres μ.q₁_definable.compl μ.q₂_definable
      (μ.q₂_definable.sdiff μ.q₁_definable)
      (fun w hw => by
        constructor
        · rintro ⟨⟨-, h1⟩, h2⟩
          exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩
          exact ⟨⟨indDom_sorted hw, h1⟩, h2⟩)
    have e4 := Q.cls_indObj_restrict2 hK hres μ.q₁_definable.compl μ.q₂_definable.compl
      (μ.q₁_definable.union μ.q₂_definable).compl
      (fun w _ => by
        simp only [compl, Set.mem_diff, Set.mem_union, not_or]
        tauto)
    rw [Q.cls_indObj_split hK hres μ.q₁_definable,
      Q.cls_indObj_split hK (Q.indRestrict_valid hres μ.q₁_definable.compl) μ.q₂_definable, e3,
      Q.cls_indObj_iso hK _ hrest μ.isoRest' (fun x hx => (hμ x hx).isoRest'),
      Q.cls_indObj_iso hK _ (Q.indShell_valid hdat) μ.isoShell (fun x hx => (hμ x hx).isoShell),
      Q.cls_indDatumK_annular hK hdat]
    congr 2
    exact e4.trans (Q.cls_indObj_iso hK _ (Q.indEnd_valid hdat) μ.isoEnd (fun x hx => (hμ x hx).isoEnd))

/-- **A chain schema valid at all keys is a chain of single-datum blowups.** -/
theorem steps1_ind : {X : ChartSchema B (rvs q) (1 + k)} → {m : ℕ} → (c : ChainSchema X m) →
    (hX : ∀ x ∈ Q.carrier, X.Valid x) → (hc : ∀ x ∈ Q.carrier, c.Valid x) →
    Steps (Lemma714Witness.Step1 (B := B) (k := 1 + k)) m (cls (Q.indObj hK X hX))
      (cls (Q.indObj hK c.last (fun x hx => ChainSchema.Valid.last (hX x hx) c (hc x hx))))
  | _, _, .nil _, _, _ => .refl _
  | _, _, .cons μ tail, hX, hc =>
    .cons (Q.step1_ind hK hX μ (fun x hx => (hc x hx).1))
      (steps1_ind tail (fun x hx => (hc x hx).1.result) (fun x hx => (hc x hx).2))

/-- **A witness schema valid at all keys gives `μIsp^db` over `B`.** -/
theorem muIsp_ind {X₀ Y₀ : ChartSchema B (rvs q) (1 + k)} (W : WitnessSchema X₀ Y₀)
    (hW : ∀ x ∈ Q.carrier, W.Valid x) :
    MuIsp (cls (Q.indObj hK X₀ (fun x hx => (hW x hx).source)))
      (cls (Q.indObj hK Y₀ (fun x hx => (hW x hx).target))) := by
  rw [Lemma714Witness.muIsp_iff_common_step1]
  have h1 := Q.steps1_ind hK W.left (fun x hx => (hW x hx).source) (fun x hx => (hW x hx).left)
  have h2 := Q.steps1_ind hK W.right (fun x hx => (hW x hx).target) (fun x hx => (hW x hx).right)
  refine ⟨_, _, W.rightLength, h1, ?_⟩
  rw [Q.cls_indObj_iso hK _ _ W.final (fun x hx => (hW x hx).final)]
  exact h2

end Moves

/-- **A degree-0 witness schema valid at all keys gives equal classes.** -/
theorem cls_ind0 {X₀ Y₀ : ChartSchema B (rvs q) 0} (W : WitnessSchema0 X₀ Y₀)
    (hW : ∀ x ∈ Q.carrier, W.Valid x) :
    cls (Q.indObj hK X₀ (fun x hx => (hW x hx).source)) = cls (Q.indObj hK Y₀ (fun x hx => (hW x hx).target)) :=
  Q.cls_indObj_iso hK _ _ W.iso (fun x hx => (hW x hx).iso)

/-! ### Cutting the key set -/

variable (Q) in
/-- The keys in a definable set `R`. -/
def sub (R : Set (Fin q → M)) (hR : DefinableOverBase B (rvs q) R) : KeySet B q where
  carrier := Q.carrier ∩ R
  definable := Q.definable.inter hR
  idx := Q.idx
  nonzero := fun x hx => Q.nonzero x hx.1
  finite := fun c => (Q.finite c).subset (fun x hx => ⟨hx.1.1, hx.2⟩)

variable (Q) in
/-- Uniform bounds on every key set inside `Q` (Lemma 2.41 gives them on a
doubly bounded key set). -/
def AllBounds : Prop := ∀ Q' : KeySet B q, Q'.carrier ⊆ Q.carrier → Q'.Bounds

theorem AllBounds.bounds (hA : Q.AllBounds) : Q.Bounds := hA Q subset_rfl

theorem AllBounds.sub (hA : Q.AllBounds) (R : Set (Fin q → M)) (hR : DefinableOverBase B (rvs q) R) :
    (Q.sub R hR).AllBounds :=
  fun Q' hQ' => hA Q' (hQ'.trans Set.inter_subset_left)

section Cut
variable {d : ℕ} {X : ChartSchema B (rvs q) d} (hX : ∀ x ∈ Q.carrier, X.Valid x)
  {R : Set (Fin q → M)} (hR : DefinableOverBase B (rvs q) R)

/-- The indexed points whose key lies in `R`. -/
def keyPiece (R : Set (Fin q → M)) : Set (Fin (q + X.arity) → M) :=
  {w | w ∘ Fin.castAdd X.arity ∈ R ∧ w ∈ sortedUniverse (Fin.append (rvs q) (rvs X.arity))}

include hR in
theorem keyPiece_definable : DefinableOverBase B (fun _ : Fin (q + X.arity) => .rv) (keyPiece (X := X) R) :=
  definable_rvs_of_append (hR.preimage_real (Fin.append (rvs q) (rvs X.arity)) (Fin.castAdd X.arity))

theorem sub_indDom : (Q.sub R hR).indDom X = Q.indDom X ∩ keyPiece (X := X) R := by
  ext w
  constructor
  · rintro ⟨⟨hk, hr⟩, hw⟩
    exact ⟨⟨hk, hw⟩, hr, X.domain_definable.proper w hw⟩
  · rintro ⟨⟨hk, hw⟩, hr, -⟩
    exact ⟨⟨hk, hr⟩, hw⟩

theorem subCompl_indDom : (Q.sub (compl (rvs q) R) hR.compl).indDom X = Q.indDom X \ keyPiece (X := X) R := by
  ext w
  constructor
  · rintro ⟨⟨hk, -, hr⟩, hw⟩
    exact ⟨⟨hk, hw⟩, fun h => hr h.1⟩
  · rintro ⟨⟨hk, hw⟩, hr⟩
    exact ⟨⟨hk, Q.definable.proper _ hk, fun h => hr ⟨h, X.domain_definable.proper w hw⟩⟩, hw⟩

/-- The indexed chart over the keys in `R` is a piece of the indexed chart. -/
def subIso :
    Iso ((Q.sub R hR).indChart X (fun x hx => hX x hx.1))
      (inside (ofChart (Q.indChart X hX)) (keyPiece (X := X) R) (keyPiece_definable hR)).toChart :=
  isoOfMap _ _ (fun w => w)
    (RVCoordinateMaps.coordinate_graph_definable B _ ((Q.sub R hR).indDom_definable X)
      (id : Fin (q + X.arity) → Fin (q + X.arity)))
    (by
      change Set.BijOn (fun w => w) ((Q.sub R hR).indDom X) (Q.indDom X ∩ keyPiece (X := X) R)
      rw [sub_indDom]
      exact Set.bijOn_id _)
    (by
      intro w _
      change ((Q.sub R hR).indChart X (fun x hx => hX x hx.1)).correctedWeight w = (Q.indChart X hX).correctedWeight w
      rw [indChart_weight, indChart_weight]
      rfl)

/-- The indexed chart over the keys outside `R` is the complementary piece. -/
def subComplIso :
    Iso ((Q.sub (compl (rvs q) R) hR.compl).indChart X (fun x hx => hX x hx.1))
      (outside (ofChart (Q.indChart X hX)) (keyPiece (X := X) R) (keyPiece_definable hR)).toChart :=
  isoOfMap _ _ (fun w => w)
    (RVCoordinateMaps.coordinate_graph_definable B _ ((Q.sub (compl (rvs q) R) hR.compl).indDom_definable X)
      (id : Fin (q + X.arity) → Fin (q + X.arity)))
    (by
      change Set.BijOn (fun w => w) ((Q.sub (compl (rvs q) R) hR.compl).indDom X) (Q.indDom X \ keyPiece (X := X) R)
      rw [subCompl_indDom (hR := hR)]
      exact Set.bijOn_id _)
    (by
      intro w _
      change ((Q.sub (compl (rvs q) R) hR.compl).indChart X (fun x hx => hX x hx.1)).correctedWeight w =
        (Q.indChart X hX).correctedWeight w
      rw [indChart_weight, indChart_weight]
      rfl)

/-- **Cutting the keys** splits the class of an indexed object. -/
theorem cls_indObj_cut (hA : Q.AllBounds) :
    cls (Q.indObj hA.bounds X hX) =
      cls ((Q.sub R hR).indObj (hA.sub R hR).bounds X (fun x hx => hX x hx.1)) +
        cls ((Q.sub (compl (rvs q) R) hR.compl).indObj (hA.sub _ hR.compl).bounds X (fun x hx => hX x hx.1)) := by
  rw [cls_partition (Q.indObj hA.bounds X hX) (keyPiece (X := X) R) (keyPiece_definable hR)]
  congr 1
  · exact (cls_eq_of_iso (Q.subIso hX hR)).symm
  · exact (cls_eq_of_iso (Q.subComplIso hX hR)).symm

theorem cls_indObj_empty (hK : Q.Bounds) (hQ : Q.carrier = ∅) : cls (Q.indObj hK X hX) = 0 := by
  apply cls_empty
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hw
  have h : keyOf w ∈ Q.carrier := hw.1
  rw [hQ] at h
  exact h

end Cut

/-! ### The cover -/

/-- **Descent of a finite cover of witness schemata.** If every key has a valid
witness schema in a finite list, the indexed objects are `μIsp^db`-related
over `B`. -/
theorem muIsp_ind_cover {k : ℕ} {X₀ Y₀ : ChartSchema B (rvs q) (1 + k)} :
    ∀ (L : List (WitnessSchema X₀ Y₀)) (Q : KeySet B q) (hA : Q.AllBounds)
      (hX : ∀ x ∈ Q.carrier, X₀.Valid x) (hY : ∀ x ∈ Q.carrier, Y₀.Valid x),
      (∀ x ∈ Q.carrier, ∃ W ∈ L, W.Valid x) →
      MuIsp (cls (Q.indObj hA.bounds X₀ hX)) (cls (Q.indObj hA.bounds Y₀ hY))
  | [], Q, hA, hX, hY, hcov => by
    have hQ : Q.carrier = ∅ := Set.eq_empty_of_forall_notMem fun x hx => by
      obtain ⟨W, hW, -⟩ := hcov x hx
      simp at hW
    rw [cls_indObj_empty hX hA.bounds hQ, cls_indObj_empty hY hA.bounds hQ]
    exact muIsp_refl 0
  | W :: L, Q, hA, hX, hY, hcov => by
    have hR : DefinableOverBase B (rvs q) {x | W.Valid x} := W.valid_definable
    rw [cls_indObj_cut hX hR hA, cls_indObj_cut hY hR hA]
    apply muIsp_add
    · exact (Q.sub _ hR).muIsp_ind (hA.sub _ hR).bounds W (fun x hx => hx.2)
    · refine muIsp_ind_cover L (Q.sub _ hR.compl) (hA.sub _ hR.compl) _ _ (fun x hx => ?_)
      obtain ⟨W', hW', hv⟩ := hcov x hx.1
      rcases List.mem_cons.mp hW' with rfl | h
      · exact absurd hv hx.2.2
      · exact ⟨W', h, hv⟩

/-- **Descent of a finite cover in degree `0`.** -/
theorem cls_ind0_cover {X₀ Y₀ : ChartSchema B (rvs q) 0} :
    ∀ (L : List (WitnessSchema0 X₀ Y₀)) (Q : KeySet B q) (hA : Q.AllBounds)
      (hX : ∀ x ∈ Q.carrier, X₀.Valid x) (hY : ∀ x ∈ Q.carrier, Y₀.Valid x),
      (∀ x ∈ Q.carrier, ∃ W ∈ L, W.Valid x) →
      cls (Q.indObj hA.bounds X₀ hX) = cls (Q.indObj hA.bounds Y₀ hY)
  | [], Q, hA, hX, hY, hcov => by
    have hQ : Q.carrier = ∅ := Set.eq_empty_of_forall_notMem fun x hx => by
      obtain ⟨W, hW, -⟩ := hcov x hx
      simp at hW
    rw [cls_indObj_empty hX hA.bounds hQ, cls_indObj_empty hY hA.bounds hQ]
  | W :: L, Q, hA, hX, hY, hcov => by
    have hR : DefinableOverBase B (rvs q) {x | W.Valid x} := W.valid_definable
    rw [cls_indObj_cut hX hR hA, cls_indObj_cut hY hR hA]
    congr 1
    · exact (Q.sub _ hR).cls_ind0 (hA.sub _ hR).bounds W (fun x hx => hx.2)
    · refine cls_ind0_cover L (Q.sub _ hR.compl) (hA.sub _ hR.compl) _ _ (fun x hx => ?_)
      obtain ⟨W', hW', hv⟩ := hcov x hx.1
      rcases List.mem_cons.mp hW' with rfl | h
      · exact absurd hv hx.2.2
      · exact ⟨W', h, hv⟩

end KeySet

end DiamondIntegral.Section7.Lemma714Schema
