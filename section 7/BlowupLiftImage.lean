import «section 7».BlowupLiftData
import «section 7».ElementaryBlowups
import «section 7».ElementaryComparison
import «section 6».RelativeApertureChains
import «section 6».Regularization
import «section 6».RegularizationGeometry
import «section 6».ApertureCore
import «section 6».ContractedApertures

/-! The image of the lift of an elementary blowup under its centripetal
transformation (Lemma 7.12, `blowup:same:RV:coa`).

For the relative aperture data `R` of `BlowupLiftData`, the point map sends
`(a, u)` to `a_j - b₀ + b₁` on the core `|a_j - b₀| < |b₁|` (tag `rv(-1)`) and
to `a_j - b₀` off it (tag `rv(1)`). Regularization then records the leading
terms of the image as labels. The regularized image is the RV pullback of an
explicit raw label set, the union of
* the endpoint labels `(f♭(u, τ(u)), rv(-1), u)`, and
* the shell labels `(f♭(u, s), rv(1), u)` with `0 < vrv s ≤ vrv τ(u)`.
These are the images of the endpoint and shell charts of Definition 7.2 under
explicit raw maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 DiamondIntegral.Section2 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BlowupLiftImage
open DiamondIntegral.Section4
open DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open AnnularBlowup BlowupChart RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts DiamondIntegral.Section7.MeasuredRVBridge
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.ElementaryBlowups

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-! ### Raw labels of the regularized image -/

section Labels
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)

/-- The number of labels after regularization. -/
abbrev labN : ℕ := (1 + k) + (1 + D.chart.arity)

/-- The leading-term labels. -/
def hd (w : Fin (labN D) → M) : Fin (1 + k) → M := fun i => w (Fin.castAdd (1 + D.chart.arity) i)

/-- The branch tag. -/
def tg (w : Fin (labN D) → M) : M := w (Fin.natAdd (1 + k) (Fin.castAdd D.chart.arity 0))

/-- The original label. -/
def lb (w : Fin (labN D) → M) : Fin D.chart.arity → M := fun i => w (Fin.natAdd (1 + k) (Fin.natAdd 1 i))

/-- Assemble a label from leading terms, a tag and an original label. -/
def mk (h : Fin (1 + k) → M) (t : M) (u : Fin D.chart.arity → M) : Fin (labN D) → M :=
  Fin.append h (Fin.append ![t] u)

@[simp] theorem hd_mk (h : Fin (1 + k) → M) (t : M) (u : Fin D.chart.arity → M) : hd D (mk D h t u) = h := by
  funext i
  simp only [hd, mk, Fin.append_left]

@[simp] theorem tg_mk (h : Fin (1 + k) → M) (t : M) (u : Fin D.chart.arity → M) : tg D (mk D h t u) = t := by
  simp only [tg, mk, Fin.append_right, Fin.append_left, Matrix.cons_val_fin_one]

@[simp] theorem lb_mk (h : Fin (1 + k) → M) (t : M) (u : Fin D.chart.arity → M) : lb D (mk D h t u) = u := by
  funext i
  simp only [lb, mk, Fin.append_right]

theorem mk_recon (w : Fin (labN D) → M) : mk D (hd D w) (tg D w) (lb D w) = w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [mk, hd, Fin.append_left]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [mk, tg, Fin.append_right, Fin.append_left]
      rw [Subsingleton.elim i 0]
      rfl
    · simp only [mk, lb, Fin.append_right]

theorem mk_injective {h h' : Fin (1 + k) → M} {t t' : M} {u u' : Fin D.chart.arity → M}
    (he : mk D h t u = mk D h' t' u') : h = h' ∧ t = t' ∧ u = u' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd_mk] using congrArg (hd D) he
  · simpa only [tg_mk] using congrArg (tg D) he
  · simpa only [lb_mk] using congrArg (lb D) he

/-- The endpoint labels of a point `(u, τ(u))` of the endpoint chart. -/
def Fe (w : Fin (1 + D.chart.arity) → M) : Fin (labN D) → M :=
  mk D (blownCoordinate D.chart D.coordinate (w ∘ headIndex 1 D.chart.arity) (w (aIdx D.chart))) minusOne
    (w ∘ headIndex 1 D.chart.arity)

/-- The shell labels of a point `(u, τ(u), s)` of the shell chart. -/
def Fs (w : Fin (1 + (1 + D.chart.arity)) → M) : Fin (labN D) → M :=
  mk D (blownCoordinate D.chart D.coordinate (w ∘ xIdx D.chart) (w (sIdx D.chart))) iRVOne (w ∘ xIdx D.chart)

/-- The endpoint label set. -/
def Icore : Set (Fin (labN D) → M) := Fe D '' (graphChart D.chart D.aperture).domain

/-- The shell label set. -/
def Ishell : Set (Fin (labN D) → M) := Fs D '' shellDomain D.chart D.aperture

theorem scalarDef_of_tupleDef {B : Base (M := M)} {n m : ℕ} {I : Set (Fin n → M)}
    {G : (Fin n → M) → (Fin m → M)} (hG : TupleDef B I G) (i : Fin m) : ScalarDef B I (fun w => G w i) :=
  scalarDef_comp (g := fun v => v i) hG (scalarDef_coord (graph_image_definable I G hG) i)
    (fun w hw => ⟨w, hw, rfl⟩)

theorem tupleDef_mk {B : Base (M := M)} {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {h : (Fin n → M) → Fin (1 + k) → M}
    {t : (Fin n → M) → M} {u : (Fin n → M) → Fin D.chart.arity → M}
    (hh : TupleDef B I h) (ht : ScalarDef B I t) (hu : TupleDef B I u) :
    TupleDef B I (fun w => mk D (h w) (t w) (u w)) := by
  apply tupleDef_of_scalar hI
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [mk, Fin.append_left] using scalarDef_of_tupleDef hh i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Subsingleton.elim i 0]
      simpa only [mk, Fin.append_right, Fin.append_left, Matrix.cons_val_fin_one] using ht
    · simpa only [mk, Fin.append_right] using scalarDef_of_tupleDef hu i

theorem Fe_tupleDef : TupleDef (⟨S, ∅⟩ : Base (M := M)) (graphChart D.chart D.aperture).domain (Fe D) := by
  have hI := (graphChart D.chart D.aperture).domain_definable
  exact tupleDef_mk D hI (endpointChart D.chart D.coordinate D.finite D.aperture).coordinate_definable
    (scalarDef_const hI minusOne_definable) (tupleDef_coord hI _)

theorem Fs_tupleDef : TupleDef (⟨S, ∅⟩ : Base (M := M)) (shellDomain D.chart D.aperture) (Fs D) := by
  have hI := (shellChart D.chart D.coordinate D.finite D.aperture).domain_definable
  exact tupleDef_mk D hI (shellChart D.chart D.coordinate D.finite D.aperture).coordinate_definable
    (scalarDef_const hI (RVNamedTuples.one_definable _)) (tupleDef_coord hI _)

theorem Icore_definable : DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (fun _ : Fin (labN D) => .rv) (Icore D) :=
  graph_image_definable _ _ (Fe_tupleDef D)

theorem Ishell_definable : DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (fun _ : Fin (labN D) => .rv) (Ishell D) :=
  graph_image_definable _ _ (Fs_tupleDef D)

end Labels

/-! ### Membership in the label sets -/

section Members
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)

theorem join_comp_head {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) :
    join n m u y ∘ headIndex n m = u := funext (fun i => join_head n m u y i)

theorem join_comp_tail {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) :
    join n m u y ∘ tailIndex n m = y := funext (fun i => join_tail n m u y i)

theorem mem_graph_join {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) :
    join 1 D.chart.arity u ![D.aperture.aperture u] ∈ (graphChart D.chart D.aperture).domain := by
  refine ⟨?_, ?_⟩
  · rw [join_comp_head]
    exact hu
  · rw [join_comp_head, join_comp_tail]

theorem mem_Icore_iff (w : Fin (labN D) → M) :
    w ∈ Icore D ↔ lb D w ∈ D.chart.domain ∧ tg D w = minusOne ∧
      hd D w = blownCoordinate D.chart D.coordinate (lb D w) (D.aperture.aperture (lb D w)) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have ha := graph_aperture D.chart D.aperture hv
    refine ⟨?_, ?_, ?_⟩
    · rw [Fe, lb_mk]
      exact hv.1
    · rw [Fe, tg_mk]
    · rw [Fe, hd_mk, lb_mk, ha]
  · rintro ⟨hl, ht, hh⟩
    refine ⟨join 1 D.chart.arity (lb D w) ![D.aperture.aperture (lb D w)], mem_graph_join D hl, ?_⟩
    have h1 : join 1 D.chart.arity (lb D w) ![D.aperture.aperture (lb D w)] ∘ headIndex 1 D.chart.arity = lb D w :=
      join_comp_head _ _ _ _
    have h2 : join 1 D.chart.arity (lb D w) ![D.aperture.aperture (lb D w)] (aIdx D.chart) =
        D.aperture.aperture (lb D w) := join_tail _ _ _ _ 0
    rw [Fe, h1, h2, ← hh, ← ht, mk_recon]

theorem mem_shell_join {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) {s : M} (hs : NonzeroRV s)
    (h1 : 1 < codeValue s) (h2 : codeValue s ≤ codeValue (D.aperture.aperture u)) :
    join 1 (1 + D.chart.arity) (join 1 D.chart.arity u ![D.aperture.aperture u]) ![s] ∈
      shellDomain D.chart D.aperture := by
  rw [shell_iff]
  rw [join_comp_head, join_comp_tail]
  refine ⟨mem_graph_join D hu, ?_, ?_, ?_⟩
  · intro i
    rw [Subsingleton.elim i 0]
    exact ⟨hs.1, hs.2⟩
  · have hs' : join 1 (1 + D.chart.arity) (join 1 D.chart.arity u ![D.aperture.aperture u]) ![s]
        (sIdx D.chart) = s := join_tail _ _ _ _ 0
    rw [hs']
    exact h1
  · have he : join 1 D.chart.arity u ![D.aperture.aperture u] (aIdx D.chart) = D.aperture.aperture u :=
      join_tail _ _ _ _ 0
    have hs' : join 1 (1 + D.chart.arity) (join 1 D.chart.arity u ![D.aperture.aperture u]) ![s]
        (sIdx D.chart) = s := join_tail _ _ _ _ 0
    rw [hs', he]
    exact h2

theorem mem_Ishell_iff (w : Fin (labN D) → M) :
    w ∈ Ishell D ↔ lb D w ∈ D.chart.domain ∧ tg D w = iRVOne ∧
      ∃ s, NonzeroRV s ∧ 1 < codeValue s ∧ codeValue s ≤ codeValue (D.aperture.aperture (lb D w)) ∧
        hd D w = blownCoordinate D.chart D.coordinate (lb D w) s := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hd', hs, h1, h2⟩ := shell_points D.chart D.aperture hv
    refine ⟨?_, ?_, v (sIdx D.chart), hs, ?_, ?_, ?_⟩
    · rw [Fs, lb_mk]
      exact hd'
    · rw [Fs, tg_mk]
    · exact h1
    · rw [Fs, lb_mk]
      exact h2
    · rw [Fs, hd_mk, lb_mk]
  · rintro ⟨hl, ht, s, hs, h1, h2, hh⟩
    refine ⟨_, mem_shell_join D hl hs h1 h2, ?_⟩
    have hx : join 1 (1 + D.chart.arity) (join 1 D.chart.arity (lb D w) ![D.aperture.aperture (lb D w)]) ![s] ∘
        xIdx D.chart = lb D w := by
      rw [xIdx_eq, join_comp_head, join_comp_head]
    have hs' : join 1 (1 + D.chart.arity) (join 1 D.chart.arity (lb D w) ![D.aperture.aperture (lb D w)]) ![s]
        (sIdx D.chart) = s := join_tail _ _ _ _ 0
    rw [Fs, hx, hs', ← hh, ← ht, mk_recon]

theorem mem_Ishell_iff' (w : Fin (labN D) → M) :
    w ∈ Ishell D ↔ lb D w ∈ D.chart.domain ∧ tg D w = iRVOne ∧
      (∀ l ≠ D.coordinate, hd D w l = D.chart.coordinate (lb D w) l) ∧ NonzeroRV (hd D w D.coordinate) ∧
      codeValue (D.chart.coordinate (lb D w) D.coordinate) < codeValue (hd D w D.coordinate) ∧
      codeValue (hd D w D.coordinate) ≤
        codeValue (iRVMul (D.aperture.aperture (lb D w)) (D.chart.coordinate (lb D w) D.coordinate)) := by
  rw [mem_Ishell_iff]
  constructor
  · rintro ⟨hl, ht, s, hs, h1, h2, hh⟩
    have hf : NonzeroRV (D.chart.coordinate (lb D w) D.coordinate) :=
      ⟨(D.chart.coordinate_proper _ hl _).1, (D.chart.coordinate_proper _ hl _).2⟩
    have hj : hd D w D.coordinate = iRVMul s (D.chart.coordinate (lb D w) D.coordinate) := by
      rw [hh, blownCoordinate_at]
    refine ⟨hl, ht, fun l hl' => by rw [hh, blownCoordinate, Function.update_of_ne hl'], ?_, ?_, ?_⟩
    · rw [hj]
      exact nonzero_mul hs hf
    · rw [hj, GammaGroupNames.codeValue_mul _ _ hs hf]
      exact lt_mul_of_one_lt_left' _ h1
    · rw [hj, GammaGroupNames.codeValue_mul _ _ hs hf,
        GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero _ hl) hf]
      exact mul_le_mul_left h2 _
  · rintro ⟨hl, ht, hoff, hn, h1, h2⟩
    have hf : NonzeroRV (D.chart.coordinate (lb D w) D.coordinate) :=
      ⟨(D.chart.coordinate_proper _ hl _).1, (D.chart.coordinate_proper _ hl _).2⟩
    refine ⟨hl, ht, ElementaryComparison.rvDiv (hd D w D.coordinate) (D.chart.coordinate (lb D w) D.coordinate),
      ElementaryComparison.rvDiv_nonzero hn hf, ?_, ?_, ?_⟩
    · rw [ElementaryComparison.codeValue_rvDiv hn hf, ← div_eq_mul_inv]
      exact one_lt_div'.mpr h1
    · rw [ElementaryComparison.codeValue_rvDiv hn hf, ← div_eq_mul_inv, div_le_iff_le_mul]
      rw [GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero _ hl) hf] at h2
      exact h2
    · funext l
      by_cases hl' : l = D.coordinate
      · subst hl'
        rw [blownCoordinate_at]
        exact ((ElementaryComparison.mul_eq_iff_rvDiv
          (ElementaryComparison.rvDiv_nonzero hn hf).1 hn.1 hf).mpr rfl).symm
      · rw [blownCoordinate, Function.update_of_ne hl']
        exact hoff l hl'

theorem Icore_Ishell_disjoint (h00 : M ⊨ Axioms.ACVF00) {w : Fin (labN D) → M} (h1 : w ∈ Icore D)
    (h2 : w ∈ Ishell D) : False :=
  minusOne_ne_one h00 (((mem_Icore_iff D w).mp h1).2.1.symm.trans ((mem_Ishell_iff D w).mp h2).2.1)

end Members

/-! ### Centres from the inactive leading terms -/

section CentresGeneral
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : DiamondIntegral.Section6.TupleFinitaryLift (centreRelation D))

theorem rel_of_inactive {x : Fin (1 + k) → VF M} {l : Fin D.chart.arity → RVInfinity M}
    (hl : rvValues l ∈ D.chart.domain)
    (hx : ∀ i, (rv M (x (BlowupRelation.skip D.coordinate i))).val =
      D.chart.coordinate (rvValues l) (BlowupRelation.skip D.coordinate i)) :
    centreRel D (tupleRV M (inact D x)) (vpair D l) := by
  refine ⟨rvValues l, hl, ?_, ?_⟩
  · funext i
    exact (hx i).symm
  · rw [vpair, dif_pos hl]
    rfl

theorem centre_rv' {x : Fin (1 + k) → VF M} {l : Fin D.chart.arity → RVInfinity M}
    (hl : rvValues l ∈ D.chart.domain)
    (hx : ∀ i, (rv M (x (BlowupRelation.skip D.coordinate i))).val =
      D.chart.coordinate (rvValues l) (BlowupRelation.skip D.coordinate i)) (i : Fin 2) :
    (rv M (centre D L i x l)).val = centrePair D (rvValues l) i := by
  have h := L.prescribed (inact D x) (vpair D l) (rel_of_inactive D hl hx) i
  rw [centre, h, vpair, dif_pos hl]
  rfl

theorem centre_ne_zero' {x : Fin (1 + k) → VF M} {l : Fin D.chart.arity → RVInfinity M}
    (hl : rvValues l ∈ D.chart.domain)
    (hx : ∀ i, (rv M (x (BlowupRelation.skip D.coordinate i))).val =
      D.chart.coordinate (rvValues l) (BlowupRelation.skip D.coordinate i)) (i : Fin 2) :
    centre D L i x l ≠ 0 :=
  ne_zero_of_rv (centre_rv' D L hl hx i) (centrePair_nonzero D hl i)

theorem vfValue_centre' {x : Fin (1 + k) → VF M} {l : Fin D.chart.arity → RVInfinity M}
    (hl : rvValues l ∈ D.chart.domain)
    (hx : ∀ i, (rv M (x (BlowupRelation.skip D.coordinate i))).val =
      D.chart.coordinate (rvValues l) (BlowupRelation.skip D.coordinate i)) (i : Fin 2) :
    vfValue (centre D L i x l) = (codeValue (centrePair D (rvValues l) i)).val :=
  vfValue_eq_codeValue (centre_rv' D L hl hx i) (centrePair_nonzero D hl i)

end CentresGeneral

/-! ### The regularized image -/

section Image
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : DiamondIntegral.Section6.TupleFinitaryLift (centreRelation D))
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hU : (toMeasured hc D.chart).doublyBounded)
variable (hP : DiamondIntegral.Section6.ProperInvariant S (liftSet hc D).carrier)
variable (Δ : Values.Gamma (M := M))
variable (hΔ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}})
variable (hΔ1 : 1 ≤ Δ) (hΔb : ∀ u ∈ D.chart.domain, codeValue (D.aperture.aperture u) ≤ Δ)

theorem tag_mem {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) :
    p.2 ∈ (tags hc D).carrier := by
  obtain ⟨u, hu, _⟩ := hp
  exact hu ▸ u.property

theorem extFocus {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) :
    (apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).extendedFocus p = centre D L 0 p.1 p.2 :=
  ((apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).extendedFocus_active hp (tag_mem hc D hp)).trans
    (centre_update D L 0 p.1 p.2 0)

theorem extEndpoint {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) :
    (apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).extendedEndpoint p = centre D L 1 p.1 p.2 :=
  ((apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).extendedEndpoint_active hp (tag_mem hc D hp)).trans
    (centre_update D L 1 p.1 p.2 0)

theorem core_eq {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) :
    (apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).core p =
      decide (vfValue (centre D L 1 p.1 p.2) < vfValue (p.1 D.coordinate - centre D L 0 p.1 p.2)) := by
  unfold DiamondIntegral.Section6.RelativeApertureData.core
  rw [extFocus hc D L hv hU hP Δ hΔ hΔ1 hΔb hp, extEndpoint hc D L hv hU hP Δ hΔ hΔ1 hΔb hp]
  rfl

theorem point_eq {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) :
    (apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).point p =
      (Function.update p.1 D.coordinate (p.1 D.coordinate - centre D L 0 p.1 p.2 +
        if (apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).core p then centre D L 1 p.1 p.2 else 0),
        Fin.append (fun _ : Fin 1 => DiamondIntegral.Section6.branchTag (M := M)
          ((apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).core p)) p.2) := by
  unfold DiamondIntegral.Section6.RelativeApertureData.point
  rw [extFocus hc D L hv hU hP Δ hΔ hΔ1 hΔb hp, extEndpoint hc D L hv hU hP Δ hΔ hΔ1 hΔb hp]
  rfl

theorem rvValues_regLabels (x : Fin (1 + k) → VF M) (b : RVInfinity M) (u : Fin D.chart.arity → RVInfinity M) :
    rvValues (Fin.append (tupleRV M x) (Fin.append (fun _ : Fin 1 => b) u)) =
      mk D (rvValues (tupleRV M x)) b.val (rvValues u) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [rvValues, mk, Fin.append_left]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Subsingleton.elim i 0]
      simp only [rvValues, mk, Fin.append_right, Fin.append_left, Matrix.cons_val_fin_one]
    · simp only [rvValues, mk, Fin.append_right]

theorem branchTag_true_val : (DiamondIntegral.Section6.branchTag (M := M) true).val = minusOne := rfl

theorem branchTag_false_val : (DiamondIntegral.Section6.branchTag (M := M) false).val = iRVOne := by
  change iRv (iVFOne (M := M)) = iRVOne
  exact RVCalc.rv_one hM

theorem vfValue_lt_infinity {b : VF M} (hb : b ≠ 0) : ¬ Values.infinity ≤ vfValue b := fun h =>
  hb ((vfValue_eq_infinity_iff b).mp (le_antisymm (Values.le_infinity _) h))

/-- The regularized labels of an image point lie in the endpoint or shell label set. -/
theorem point_labels_mem {x : Fin (1 + k) → VF M} {u : Fin D.chart.arity → RVInfinity M}
    (hx : (x, u) ∈ (liftSet hc D).carrier) (c : Bool)
    (hcore : c = decide (vfValue (centre D L 1 x u) < vfValue (x D.coordinate - centre D L 0 x u))) :
    mk D (rvValues (tupleRV M (Function.update x D.coordinate (x D.coordinate - centre D L 0 x u +
      if c then centre D L 1 x u else 0)))) (DiamondIntegral.Section6.branchTag (M := M) c).val (rvValues u) ∈
        Icore D ∪ Ishell D := by
  obtain ⟨hl, hrv⟩ := (mem_liftSet_iff hc D (x, u)).mp hx
  have hb0 := centre_rv hc D L hx 0
  have hb1 := centre_rv hc D L hx 1
  have hne0 := centre_ne_zero hc D L hx 0
  have hne1 := centre_ne_zero hc D L hx 1
  have hf : NonzeroRV (D.chart.coordinate (rvValues u) D.coordinate) :=
    ⟨(D.chart.coordinate_proper _ hl _).1, (D.chart.coordinate_proper _ hl _).2⟩
  have hoff : ∀ (e : VF M), ∀ l ≠ D.coordinate,
      rvValues (tupleRV M (Function.update x D.coordinate e)) l = D.chart.coordinate (rvValues u) l := by
    intro e l hl'
    change (rv M (Function.update x D.coordinate e l)).val = _
    rw [Function.update_of_ne hl']
    exact congrFun hrv l
  cases c with
  | true =>
    left
    rw [mem_Icore_iff, lb_mk, tg_mk, hd_mk]
    refine ⟨hl, rfl, ?_⟩
    funext l
    by_cases hl' : l = D.coordinate
    · subst hl'
      rw [blownCoordinate_at]
      have hlt : vfValue (centre D L 1 x u) < vfValue (x D.coordinate - centre D L 0 x u) :=
        of_decide_eq_true hcore.symm
      have he : rv M (x D.coordinate - centre D L 0 x u + centre D L 1 x u) = rv M (centre D L 1 x u) :=
        (DiamondIntegral.Section6.rv_eq_iff_value_close hne1).mpr (by rw [add_sub_cancel_right]; exact hlt)
      change (rv M (Function.update x D.coordinate _ D.coordinate)).val = _
      rw [Function.update_self, if_pos rfl, he, hb1]
      rfl
    · rw [blownCoordinate, Function.update_of_ne hl']
      exact hoff _ l hl'
  | false =>
    right
    rw [mem_Ishell_iff', lb_mk, tg_mk, hd_mk]
    have hnlt : ¬ vfValue (centre D L 1 x u) < vfValue (x D.coordinate - centre D L 0 x u) :=
      fun h => Bool.false_ne_true (hcore.trans (decide_eq_true h))
    have hy : x D.coordinate - centre D L 0 x u ≠ 0 := by
      intro h0
      rw [h0, (vfValue_eq_infinity_iff (0 : VF M)).mpr rfl] at hnlt
      exact hnlt (lt_of_le_of_ne (Values.le_infinity _)
        (fun he => hne1 ((vfValue_eq_infinity_iff _).mp he)))
    have hj : rvValues (tupleRV M (Function.update x D.coordinate (x D.coordinate - centre D L 0 x u +
        if false then centre D L 1 x u else 0))) D.coordinate = iRv (x D.coordinate - centre D L 0 x u).val := by
      change (rv M (Function.update x D.coordinate _ D.coordinate)).val = _
      rw [Function.update_self, if_neg Bool.false_ne_true, add_zero]
      rfl
    have hnz := DiamondIntegral.Section6.iRv_nonzero hy
    have hvy : vfValue (x D.coordinate - centre D L 0 x u) = (codeValue (iRv (x D.coordinate - centre D L 0 x u).val)).val :=
      vfValue_eq_codeValue rfl hnz
    refine ⟨hl, branchTag_false_val, fun l hl' => hoff _ l hl', ?_, ?_, ?_⟩
    · rw [hj]
      exact hnz
    · rw [hj]
      have hxr : rv M (x D.coordinate) = rv M (centre D L 0 x u) :=
        Subtype.ext ((congrFun hrv D.coordinate).trans hb0.symm)
      have hlt := (DiamondIntegral.Section6.rv_eq_iff_value_close hne0).mp hxr
      rw [vfValue_eq_codeValue hb0 (centrePair_nonzero D hl 0), hvy] at hlt
      exact hlt
    · rw [hj]
      have hle := not_lt.mp hnlt
      rw [vfValue_eq_codeValue hb1 (centrePair_nonzero D hl 1), hvy] at hle
      exact hle

/-- The regularized image of the lift under the centripetal transformation. -/
abbrev Vreg : DefSet (rawMixedSpace (M := M) (1 + k) (labN D)) S :=
  (DiamondIntegral.Section6.regularizeMap (apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).map.image).image

theorem mem_Vreg_of_point {a : Mixed M (1 + k) D.chart.arity} (ha : a ∈ (liftSet hc D).carrier) :
    DiamondIntegral.Section6.regularize ((apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).point a) ∈
      (Vreg hc D L hv hU hP Δ hΔ hΔ1 hΔb).carrier := by
  rw [DiamondIntegral.Section6.regularization_carrier]
  refine ⟨_, ?_, rfl⟩
  rw [DiamondIntegral.Section6.RelativeApertureData.image_carrier]
  exact ⟨a, ha, rfl⟩

/-- The regularized image is the RV pullback of the endpoint and shell labels. -/
theorem mem_Vreg_iff (p : Mixed M (1 + k) (labN D)) :
    p ∈ (Vreg hc D L hv hU hP Δ hΔ hΔ1 hΔb).carrier ↔
      rvValues p.2 ∈ Icore D ∪ Ishell D ∧ rvValues (tupleRV M p.1) = hd D (rvValues p.2) := by
  constructor
  · intro hp
    rw [DiamondIntegral.Section6.regularization_carrier] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [DiamondIntegral.Section6.RelativeApertureData.image_carrier] at hq
    obtain ⟨⟨x, u⟩, ha, rfl⟩ := hq
    rw [point_eq hc D L hv hU hP Δ hΔ hΔ1 hΔb ha]
    change rvValues (Fin.append (tupleRV M _) (Fin.append (fun _ : Fin 1 => _) u)) ∈ _ ∧
      rvValues (tupleRV M _) = hd D (rvValues (Fin.append (tupleRV M _) (Fin.append (fun _ : Fin 1 => _) u)))
    rw [rvValues_regLabels, hd_mk]
    exact ⟨point_labels_mem hc D L ha _ (core_eq hc D L hv hU hP Δ hΔ hΔ1 hΔb ha), rfl⟩
  · rintro ⟨hw, hhd⟩
    obtain ⟨y, t⟩ := p
    let u : Fin D.chart.arity → RVInfinity M := fun i => t (Fin.natAdd (1 + k) (Fin.natAdd 1 i))
    have hu : rvValues u = lb D (rvValues t) := rfl
    have hyj : ∀ l, (rv M (y l)).val = hd D (rvValues t) l := fun l => congrFun hhd l
    have hl : rvValues u ∈ D.chart.domain := by
      rcases hw with h | h
      · exact ((mem_Icore_iff D _).mp h).1
      · exact ((mem_Ishell_iff D _).mp h).1
    have hoff : ∀ l ≠ D.coordinate, (rv M (y l)).val = D.chart.coordinate (rvValues u) l := by
      intro l hl'
      rw [hyj l]
      rcases hw with h | h
      · rw [((mem_Icore_iff D _).mp h).2.2, blownCoordinate, Function.update_of_ne hl']
        rfl
      · exact ((mem_Ishell_iff' D _).mp h).2.2.1 l hl'
    have hin : ∀ i, (rv M (y (BlowupRelation.skip D.coordinate i))).val =
        D.chart.coordinate (rvValues u) (BlowupRelation.skip D.coordinate i) :=
      fun i => hoff _ (BlowupRelation.skip_ne D.coordinate i)
    have hb0 := centre_rv' D L hl hin 0
    have hb1 := centre_rv' D L hl hin 1
    have hne0 := centre_ne_zero' D L hl hin 0
    have hne1 := centre_ne_zero' D L hl hin 1
    have hv0 := vfValue_centre' D L hl hin 0
    have hv1 := vfValue_centre' D L hl hin 1
    have hle01 := centrePair_le D hl
    -- a candidate preimage `(x, u)` with `x` differing from `y` only at `j`
    have key : ∀ (e : VF M) (c : Bool), (rv M e) = rv M (centre D L 0 y u) →
        c = decide (vfValue (centre D L 1 y u) < vfValue (e - centre D L 0 y u)) →
        e - centre D L 0 y u + (if c then centre D L 1 y u else 0) = y D.coordinate →
        t = Fin.append (tupleRV M y) (Fin.append (fun _ : Fin 1 => DiamondIntegral.Section6.branchTag (M := M) c) u) →
        (y, t) ∈ (Vreg hc D L hv hU hP Δ hΔ hΔ1 hΔb).carrier := by
      intro e c he hc' hy ht
      let x := Function.update y D.coordinate e
      have hxu : (x, u) ∈ (liftSet hc D).carrier := by
        refine (mem_liftSet_iff hc D (x, u)).mpr ⟨hl, funext (fun l => ?_)⟩
        change (rv M (Function.update y D.coordinate e l)).val = _
        by_cases hl' : l = D.coordinate
        · subst hl'
          rw [Function.update_self, he]
          exact hb0
        · rw [Function.update_of_ne hl']
          exact hoff l hl'
      have hc0 : centre D L 0 x u = centre D L 0 y u := centre_update D L 0 y u e
      have hc1 : centre D L 1 x u = centre D L 1 y u := centre_update D L 1 y u e
      have hcore : (apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).core (x, u) = c := by
        have hxj : x D.coordinate = e := Function.update_self _ _ _
        rw [core_eq hc D L hv hU hP Δ hΔ hΔ1 hΔb hxu, hc', hc0, hc1]
        simp only [hxj]
      have h := mem_Vreg_of_point hc D L hv hU hP Δ hΔ hΔ1 hΔb hxu
      rw [point_eq hc D L hv hU hP Δ hΔ hΔ1 hΔb hxu, hcore, hc0, hc1] at h
      have hx : Function.update x D.coordinate (x D.coordinate - centre D L 0 y u +
          if c then centre D L 1 y u else 0) = y := by
        change Function.update (Function.update y D.coordinate e) D.coordinate
          (Function.update y D.coordinate e D.coordinate - _ + _) = y
        rw [Function.update_self, hy, Function.update_idem, Function.update_eq_self]
      rw [hx] at h
      rw [ht]
      exact h
    have htag : ∀ c : Bool, tg D (rvValues t) = (DiamondIntegral.Section6.branchTag (M := M) c).val →
        t = Fin.append (tupleRV M y) (Fin.append (fun _ : Fin 1 => DiamondIntegral.Section6.branchTag (M := M) c) u) := by
      intro c hc'
      apply rvValues_injective
      rw [rvValues_regLabels, hhd, ← hc', hu]
      exact (mk_recon D (rvValues t)).symm
    rcases hw with h | h
    · obtain ⟨_, htg, hhead⟩ := (mem_Icore_iff D _).mp h
      have hyr : rv M (y D.coordinate) = rv M (centre D L 1 y u) := by
        apply Subtype.ext
        rw [hb1, hyj, hhead, blownCoordinate_at]
        rfl
      have hlt := (DiamondIntegral.Section6.rv_eq_iff_value_close hne1).mp hyr
      apply key (y D.coordinate - centre D L 1 y u + centre D L 0 y u) true
      · apply (DiamondIntegral.Section6.rv_eq_iff_value_close hne0).mpr
        rw [add_sub_cancel_right, hv0]
        exact lt_of_le_of_lt (by rw [hv1]; exact hle01) hlt
      · rw [add_sub_cancel_right]
        exact (decide_eq_true hlt).symm
      · rw [if_pos rfl, add_sub_cancel_right, sub_add_cancel]
      · exact htag true (htg.trans branchTag_true_val.symm)
    · obtain ⟨_, htg, _, hnz, h1, h2⟩ := (mem_Ishell_iff' D _).mp h
      have hvy : vfValue (y D.coordinate) = (codeValue (hd D (rvValues t) D.coordinate)).val :=
        vfValue_eq_codeValue (hyj _) hnz
      apply key (y D.coordinate + centre D L 0 y u) false
      · apply (DiamondIntegral.Section6.rv_eq_iff_value_close hne0).mpr
        rw [add_sub_cancel_right, hv0, hvy]
        exact h1
      · rw [add_sub_cancel_right]
        refine (decide_eq_false (fun hlt => ?_)).symm
        rw [hv1, hvy] at hlt
        exact absurd h2 (not_le.mpr hlt)
      · rw [if_neg Bool.false_ne_true, add_zero, add_sub_cancel_right]
      · exact htag false (htg.trans branchTag_false_val.symm)

end Image

end DiamondIntegral.Section7.BlowupLiftImage
