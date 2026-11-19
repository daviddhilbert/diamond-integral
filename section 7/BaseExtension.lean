import «section 7».BlowupCongruence

/-! Enlarging the parameter base of Section 7's classes.

For bases `B ⊆ C` (real and Γ names), a chart over `B` is a chart over `C`
with the same data (`Chart.ext`): every definability requirement is
monotone in the base. Isomorphisms, apertures and annular data extend the same
way. The constructions of Section 4 (source, shell, endpoint, tagged union)
only use the data, so the blowup of an extended datum is the extension of the
blowup. Hence `clsExt : Cls B k →+ Cls C k` maps blowups to blowups
(`step_ext`, `steps_ext`) and `μIsp^db` over `B` into `μIsp^db` over `C`
(`muIsp_ext`). Corollary 7.15 uses this to pass from `S⟨b⟩` to `S⟨a⟩` when
`b` is defined from `a`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.BaseExtension
open DiamondIntegral.Section4
open RVMeasuredCharts AnnularBlowup RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BlowupCongruence IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) {k : ℕ}

/-- A chart over `B` as a chart over `C`. -/
def chartExt (a : Chart B k) : Chart C k where
  arity := a.arity
  domain := a.domain
  domain_definable := a.domain_definable.mono hr hg
  coordinate := a.coordinate
  coordinate_definable := a.coordinate_definable.mono hr hg
  coordinate_proper := a.coordinate_proper
  finite_fibres := a.finite_fibres
  volume := a.volume
  volume_definable := a.volume_definable.mono hr hg

/-- An isomorphism over `B` as one over `C`. -/
def isoExt {a b : Chart B k} (F : Iso a b) : Iso (chartExt hr hg a) (chartExt hr hg b) where
  equiv := F.equiv
  graph_definable := F.graph_definable.mono hr hg
  weight_eq := F.weight_eq

/-- A bounded object over `B` as one over `C`. -/
def objExt (a : Obj B k) : Obj C k := ⟨chartExt hr hg a.toChart, a.domain_bounded⟩

/-- The extension of classes. -/
def clsExtFun : Cls B k → Cls C k :=
  Quotient.map (objExt hr hg) (fun _ _ ⟨F⟩ => ⟨isoExt hr hg F⟩)

theorem clsExtFun_cls (a : Obj B k) : clsExtFun hr hg (cls a) = cls (objExt hr hg a) := rfl

section Coproduct
open RVChartDisjointUnion RVMeasuredProduct RVNamedTuples RVTaggedCoproduct

/-- Chart data over `B` as data over `C`. -/
def dataExt {n : ℕ} (a : Data B n k) : Data C n k :=
  ⟨a.domain, a.domain_definable.mono hr hg, a.coordinate, a.coordinate_definable.mono hr hg, a.coordinate_proper,
    a.finite_fibres, a.volume, a.volume_definable.mono hr hg⟩

theorem dataExt_castGrade {n l : ℕ} (h : k = l) (D : Data B n k) :
    dataExt hr hg (castGrade h D) = castGrade h (dataExt hr hg D) := by
  cases h
  rfl

theorem disjointUnion_congr {n : ℕ} {a a' b b' : Data C n k} (ha : a = a') (hb : b = b')
    (hd : Disjoint a.domain b.domain) (hd' : Disjoint a'.domain b'.domain) :
    disjointUnion a b hd = disjointUnion a' b' hd' := by
  subst ha hb
  rfl

theorem dataExt_leftData (a b : Chart B k) :
    dataExt hr hg (leftData a b) = leftData (chartExt hr hg a) (chartExt hr hg b) := by
  unfold leftData
  rw [dataExt_castGrade]
  rfl

theorem chartExt_coproduct (a b : Chart B k) :
    chartExt hr hg (coproduct a b) = coproduct (chartExt hr hg a) (chartExt hr hg b) := by
  change (dataExt hr hg (disjointUnion (leftData a b) (rightData a b) (tagged_disjoint a b))).toChart =
    (disjointUnion (leftData (chartExt hr hg a) (chartExt hr hg b)) (rightData (chartExt hr hg a) (chartExt hr hg b))
      (tagged_disjoint _ _)).toChart
  congr 1
  exact (show dataExt hr hg (disjointUnion (leftData a b) (rightData a b) (tagged_disjoint a b)) =
      disjointUnion (dataExt hr hg (leftData a b)) (dataExt hr hg (rightData a b)) (tagged_disjoint a b) from rfl).trans
    (disjointUnion_congr (dataExt_leftData hr hg a b) rfl _ _)

theorem objExt_coprod (a b : Obj B k) : objExt hr hg (coprod a b) = coprod (objExt hr hg a) (objExt hr hg b) := by
  change (⟨chartExt hr hg (coproduct a.toChart b.toChart), _⟩ : Obj C k) =
    ⟨coproduct (chartExt hr hg a.toChart) (chartExt hr hg b.toChart), _⟩
  congr 1
  exact chartExt_coproduct hr hg a.toChart b.toChart

end Coproduct

theorem objExt_empty : objExt hr hg (emptyObj B k) = emptyObj C k := rfl

/-- The extension of classes, as a monoid map. -/
def clsExt : Cls B k →+ Cls C k where
  toFun := clsExtFun hr hg
  map_zero' := by
    change cls (objExt hr hg (emptyObj B k)) = cls (emptyObj C k)
    rw [objExt_empty]
  map_add' x y := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    change cls (objExt hr hg (coprod _ _)) = cls (coprod _ _)
    rw [objExt_coprod]

theorem clsExt_cls (a : Obj B k) : clsExt hr hg (cls a) = cls (objExt hr hg a) := rfl

/-- An aperture over `B` as one over `C`. -/
def apertureExt {r : Chart B k} (A : Aperture r) : Aperture (chartExt hr hg r) where
  aperture := A.aperture
  graph_definable := A.graph_definable.mono hr hg
  nonzero := A.nonzero
  nonnegative := A.nonnegative
  bound := A.bound
  bounded := A.bounded

/-- An annular datum over `B` as one over `C`. -/
def datumExt (D : AnnularDatum B k) : AnnularDatum C k where
  chart := chartExt hr hg D.chart
  coordinate := D.coordinate
  finite := D.finite
  aperture := apertureExt hr hg D.aperture
  bounded := D.bounded

theorem source_ext (D : AnnularDatum B k) : (datumExt hr hg D).source = objExt hr hg D.source := rfl

theorem annularObject_ext (D : AnnularDatum B k) :
    (datumExt hr hg D).annularObject = objExt hr hg D.annularObject :=
  (objExt_coprod hr hg (BlowupRelation.shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)
    (BlowupRelation.endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded)).symm

/-- A blowup over `B` is a blowup over `C`. -/
theorem step_ext {x y : Cls B (1 + k)} (h : Step x y) : Step (clsExt hr hg x) (clsExt hr hg y) := by
  obtain ⟨n, D, z, rfl, rfl⟩ := h
  refine ⟨n, fun i => datumExt hr hg (D i), clsExt hr hg z, ?_, ?_⟩
  · rw [map_add, map_sum]
    rfl
  · rw [map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [clsExt_cls, ← annularObject_ext]

theorem steps_ext {n : ℕ} {x y : Cls B (1 + k)} (h : BlowupSteps n x y) :
    BlowupSteps n (clsExt hr hg x) (clsExt hr hg y) := by
  induction h with
  | refl x => exact .refl _
  | cons h _ ih => exact .cons (step_ext hr hg h) ih

/-- `μIsp^db` over `B` implies `μIsp^db` over `C`. -/
theorem muIsp_ext {x y : Cls B (1 + k)} (h : MuIsp x y) : MuIsp (clsExt hr hg x) (clsExt hr hg y) := by
  obtain ⟨w, m, n, hx, hy⟩ := h
  exact ⟨clsExt hr hg w, m, n, steps_ext hr hg hx, steps_ext hr hg hy⟩

end DiamondIntegral.Section7.BaseExtension
