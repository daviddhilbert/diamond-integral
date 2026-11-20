import «section 7».BlowupCongruence

/-! Enlarging the parameter base of Section 7's classes.

For bases `B`, `C` such that definability over `B` implies definability over
`C` (`Transfer`: for instance `B ⊆ C`, or the names of `B` in the definable
closure of `C`), a chart over `B` is a chart over `C` with the same data
(`chartExt`). Isomorphisms, apertures and annular data extend the same
way. The constructions of Section 4 (source, shell, endpoint, tagged union)
only use the data, so the blowup of an extended datum is the extension of the
blowup. Hence `clsExt : Cls B k →+ Cls C k` maps blowups to blowups
(`step_ext`, `steps_ext`) and `μIsp^db` over `B` into `μIsp^db` over `C`
(`muIsp_ext`). Corollary 7.15 uses this to pass from `S⟨b⟩` to `S⟨a⟩` when
`b` is definable from `a` over `S` (`Transfer.ofDcl`). -/

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
variable {B C : Base (M := M)}

/-- Definability over `B` implies definability over `C`. This holds when the
names of `B` are names of `C` (`Transfer.ofSubset`), and more generally when they
are in the definable closure of `C` (`Transfer.ofDcl`). -/
def Transfer (B C : Base (M := M)) : Prop :=
  ∀ {n : ℕ} {sn : Fin n → SortTag} {U : Set (Fin n → M)}, DefinableOverBase B sn U → DefinableOverBase C sn U

theorem Transfer.ofSubset (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) : Transfer B C :=
  fun h => h.mono hr hg

theorem Transfer.ofDcl (hreal : ∀ c ∈ B.real, ∃ σ, DefinableClosureAtBase C σ c)
    (hgamma : ∀ γ ∈ B.gamma, GammaDefinableClosureAtBase C γ) : Transfer B C :=
  fun h => h.eliminate_definable_params hreal hgamma

variable (ht : Transfer B C) {k : ℕ}

/-- A chart over `B` as a chart over `C`. -/
def chartExt (a : Chart B k) : Chart C k where
  arity := a.arity
  domain := a.domain
  domain_definable := ht a.domain_definable
  coordinate := a.coordinate
  coordinate_definable := ht a.coordinate_definable
  coordinate_proper := a.coordinate_proper
  finite_fibres := a.finite_fibres
  volume := a.volume
  volume_definable := ht a.volume_definable

/-- An isomorphism over `B` as one over `C`. -/
def isoExt {a b : Chart B k} (F : Iso a b) : Iso (chartExt ht a) (chartExt ht b) where
  equiv := F.equiv
  graph_definable := ht F.graph_definable
  weight_eq := F.weight_eq

/-- A bounded object over `B` as one over `C`. -/
def objExt (a : Obj B k) : Obj C k := ⟨chartExt ht a.toChart, a.domain_bounded⟩

/-- The extension of classes. -/
def clsExtFun : Cls B k → Cls C k :=
  Quotient.map (objExt ht) (fun _ _ ⟨F⟩ => ⟨isoExt ht F⟩)

theorem clsExtFun_cls (a : Obj B k) : clsExtFun ht (cls a) = cls (objExt ht a) := rfl

section Coproduct
open RVChartDisjointUnion RVMeasuredProduct RVNamedTuples RVTaggedCoproduct

/-- Chart data over `B` as data over `C`. -/
def dataExt {n : ℕ} (a : Data B n k) : Data C n k :=
  ⟨a.domain, ht a.domain_definable, a.coordinate, ht a.coordinate_definable, a.coordinate_proper,
    a.finite_fibres, a.volume, ht a.volume_definable⟩

theorem dataExt_castGrade {n l : ℕ} (h : k = l) (D : Data B n k) :
    dataExt ht (castGrade h D) = castGrade h (dataExt ht D) := by
  cases h
  rfl

theorem disjointUnion_congr {n : ℕ} {a a' b b' : Data C n k} (ha : a = a') (hb : b = b')
    (hd : Disjoint a.domain b.domain) (hd' : Disjoint a'.domain b'.domain) :
    disjointUnion a b hd = disjointUnion a' b' hd' := by
  subst ha hb
  rfl

theorem dataExt_leftData (a b : Chart B k) :
    dataExt ht (leftData a b) = leftData (chartExt ht a) (chartExt ht b) := by
  unfold leftData
  rw [dataExt_castGrade]
  rfl

theorem chartExt_coproduct (a b : Chart B k) :
    chartExt ht (coproduct a b) = coproduct (chartExt ht a) (chartExt ht b) := by
  change (dataExt ht (disjointUnion (leftData a b) (rightData a b) (tagged_disjoint a b))).toChart =
    (disjointUnion (leftData (chartExt ht a) (chartExt ht b)) (rightData (chartExt ht a) (chartExt ht b))
      (tagged_disjoint _ _)).toChart
  congr 1
  exact (show dataExt ht (disjointUnion (leftData a b) (rightData a b) (tagged_disjoint a b)) =
      disjointUnion (dataExt ht (leftData a b)) (dataExt ht (rightData a b)) (tagged_disjoint a b) from rfl).trans
    (disjointUnion_congr (dataExt_leftData ht a b) rfl _ _)

theorem objExt_coprod (a b : Obj B k) : objExt ht (coprod a b) = coprod (objExt ht a) (objExt ht b) := by
  change (⟨chartExt ht (coproduct a.toChart b.toChart), _⟩ : Obj C k) =
    ⟨coproduct (chartExt ht a.toChart) (chartExt ht b.toChart), _⟩
  congr 1
  exact chartExt_coproduct ht a.toChart b.toChart

end Coproduct

theorem objExt_empty : objExt ht (emptyObj B k) = emptyObj C k := rfl

/-- The extension of classes, as a monoid map. -/
def clsExt : Cls B k →+ Cls C k where
  toFun := clsExtFun ht
  map_zero' := by
    change cls (objExt ht (emptyObj B k)) = cls (emptyObj C k)
    rw [objExt_empty]
  map_add' x y := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    change cls (objExt ht (coprod _ _)) = cls (coprod _ _)
    rw [objExt_coprod]

theorem clsExt_cls (a : Obj B k) : clsExt ht (cls a) = cls (objExt ht a) := rfl

/-- An aperture over `B` as one over `C`. -/
def apertureExt {r : Chart B k} (A : Aperture r) : Aperture (chartExt ht r) where
  aperture := A.aperture
  graph_definable := ht A.graph_definable
  nonzero := A.nonzero
  nonnegative := A.nonnegative
  bound := A.bound
  bounded := A.bounded

/-- An annular datum over `B` as one over `C`. -/
def datumExt (D : AnnularDatum B k) : AnnularDatum C k where
  chart := chartExt ht D.chart
  coordinate := D.coordinate
  finite := D.finite
  aperture := apertureExt ht D.aperture
  bounded := D.bounded

theorem source_ext (D : AnnularDatum B k) : (datumExt ht D).source = objExt ht D.source := rfl

theorem annularObject_ext (D : AnnularDatum B k) :
    (datumExt ht D).annularObject = objExt ht D.annularObject :=
  (objExt_coprod ht (BlowupRelation.shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)
    (BlowupRelation.endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded)).symm

/-- A blowup over `B` is a blowup over `C`. -/
theorem step_ext {x y : Cls B (1 + k)} (h : Step x y) : Step (clsExt ht x) (clsExt ht y) := by
  obtain ⟨n, D, z, rfl, rfl⟩ := h
  refine ⟨n, fun i => datumExt ht (D i), clsExt ht z, ?_, ?_⟩
  · rw [map_add, map_sum]
    rfl
  · rw [map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [clsExt_cls, ← annularObject_ext]

theorem steps_ext {n : ℕ} {x y : Cls B (1 + k)} (h : BlowupSteps n x y) :
    BlowupSteps n (clsExt ht x) (clsExt ht y) := by
  induction h with
  | refl x => exact .refl _
  | cons h _ ih => exact .cons (step_ext ht h) ih

/-- `μIsp^db` over `B` implies `μIsp^db` over `C`. -/
theorem muIsp_ext {x y : Cls B (1 + k)} (h : MuIsp x y) : MuIsp (clsExt ht x) (clsExt ht y) := by
  obtain ⟨w, m, n, hx, hy⟩ := h
  exact ⟨clsExt ht w, m, n, steps_ext ht hx, steps_ext ht hy⟩

end DiamondIntegral.Section7.BaseExtension
