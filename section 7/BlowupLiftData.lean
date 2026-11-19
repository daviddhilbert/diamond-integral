import «section 7».StrictCharts
import «section 7».MeasuredRVBridge
import «section 6».TupleFinitaryLifting

/-! The centres of the VF lift of an elementary blowup (Lemma 7.12,
`blowup:same:RV:coa`).

For an aperture datum `U = (U, f, ω)`, coordinate `j`, aperture `τ`, the
relation sending the inactive leading terms `r = f_{~j}(u)` to the finitely many
pairs `(f_j(u), τ(u) f_j(u))` is finitary, because `pr_{~j} ↾ f(U)` is
finite-to-one. Lemma 6.30 (in its tuple form, with continuous branches) lifts it
to definable centres `b₀(a, u) ∈ f_j(u)^♯` and `b₁(a, u) ∈ (τ(u) f_j(u))^♯`,
over the full inactive VF input `a ∈ r^♯`. No definable point of `τ(u)^♯` is
chosen. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 DiamondIntegral.Section2 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BlowupLiftData
open DiamondIntegral.Section4
open DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open AnnularBlowup BlowupChart RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

section Relation
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)

/-- The inactive structural coordinates `f_{~j}(u)`. -/
def inactCoord (u : Fin D.chart.arity → M) : Fin k → M :=
  fun i => D.chart.coordinate u (BlowupRelation.skip D.coordinate i)

/-- The pair `(f_j(u), τ(u) f_j(u))`. -/
def centrePair (u : Fin D.chart.arity → M) : Fin 2 → M :=
  ![D.chart.coordinate u D.coordinate, iRVMul (D.aperture.aperture u) (D.chart.coordinate u D.coordinate)]

theorem centrePair_nonzero {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) (i : Fin 2) :
    NonzeroRV (centrePair D u i) := by
  have hf : NonzeroRV (D.chart.coordinate u D.coordinate) := by
    have := D.chart.coordinate_proper u hu D.coordinate
    exact ⟨this.1, this.2⟩
  fin_cases i
  · exact hf
  · exact BlowupChart.nonzero_mul (D.aperture.nonzero u hu) hf

theorem inactCoord_nonzero {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) (i : Fin k) :
    NonzeroRV (inactCoord D u i) := by
  have := D.chart.coordinate_proper u hu (BlowupRelation.skip D.coordinate i)
  exact ⟨this.1, this.2⟩

/-- The centre relation: inactive leading terms to the pairs of target leading terms. -/
def centreRel (t : Fin k → RVInfinity M) (v : Fin 2 → RVInfinity M) : Prop :=
  ∃ u ∈ D.chart.domain, inactCoord D u = rvValues t ∧ centrePair D u = rvValues v

theorem inactive_eq_of_inactCoord {u u' : Fin D.chart.arity → M}
    (h : inactCoord D u = inactCoord D u') :
    AnnularBlowup.inactive D.chart D.coordinate u = AnnularBlowup.inactive D.chart D.coordinate u' := by
  funext l
  by_cases hl : l = D.coordinate
  · subst hl
    simp only [AnnularBlowup.inactive, Function.update_self]
  · obtain ⟨i, rfl⟩ := BlowupRelation.exists_skip D.coordinate l hl
    simp only [AnnularBlowup.inactive, Function.update_of_ne hl]
    exact congrFun h i

/-- The raw graph of `u ↦ (f_{~j}(u), f_j(u), τ(u) f_j(u))`. -/
def centreMap (u : Fin D.chart.arity → M) : Fin (2 + k) → M := join 2 k (inactCoord D u) (centrePair D u)

theorem centreMap_tupleDef : TupleDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain (centreMap D) := by
  have hI := D.chart.domain_definable
  have hc : TupleDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain D.chart.coordinate := D.chart.coordinate_definable
  have hcomp (l : Fin (1 + k)) : ScalarDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain
      (fun u => D.chart.coordinate u l) := scalarDef_comp_component hI hc l
  apply tupleDef_of_scalar hI
  intro i
  rcases block_cases 2 k i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · simpa only [centreMap, join_head, inactCoord] using hcomp (BlowupRelation.skip D.coordinate i')
  · simp only [centreMap, join_tail]
    fin_cases i'
    · exact hcomp D.coordinate
    · exact scalarDef_mul hI D.aperture.graph_definable (hcomp D.coordinate)

/-- The finitary relation of Lemma 6.30 for the centres. -/
def centreRelation : DiamondIntegral.Section6.FinitaryRVRelation S k 2 where
  rel := centreRel D
  definable := by
    have hW := base_real (BoundedClasses.graph_image_definable D.chart.domain (centreMap D)
      (centreMap_tupleDef D))
    let σ : Fin (2 + k) → Fin k ⊕ Fin 2 := join 2 k Sum.inl Sum.inr
    convert hW.preimage_comp σ using 1
    apply Set.ext
    intro z
    have hzh : (z ∘ σ) ∘ headIndex 2 k = z ∘ Sum.inl := by
      funext i
      simp only [Function.comp_apply, σ, join_head]
    have hzt : (z ∘ σ) ∘ tailIndex 2 k = z ∘ Sum.inr := by
      funext i
      simp only [Function.comp_apply, σ, join_tail]
    constructor
    · rintro ⟨t, v, ⟨u, hu, ht, hv⟩, hzt', hzv⟩
      refine ⟨u, hu, ?_⟩
      change centreMap D u = z ∘ σ
      rw [← join_reconstruct 2 k (z ∘ σ), hzh, hzt, centreMap, ht, hv, hzt', hzv]
    · rintro ⟨u, hu, he⟩
      have he' : centreMap D u = z ∘ σ := he
      have h1 : inactCoord D u = z ∘ Sum.inl := by
        rw [← hzh, ← he']
        funext i
        simp only [Function.comp_apply, centreMap, join_head]
      have h2 : centrePair D u = z ∘ Sum.inr := by
        rw [← hzt, ← he']
        funext i
        simp only [Function.comp_apply, centreMap, join_tail]
      refine ⟨rvTuple (inactCoord D u) (fun i => (inactCoord_nonzero D hu i).1),
        rvTuple (centrePair D u) (fun i => (centrePair_nonzero D hu i).1), ⟨u, hu, rfl, rfl⟩, ?_, ?_⟩
      · exact h1
      · exact h2
  finite := by
    intro t
    by_cases hne : ∃ u0 ∈ D.chart.domain, inactCoord D u0 = rvValues t
    · obtain ⟨u0, hu0, he0⟩ := hne
      have hF := (D.finite (AnnularBlowup.inactive D.chart D.coordinate u0)).image (centrePair D)
      refine Set.Finite.of_finite_image (f := rvValues) (hF.subset ?_) rvValues_injective.injOn
      rintro _ ⟨v, ⟨u, hu, ht, hv⟩, rfl⟩
      exact ⟨u, ⟨hu, inactive_eq_of_inactCoord D (ht.trans he0.symm)⟩, hv⟩
    · apply Set.Finite.subset Set.finite_empty
      rintro v ⟨u, hu, ht, _⟩
      exact hne ⟨u, hu, ht⟩
  source := by
    rintro t v ⟨u, hu, ht, _⟩ i hi
    have h := (inactCoord_nonzero D hu i).2
    rw [ht] at h
    exact h (congrArg Subtype.val hi)

end Relation

/-! ### The centres on the lift -/

section Centres
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : DiamondIntegral.Section6.TupleFinitaryLift (centreRelation D))

/-- The lifted object `𝕃U`: the Section 6 carrier of the measured object. -/
abbrev liftSet : DefSet (rawMixedSpace (M := M) (1 + k) D.chart.arity) S :=
  rvLift (toMeasured hc D.chart).object

/-- The inactive VF coordinates. -/
def inact (x : Fin (1 + k) → VF M) : Fin k → VF M := fun i => x (BlowupRelation.skip D.coordinate i)

/-- The target leading terms of a label, as an RV tuple (zero off the domain). -/
def vpair (l : Fin D.chart.arity → RVInfinity M) : Fin 2 → RVInfinity M :=
  if h : rvValues l ∈ D.chart.domain then
    rvTuple (centrePair D (rvValues l)) (fun i => (centrePair_nonzero D h i).1)
  else fun _ => rvZero M

/-- The centres: `b₀` (index `0`) in `f_j(u)^♯` and `b₁` (index `1`) in
`(τ(u) f_j(u))^♯`. -/
def centre (i : Fin 2) (x : Fin (1 + k) → VF M) (l : Fin D.chart.arity → RVInfinity M) : VF M :=
  L.center (DiamondIntegral.Section6.liftCode (inact D x) (vpair D l)) i

theorem mem_liftSet_iff (p : Mixed M (1 + k) D.chart.arity) :
    p ∈ (liftSet hc D).carrier ↔
      rvValues p.2 ∈ D.chart.domain ∧ rvValues (tupleRV M p.1) = D.chart.coordinate (rvValues p.2) := by
  constructor
  · rintro ⟨u, hu, hv⟩
    have hd : rvValues u.val ∈ D.chart.domain := u.property
    rw [hu] at hd
    refine ⟨hd, ?_⟩
    have h1 : rvValues (tupleRV M p.1) = rvValues ((toMeasured hc D.chart).object.value u) := by
      rw [hv]
      rfl
    rw [h1, ← hu]
    rfl
  · rintro ⟨hd, hv⟩
    refine ⟨⟨p.2, hd⟩, rfl, ?_⟩
    apply rvValues_injective
    change D.chart.coordinate (rvValues p.2) = rvValues (tupleRV M p.1)
    exact hv.symm

theorem rel_of_mem {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) :
    centreRel D (tupleRV M (inact D p.1)) (vpair D p.2) := by
  obtain ⟨hd, hv⟩ := (mem_liftSet_iff hc D p).mp hp
  refine ⟨rvValues p.2, hd, ?_, ?_⟩
  · funext i
    exact (congrFun hv (BlowupRelation.skip D.coordinate i)).symm
  · rw [vpair, dif_pos hd]
    rfl

theorem centre_rv {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) (i : Fin 2) :
    (rv M (centre D L i p.1 p.2)).val = centrePair D (rvValues p.2) i := by
  have h := L.prescribed (inact D p.1) (vpair D p.2) (rel_of_mem hc D hp) i
  obtain ⟨hd, _⟩ := (mem_liftSet_iff hc D p).mp hp
  rw [centre, h, vpair, dif_pos hd]
  rfl

theorem centre_update (i : Fin 2) (x : Fin (1 + k) → VF M) (l : Fin D.chart.arity → RVInfinity M) (c : VF M) :
    centre D L i (Function.update x D.coordinate c) l = centre D L i x l := by
  have h : inact D (Function.update x D.coordinate c) = inact D x := by
    funext m
    exact Function.update_of_ne (BlowupRelation.skip_ne D.coordinate m) _ _
  rw [centre, centre, h]

theorem coord_rv {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) (l : Fin (1 + k)) :
    (rv M (p.1 l)).val = D.chart.coordinate (rvValues p.2) l :=
  congrFun ((mem_liftSet_iff hc D p).mp hp).2 l

end Centres

end DiamondIntegral.Section7.BlowupLiftData
