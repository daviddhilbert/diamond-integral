import «section 5».Section5DischargedInputs
import «section 5».NativeWeakVFFubini
import «section 5».NativeWeakFiniteRVSchemaPromotion
import «section 5».NativeWeakRVLiftPresentations
import «section 5».NativeWeakLiftValues
import «section 5».NativeGeometricBaseStrataValues
import «section 5».NativeMixedCoordinateMaps

/-! Theorem 5.17 and Proposition 5.23 for fibre representatives in RV[*]
(RV[<=k] objects with labels allowed to vanish), with both earlier-section
inputs instantiated by checked proofs.

* `bounded_weak_fubini_discharged`: Theorem 5.17 for RV[*] representatives.
* `nativeWeakGeometricValue`: the normalized geometric value of an RV[*]
  object, `∑_I L^{-card I} 𝔼̃_g(U_I)` over its exact-degree strata
  (`nativeWeakGeometricValue_eq_sum_strata`); it is the geometric value of
  the integral of the lift (`nativeVFGeometricValue_weak_lift`) and the usual
  value on single-degree objects (`nativeWeakGeometricValue_toWeak`).
* `geometric_weak_fubini_discharged`: Proposition 5.23 for RV[*]
  representatives; the single-degree hypothesis is a special case
  (`NativeGeometricVFFibreLiftEquality.toWeak`).

Proof of 5.23. Each vanishing label of a finite RV schema is thickened by the
affine padding object `𝔾_m ⊔ pt` on its zero stratum (`thickAt`); this is a
first-order operation on the original-ground formulas. The thickened schema
has nonzero labels, its single-degree row value is the RV[*] row value
(`thickFull_row_value`), and its lift family has the same geometric VF value
(`thickSeq_vf`, from `E_g(∫(𝒪^× ⊔ (1+𝔪))) = 1`). Compactness supplies finitely
many complete witnesses (RV[<=k] schemas, lift graphs, a common degree and a
stabilized RES certificate for the padded thickenings); on each base piece
the single-degree fixed-witness theorem applies to the thickenings. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge Section3RVClassCuts
open Algebra.GrothendieckAddGroup
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

section BoundedWeak
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

theorem bounded_weak_fubini_discharged (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z∈nativeMixedDomain C,NativeBoundedWeakVFFibreLiftEquality G.model00
      GammaQE.gamma_piecewise_rational_affine G.uncountable.le G.saturated G.small_real
      G.small_gamma G.nontrivial_definable_gamma f f' z) :
    section5BoundedVFIntegral G hc (nativeVFClass A)=section5BoundedVFIntegral G hc (nativeVFClass A') :=
  nativeBoundedWeakVFFubini GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc) A A' C f f' h

end BoundedWeak

/-! ### The geometric value of an RV[*] representative -/
section WeakValue
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

/-- The stratum of an RV[<=k] object on which exactly the labels in `I` are nonzero. -/
def weakZeroPatternDomain (U : NativeWeakRVObject hc B k) (I : Finset (Fin k)) :
    GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity) :=
  U.volume.preimage (nativeRVZeroPatternBase (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k)) id I)

theorem weakZeroPatternDomain_mem (U : NativeWeakRVObject hc B k) (I : Finset (Fin k)) (u : U.domain) :
    u.val ∈ (weakZeroPatternDomain U I).carrier ↔ nativeRVZeroPattern id I (rvValues (U.volume u).val) := by
  constructor
  · rintro ⟨a,ha,hm⟩
    have he : a = u := Subtype.ext ha
    subst he
    exact ((nativeRVZeroPatternBase_mem _ id I _).mp hm).2
  · intro h
    exact ⟨u,rfl,(nativeRVZeroPatternBase_mem _ id I _).mpr ⟨Set.mem_univ _,h⟩⟩

theorem weakZeroPatternDomain_subset (U : NativeWeakRVObject hc B k) (I : Finset (Fin k)) :
    (weakZeroPatternDomain U I).carrier ⊆ U.domain.carrier :=
  U.volume.preimage_subset _

/-- A single-degree RV[k] object regarded as an RV[<=k] object. -/
def nativeStrictToWeak (U : GammaGroundRVObject hc B k) : NativeWeakRVObject hc B k :=
  ⟨U.arity,U.domain,U.volume,U.finite⟩

theorem nativeStrictToWeak_lift (U : GammaGroundRVObject hc B k) :
    (nativeWeakRVObjectLift (nativeStrictToWeak U)).carrier = (gammaGroundObjectLift U).carrier := rfl

end WeakValue

section WeakValueDef
variable {k : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

/-- The normalized geometric value of an RV[*] object, presented as an RV[<=k] object:
each exact-degree stratum is normalized in its own degree. -/
def nativeWeakGeometricValue (U : NativeWeakRVObject hc B k) : RESAffineLocalization.Target B :=
  ∑ I : Finset (Fin k),geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B)
    (nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .geometric (weakZeroPatternDomain U I)) (Fintype.card I)

theorem nativeRVSetValue_empty (kind : EulerKind) {n : ℕ} (X : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (hX : X.carrier = ∅) : nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X = 0 := by
  have h := nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind X
    (fun i : Empty => i.elim) (fun i => i.elim) (fun x => by simp [hX])
  simpa using h

/-- On a single-degree object the RV[*] value is the usual geometric value. -/
theorem nativeWeakGeometricValue_toWeak (U : GammaGroundRVObject hc B k) :
    nativeWeakGeometricValue h00 linear hκ hs hc B hr hγ hΓ (nativeStrictToWeak U) =
      nativeGroundGeometricRetraction h00 linear hκ hs hr hγ hΓ (ordinaryClass U) := by
  rw [nativeGroundGeometricRetraction_class,← nativeRVSetValue_object]
  unfold nativeWeakGeometricValue
  have hall : ∀ u : U.domain,nativeRVZeroPattern id Finset.univ (rvValues (U.volume u).val) := by
    intro u i
    simp only [Finset.mem_univ,true_iff,id]
    exact U.nonzero u i
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin k))]
  · have hc' : (weakZeroPatternDomain (nativeStrictToWeak U) Finset.univ).carrier = U.domain.carrier := by
      ext u
      constructor
      · exact fun h => weakZeroPatternDomain_subset (nativeStrictToWeak U) _ h
      · intro hu
        exact (weakZeroPatternDomain_mem (nativeStrictToWeak U) _ ⟨u,hu⟩).mpr (hall ⟨u,hu⟩)
    rw [nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ .geometric _ _
      (GammaGroundBijection.ofCarrierEq hc'),Fintype.card_coe,Finset.card_univ,Fintype.card_fin]
  · intro I _ hI
    have he : (weakZeroPatternDomain (nativeStrictToWeak U) I).carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have hp := (weakZeroPatternDomain_mem (nativeStrictToWeak U) I ⟨u,weakZeroPatternDomain_subset (nativeStrictToWeak U) I hu⟩).mp hu
      apply hI
      ext i
      have h1 := hp i
      have h2 := hall ⟨u,weakZeroPatternDomain_subset (nativeStrictToWeak U) I hu⟩ i
      exact h1.trans h2.symm
    rw [nativeRVSetValue_empty h00 linear hκ hs hc B hr hγ hΓ .geometric _ he]
    unfold geometricDegreeValue
    simp
  · intro h
    exact False.elim (h (Finset.mem_univ _))

end WeakValueDef

/-! ### Exact-degree strata as single-degree objects -/
section WeakStrata
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

/-- The stratum of an RV[<=k] object with nonzero labels exactly `I`, as an object of RV[card I]. -/
def weakStratumObject (U : NativeWeakRVObject hc B k) (I : Finset (Fin k)) :
    GammaGroundRVObject hc B (Fintype.card I) where
  arity := U.arity
  domain := weakZeroPatternDomain U I
  volume := (gammaGroundRVSelectCoordinates (nativeVFZeroPatternIndex I)
    (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k))).comp (U.volume.restrict (weakZeroPatternDomain_subset U I))
  finite := by
    intro t
    let S := {a : weakZeroPatternDomain U I | ((gammaGroundRVSelectCoordinates (nativeVFZeroPatternIndex I)
      (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k))).comp (U.volume.restrict (weakZeroPatternDomain_subset U I))) a = t}
    change S.Finite
    by_cases hS : S.Nonempty
    · obtain ⟨a0,ha0⟩ := hS
      let u0 : U.domain := ⟨a0.val,weakZeroPatternDomain_subset U I a0.property⟩
      have hvol : ∀ a ∈ S,U.volume ⟨a.val,weakZeroPatternDomain_subset U I a.property⟩ = U.volume u0 := by
        intro a ha
        apply Subtype.ext
        funext j
        have hpa := (weakZeroPatternDomain_mem U I ⟨a.val,weakZeroPatternDomain_subset U I a.property⟩).mp a.property j
        have hp0 := (weakZeroPatternDomain_mem U I u0).mp a0.property j
        by_cases hj : j ∈ I
        · obtain ⟨i,rfl⟩ := (nativeVFZeroPatternIndex_range I j).mpr hj
          have h1 := congrArg (fun x => x.val i) ha
          have h2 := congrArg (fun x => x.val i) ha0
          exact h1.trans h2.symm
        · have ha' : rvValues (U.volume ⟨a.val,weakZeroPatternDomain_subset U I a.property⟩).val j = iRVZero := by
            by_contra hn; exact hj (hpa.mpr hn)
          have h0' : rvValues (U.volume u0).val j = iRVZero := by
            by_contra hn; exact hj (hp0.mpr hn)
          exact Subtype.ext (ha'.trans h0'.symm)
      let ι : weakZeroPatternDomain U I → U.domain := fun a => ⟨a.val,weakZeroPatternDomain_subset U I a.property⟩
      have hι : Set.InjOn ι (ι ⁻¹' {x | U.volume x = U.volume u0}) :=
        fun a _ b _ h => Subtype.ext (congrArg (fun x : U.domain => x.val) h)
      exact ((U.finite (U.volume u0)).preimage hι).subset (fun a ha => hvol a ha)
    · rw [Set.not_nonempty_iff_eq_empty.mp hS]
      exact Set.finite_empty
  nonzero := by
    intro a j
    have hp := (weakZeroPatternDomain_mem U I ⟨a.val,weakZeroPatternDomain_subset U I a.property⟩).mp a.property
      (nativeVFZeroPatternIndex I j)
    exact hp.mp ((nativeVFZeroPatternIndex_range I _).mp ⟨j,rfl⟩)

end WeakStrata

section WeakStrataValues
variable {k : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

/-- The RV[*] value is the sum of the usual geometric values of the exact-degree strata,
`𝔼_g(U) = ∑_I 𝔼_g(U_I)` with `U_I ∈ RV[card I]`. -/
theorem nativeWeakGeometricValue_eq_sum_strata (U : NativeWeakRVObject hc B k) :
    nativeWeakGeometricValue h00 linear hκ hs hc B hr hγ hΓ U =
      ∑ I : Finset (Fin k),nativeGroundGeometricRetraction h00 linear hκ hs hr hγ hΓ
        (ordinaryClass (weakStratumObject U I)) := by
  unfold nativeWeakGeometricValue
  apply Finset.sum_congr rfl
  intro I _
  rw [nativeGroundGeometricRetraction_class,← nativeRVSetValue_object]
  rfl

/-- The bounded value used in the RV[*] Theorem 5.17 hypothesis is the sum of the raw
values of the exact-degree strata, `𝔼_b(U) = ∑_I 𝔼_b(U_I)`. -/
theorem nativeRVSetValue_weak_eq_sum_strata (kind : EulerKind) (U : NativeWeakRVObject hc B k) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind U.domain =
      ∑ I : Finset (Fin k),nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
        (ordinaryClass (weakStratumObject U I)) := by
  rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind U.domain (weakZeroPatternDomain U)]
  · apply Finset.sum_congr rfl
    intro I _
    exact nativeRVSetValue_object h00 linear hκ hs hc B hr hγ hΓ kind (weakStratumObject U I)
  · intro I J hIJ
    apply Set.disjoint_left.mpr
    intro u hI hJ
    have hu := weakZeroPatternDomain_subset U I hI
    have h1 := (weakZeroPatternDomain_mem U I ⟨u,hu⟩).mp hI
    have h2 := (weakZeroPatternDomain_mem U J ⟨u,hu⟩).mp hJ
    exact hIJ (Finset.ext (fun j => (h1 j).trans (h2 j).symm))
  · intro u
    constructor
    · intro hu
      refine ⟨Finset.univ.filter (fun j => rvValues (U.volume ⟨u,hu⟩).val j ≠ iRVZero),?_⟩
      refine (weakZeroPatternDomain_mem U _ ⟨u,hu⟩).mpr ?_
      intro j
      simp
    · rintro ⟨I,hI⟩
      exact weakZeroPatternDomain_subset U I hI

end WeakStrataValues

/-! ### Thickening one zero-able label of a finite RV schema

The label `i` is replaced, on its zero stratum, by the affine-line padding
object `𝔸_RES = 𝔾_m ⊔ pt`. This is a first-order operation on the
original-ground formulas, uniform in the parameters. -/
section Thickening
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

theorem iRV_iRVZero : iRV (iRVZero : M) := by
  have h := (0 : CanonicalRV.RVSort M).property
  rw [RVOperations.zero_val] at h
  exact h

variable (hc B) in
/-- The number of extra RV coordinates of the padding object. -/
abbrev thickC : ℕ := (nativeAffineRVPower hc B 1).arity

variable (hc B) in
/-- The label graph of the padding object `𝔸_RES`. -/
def thickPadGraph : Set (Fin (thickC hc B + 1) → M) :=
  nativeWeakRVLabelGraph (nativeStrictToWeak (nativeAffineRVPower hc B 1))

theorem thickPadGraph_definable :
    DefinableOverBase B (Fin.append (fun _ : Fin (thickC hc B) => .rv) (fun _ : Fin 1 => .rv))
      (thickPadGraph hc B) :=
  nativeWeakRVLabelGraph_definable (nativeStrictToWeak (nativeAffineRVPower hc B 1))

/-- The thickened label relation, written in separated coordinates. -/
def thickRel (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaFiniteRVSchema B p a k sp) (i : Fin k)
    (z : Fin p → M) (u : Fin a → M) (w : Fin (thickC hc B) → M) (y : Fin k → M) : Prop :=
  (Fin.append (Fin.append z u) y ∈ F.volume ∧ y i ≠ iRVZero ∧ ∀ j,w j = iRVZero) ∨
  (Fin.append (Fin.append z u) (Function.update y i iRVZero) ∈ F.volume ∧
    Fin.append w (fun _ : Fin 1 => y i) ∈ thickPadGraph hc B)

section Coordinates
variable {c : ℕ}
def thZ (x : Fin ((p+(a+c))+k) → M) : Fin p → M := fun j => x (Fin.castAdd k (Fin.castAdd (a+c) j))
def thU (x : Fin ((p+(a+c))+k) → M) : Fin a → M := fun j => x (Fin.castAdd k (Fin.natAdd p (Fin.castAdd c j)))
def thW (x : Fin ((p+(a+c))+k) → M) : Fin c → M := fun j => x (Fin.castAdd k (Fin.natAdd p (Fin.natAdd a j)))
def thY (x : Fin ((p+(a+c))+k) → M) : Fin k → M := fun j => x (Fin.natAdd (p+(a+c)) j)

@[simp] theorem thZ_append (z : Fin p → M) (u : Fin a → M) (w : Fin c → M) (y : Fin k → M) :
    thZ (Fin.append (Fin.append z (Fin.append u w)) y) = z := by
  funext j; simp [thZ]
@[simp] theorem thU_append (z : Fin p → M) (u : Fin a → M) (w : Fin c → M) (y : Fin k → M) :
    thU (Fin.append (Fin.append z (Fin.append u w)) y) = u := by
  funext j; simp [thU]
@[simp] theorem thW_append (z : Fin p → M) (u : Fin a → M) (w : Fin c → M) (y : Fin k → M) :
    thW (Fin.append (Fin.append z (Fin.append u w)) y) = w := by
  funext j; simp [thW]
@[simp] theorem thY_append (z : Fin p → M) (u : Fin a → M) (w : Fin c → M) (y : Fin k → M) :
    thY (Fin.append (Fin.append z (Fin.append u w)) y) = y := by
  funext j; simp [thY]

theorem th_split (x : Fin ((p+(a+c))+k) → M) :
    x = Fin.append (Fin.append (thZ x) (Fin.append (thU x) (thW x))) (thY x) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [thZ]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [thU,thW]
  · simp [thY]
end Coordinates

/-- Sorts of the thickened volume relation. -/
abbrev thickSort (sp : Fin p → SortTag) (a c k : ℕ) : Fin ((p+(a+c))+k) → SortTag :=
  Fin.append (Fin.append sp (fun _ : Fin (a+c) => .rv)) (fun _ : Fin k => .rv)

theorem thick_sorted_iff {c : ℕ} (z : Fin p → M) (u : Fin a → M) (w : Fin c → M) (y : Fin k → M) :
    Fin.append (Fin.append z (Fin.append u w)) y ∈ sortedUniverse (thickSort sp a c k) ↔
      (∀ j,sortEval (sp j) (z j)) ∧ (∀ j,iRV (u j)) ∧ (∀ j,iRV (w j)) ∧ (∀ j,iRV (y j)) := by
  constructor
  · intro h
    refine ⟨fun j => ?_,fun j => ?_,fun j => ?_,fun j => ?_⟩
    · simpa using h (Fin.castAdd k (Fin.castAdd (a+c) j))
    · simpa [sortEval,iRV] using h (Fin.castAdd k (Fin.natAdd p (Fin.castAdd c j)))
    · simpa [sortEval,iRV] using h (Fin.castAdd k (Fin.natAdd p (Fin.natAdd a j)))
    · simpa [sortEval,iRV] using h (Fin.natAdd (p+(a+c)) j)
  · rintro ⟨hz,hu,hw,hy⟩ j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hz j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa [sortEval,iRV] using hu j
        · simpa [sortEval,iRV] using hw j
    · simpa [sortEval,iRV] using hy j

theorem coord_eq_zero_predicate (hc : CanonicalStructure.IsCanonical (M := M)) {n : ℕ} (s : Fin n → SortTag) (j : Fin n) :
    OriginalSortedPredicate B s (fun x => x j = iRVZero) := by
  have h := parameter_free_formula_original_definable hc B s
    ((Term.var j).equal (Term.func Fn.rvZero Fin.elim0))
  apply OriginalSortedPredicate.congr h
  intro z _
  have he : (Term.func Fn.rvZero (Fin.elim0 : Fin 0 → LRV.Term (Fin n))).realize z = iRVZero := by
    simp only [Term.realize_func,iRVZero]
    congr 1
    exact Subsingleton.elim _ _
  simp only [Formula.realize_equal,Term.realize_var,he]

theorem thickRel_predicate (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) :
    OriginalSortedPredicate B (thickSort sp a (thickC hc B) k)
      (fun x => thickRel hc F i (thZ x) (thU x) (thW x) (thY x)) := by
  let c := thickC hc B
  let st := thickSort sp a c k
  -- the original volume, read on (z,u,y)
  let π1 : Fin ((p+a)+k) → Fin ((p+(a+c))+k) :=
    Fin.append (Fin.append (fun j => Fin.castAdd k (Fin.castAdd (a+c) j))
      (fun j => Fin.castAdd k (Fin.natAdd p (Fin.castAdd c j)))) (fun j => Fin.natAdd (p+(a+c)) j)
  have hπ1 (x : Fin ((p+(a+c))+k) → M) : x ∘ π1 = Fin.append (Fin.append (thZ x) (thU x)) (thY x) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [π1,thZ,thU]
    · simp [π1,thY]
  have hV : OriginalSortedPredicate B st
      (fun x => Fin.append (Fin.append (thZ x) (thU x)) (thY x) ∈ F.volume) := by
    have h := (OriginalSortedPredicate.of_definable (s := Fin.append (Fin.append sp (fun _ : Fin a => .rv))
      (fun _ : Fin k => .rv)) F.volume_definable).pullback (t := st) π1 (by
        intro j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [π1,st]
        · simp [π1,st])
    exact h.congr (fun x _ => by rw [hπ1])
  -- the label `i` is nonzero
  have hY : OriginalSortedPredicate B st (fun x => thY x i ≠ iRVZero) :=
    (coord_eq_zero_predicate hc st (Fin.natAdd (p+(a+c)) i)).neg
  -- the padding coordinates vanish
  have hW0 : OriginalSortedPredicate B st (fun x => ∀ j,thW x j = iRVZero) :=
    OriginalSortedPredicate.finite_all (fun j => coord_eq_zero_predicate hc st
      (Fin.castAdd k (Fin.natAdd p (Fin.natAdd a j))))
  -- the original volume with label `i` replaced by zero
  let st1 : Fin (((p+(a+c))+k)+1) → SortTag := Fin.append st (fun _ : Fin 1 => .rv)
  let π2 : Fin ((p+a)+k) → Fin (((p+(a+c))+k)+1) :=
    Fin.append (Fin.append (fun j => Fin.castAdd 1 (Fin.castAdd k (Fin.castAdd (a+c) j)))
      (fun j => Fin.castAdd 1 (Fin.castAdd k (Fin.natAdd p (Fin.castAdd c j)))))
      (fun j => if j = i then Fin.natAdd ((p+(a+c))+k) 0 else Fin.castAdd 1 (Fin.natAdd (p+(a+c)) j))
  have hπ2 (x : Fin ((p+(a+c))+k) → M) (t : Fin 1 → M) :
      Fin.append x t ∘ π2 = Fin.append (Fin.append (thZ x) (thU x)) (Function.update (thY x) i (t 0)) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [π2,thZ,thU]
    · by_cases hj : j = i
      · subst hj; simp [π2]
      · simp [π2,hj,thY]
  have hR : OriginalSortedPredicate B st1
      (fun x => x (Fin.natAdd ((p+(a+c))+k) 0) = iRVZero ∧ x ∘ π2 ∈ F.volume) := by
    refine (coord_eq_zero_predicate hc st1 _).conj ?_
    exact (OriginalSortedPredicate.of_definable (s := Fin.append (Fin.append sp (fun _ : Fin a => .rv))
      (fun _ : Fin k => .rv)) F.volume_definable).pullback (t := st1) π2 (by
        intro j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [π2,st1,st]
        · by_cases hj : j = i
          · subst hj; simp [π2,st1,st]
          · simp [π2,st1,st,hj])
  have hU : OriginalSortedPredicate B st
      (fun x => Fin.append (Fin.append (thZ x) (thU x)) (Function.update (thY x) i iRVZero) ∈ F.volume) := by
    have h := hR.ex
    apply h.congr
    intro x _
    constructor
    · rintro ⟨t,ht,h0,hv⟩
      have h0' : t 0 = iRVZero := by simpa using h0
      rw [hπ2,h0'] at hv
      exact hv
    · intro hv
      refine ⟨fun _ => iRVZero,fun _ => iRV_iRVZero,by simp,?_⟩
      rw [hπ2]
      exact hv
  -- the padding graph
  let π3 : Fin (c+1) → Fin ((p+(a+c))+k) :=
    Fin.append (fun j => Fin.castAdd k (Fin.natAdd p (Fin.natAdd a j))) (fun _ => Fin.natAdd (p+(a+c)) i)
  have hπ3 (x : Fin ((p+(a+c))+k) → M) : x ∘ π3 = Fin.append (thW x) (fun _ : Fin 1 => thY x i) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [π3,thW,thY]
  have hP : OriginalSortedPredicate B st
      (fun x => Fin.append (thW x) (fun _ : Fin 1 => thY x i) ∈ thickPadGraph hc B) := by
    have h := (OriginalSortedPredicate.of_definable (thickPadGraph_definable (hc := hc) (B := B))).pullback
      (t := st) π3 (by
        intro j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [π3,st,c])
    exact h.congr (fun x _ => by rw [hπ3])
  exact (hV.conj (hY.conj hW0)).disj (hU.conj hP)

/-- The thickened volume relation. -/
def thickVolume (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) : Set (Fin ((p+(a+thickC hc B))+k) → M) :=
  {x | x ∈ sortedUniverse (thickSort sp a (thickC hc B) k) ∧ thickRel hc F i (thZ x) (thU x) (thW x) (thY x)}

theorem thickVolume_definable (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) :
    DefinableOverBase B (thickSort sp a (thickC hc B) k) (thickVolume hc F i) :=
  thickRel_predicate F i

theorem thickDomain_predicate (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) :
    OriginalSortedPredicate B (Fin.append sp (fun _ : Fin (a+thickC hc B) => .rv))
      (fun x => ∃ y : Fin k → M,y ∈ sortedUniverse (fun _ : Fin k => SortTag.rv) ∧
        Fin.append x y ∈ thickVolume hc F i) :=
  (OriginalSortedPredicate.of_definable (thickVolume_definable F i)).ex

/-- Thickening of label `i`, with fibre bound `F.bound + F.bound * N` for a bound `N`
of the padding object's fibres. -/
def thickAt (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) (N : ℕ) :
    GammaFiniteRVSchema B p (a+thickC hc B) k sp where
  domain := {x | x ∈ sortedUniverse (Fin.append sp (fun _ : Fin (a+thickC hc B) => .rv)) ∧
    ∃ y : Fin k → M,y ∈ sortedUniverse (fun _ : Fin k => SortTag.rv) ∧ Fin.append x y ∈ thickVolume hc F i}
  volume := thickVolume hc F i
  domain_definable := thickDomain_predicate F i
  volume_definable := thickVolume_definable F i
  bound := F.bound + F.bound * N

end Thickening

/-! ### Validity of the thickened schema -/
section ThickeningValidity
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

theorem thickPadGraph_functional {w : Fin (thickC hc B) → M} {s t : M}
    (hs : Fin.append w (fun _ : Fin 1 => s) ∈ thickPadGraph hc B)
    (ht : Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B) : s = t := by
  obtain ⟨u,hu,hv⟩ := (nativeWeakRVLabelGraph_append_iff _ _ _).mp hs
  obtain ⟨u',hu',hv'⟩ := (nativeWeakRVLabelGraph_append_iff _ _ _).mp ht
  have he : u = u' := Subtype.ext (rvValues_injective (hu.trans hu'.symm))
  subst he
  exact (congrFun hv 0).symm.trans (congrFun hv' 0)

theorem thickPadGraph_proper {w : Fin (thickC hc B) → M} {s : M}
    (hs : Fin.append w (fun _ : Fin 1 => s) ∈ thickPadGraph hc B) : (∀ j,iRV (w j)) ∧ iRV s := by
  have hp := (thickPadGraph_definable (hc := hc) (B := B)).proper _ hs
  refine ⟨fun j => ?_,?_⟩
  · simpa [sortEval,iRV] using hp (Fin.castAdd 1 j)
  · simpa [sortEval,iRV] using hp (Fin.natAdd (thickC hc B) 0)

theorem thickPadGraph_nonzero {w : Fin (thickC hc B) → M} {s : M}
    (hs : Fin.append w (fun _ : Fin 1 => s) ∈ thickPadGraph hc B) : s ≠ iRVZero := by
  obtain ⟨u,_,hv⟩ := (nativeWeakRVLabelGraph_append_iff _ _ _).mp hs
  have h := (nativeAffineRVPower hc B 1).nonzero u 0
  exact fun hs0 => h ((congrFun hv 0).trans hs0)

theorem thickRel_sorted (F : GammaFiniteRVSchema B p a k sp) (i : Fin k)
    {z : Fin p → M} {u : Fin a → M} {w : Fin (thickC hc B) → M} {y : Fin k → M}
    (h : thickRel hc F i z u w y) :
    Fin.append (Fin.append z (Fin.append u w)) y ∈ sortedUniverse (thickSort sp a (thickC hc B) k) := by
  apply (thick_sorted_iff z u w y).mpr
  rcases h with ⟨hv,_,hw⟩ | ⟨hv,hq⟩
  · have hp := F.volume_definable.proper _ hv
    refine ⟨fun j => ?_,fun j => ?_,fun j => ?_,fun j => ?_⟩
    · simpa using hp (Fin.castAdd k (Fin.castAdd a j))
    · simpa [sortEval,iRV] using hp (Fin.castAdd k (Fin.natAdd p j))
    · rw [hw j]; exact iRV_iRVZero
    · simpa [sortEval,iRV] using hp (Fin.natAdd (p+a) j)
  · have hp := F.volume_definable.proper _ hv
    have hq' := thickPadGraph_proper hq
    refine ⟨fun j => ?_,fun j => ?_,hq'.1,fun j => ?_⟩
    · simpa using hp (Fin.castAdd k (Fin.castAdd a j))
    · simpa [sortEval,iRV] using hp (Fin.castAdd k (Fin.natAdd p j))
    · by_cases hj : j = i
      · subst hj; exact hq'.2
      · have := hp (Fin.natAdd (p+a) j)
        simpa [sortEval,iRV,Function.update_of_ne hj] using this

theorem thickVolume_mem (F : GammaFiniteRVSchema B p a k sp) (i : Fin k)
    (z : Fin p → M) (u : Fin a → M) (w : Fin (thickC hc B) → M) (y : Fin k → M) :
    Fin.append (Fin.append z (Fin.append u w)) y ∈ thickVolume hc F i ↔ thickRel hc F i z u w y := by
  constructor
  · rintro ⟨_,h⟩
    simpa using h
  · intro h
    refine ⟨thickRel_sorted F i h,?_⟩
    simpa using h

theorem thickVolume_mem' (F : GammaFiniteRVSchema B p a k sp) (i : Fin k)
    (z : Fin p → M) (x : Fin (a+thickC hc B) → M) (y : Fin k → M) :
    Fin.append (Fin.append z x) y ∈ thickVolume hc F i ↔
      thickRel hc F i z (x ∘ Fin.castAdd (thickC hc B)) (x ∘ Fin.natAdd a) y := by
  have hx : x = Fin.append (x ∘ Fin.castAdd (thickC hc B)) (x ∘ Fin.natAdd a) :=
    Fin.append_castAdd_natAdd.symm
  conv_lhs => rw [hx]
  exact thickVolume_mem F i z _ _ y

theorem thickAt_valid (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) (N : ℕ)
    (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N)
    (z : Fin p → M) (hz : F.valid z) : (thickAt hc F i N).valid z := by
  obtain ⟨hzs,huniq,hdom,hfib⟩ := hz
  refine ⟨hzs,?_,?_,?_⟩
  · intro x hx
    obtain ⟨_,y,_,hy⟩ := hx
    refine ⟨y,hy,?_⟩
    intro y' hy'
    change Fin.append (Fin.append z x) y' ∈ thickVolume hc F i at hy'
    rw [thickVolume_mem'] at hy hy'
    rcases hy with ⟨hv,hi,_⟩ | ⟨hv,hq⟩ <;> rcases hy' with ⟨hv',hi',_⟩ | ⟨hv',hq'⟩
    · exact (huniq _ (hdom _ _ hv)).unique hv' hv
    · exact False.elim (hi (by
        have he := (huniq _ (hdom _ _ hv)).unique hv' hv
        rw [← he]; simp))
    · exact False.elim (hi' (by
        have he := (huniq _ (hdom _ _ hv)).unique hv' hv
        rw [he]; simp))
    · have he := (huniq _ (hdom _ _ hv)).unique hv' hv
      have hi := thickPadGraph_functional hq hq'
      funext j
      by_cases hj : j = i
      · subst hj; exact hi.symm
      · have := congrFun he j
        simpa [Function.update_of_ne hj] using this
  · intro x y hxy
    refine ⟨?_,y,?_,hxy⟩
    · intro j
      have hs := thickRel_sorted F i ((thickVolume_mem' F i z x y).mp hxy)
      have hx : x = Fin.append (x ∘ Fin.castAdd (thickC hc B)) (x ∘ Fin.natAdd a) :=
        Fin.append_castAdd_natAdd.symm
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hs (Fin.castAdd k (Fin.castAdd (a+thickC hc B) j))
      · have := hs (Fin.castAdd k (Fin.natAdd p j))
        simpa [← hx] using this
    · intro j
      have hs := thickRel_sorted F i ((thickVolume_mem' F i z x y).mp hxy)
      simpa using hs (Fin.natAdd (p+(a+thickC hc B)) j)
  · intro y hy
    have hy' : ∀ j,iRV (y j) := fun j => by simpa [sortEval,iRV] using hy j
    let y0 := Function.update y i iRVZero
    have hy0 : ∀ j,sortEval SortTag.rv (y0 j) := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa [y0,sortEval,iRV] using iRV_iRVZero
      · simpa [y0,Function.update_of_ne hj] using hy j
    obtain ⟨hf1,hn1⟩ := hfib y hy
    obtain ⟨hf2,hn2⟩ := hfib y0 hy0
    obtain ⟨hf3,hn3⟩ := hN (y i) (hy' i)
    let S1 := (fun u : Fin a → M => Fin.append u (fun _ : Fin (thickC hc B) => iRVZero)) ''
      {u | Fin.append (Fin.append z u) y ∈ F.volume}
    let S2 := (fun uw : (Fin a → M) × (Fin (thickC hc B) → M) => Fin.append uw.1 uw.2) ''
      ({u | Fin.append (Fin.append z u) y0 ∈ F.volume} ×ˢ
        {w | Fin.append w (fun _ : Fin 1 => y i) ∈ thickPadGraph hc B})
    have hsub : {x | Fin.append (Fin.append z x) y ∈ (thickAt hc F i N).volume} ⊆ S1 ∪ S2 := by
      intro x hx
      change Fin.append (Fin.append z x) y ∈ thickVolume hc F i at hx
      rw [thickVolume_mem'] at hx
      have hxe : x = Fin.append (x ∘ Fin.castAdd (thickC hc B)) (x ∘ Fin.natAdd a) :=
        Fin.append_castAdd_natAdd.symm
      rcases hx with ⟨hv,_,hw⟩ | ⟨hv,hq⟩
      · left
        refine ⟨x ∘ Fin.castAdd (thickC hc B),hv,?_⟩
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp
        · simp only [Fin.append_right]; exact (hw j).symm
      · right
        exact ⟨(x ∘ Fin.castAdd (thickC hc B),x ∘ Fin.natAdd a),⟨hv,hq⟩,hxe.symm⟩
    have hfin1 : S1.Finite := hf1.image _
    have hfin2 : S2.Finite := (hf2.prod hf3).image _
    refine ⟨(hfin1.union hfin2).subset hsub,?_⟩
    calc _ ≤ (S1 ∪ S2).ncard := Set.ncard_le_ncard hsub (hfin1.union hfin2)
      _ ≤ S1.ncard + S2.ncard := Set.ncard_union_le _ _
      _ ≤ F.bound + F.bound * N := by
        apply Nat.add_le_add
        · exact (Set.ncard_image_le hf1).trans hn1
        · refine (Set.ncard_image_le (hf2.prod hf3)).trans ?_
          rw [Set.ncard_prod]
          exact Nat.mul_le_mul hn2 hn3

end ThickeningValidity

/-! ### Iterated thickening: every label becomes nonzero -/
section ThickeningSequence
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def thickArity (a c : ℕ) : ℕ → ℕ
  | 0 => a
  | m+1 => thickArity a c m + c

/-- Thicken the labels `0,…,m-1` in turn. -/
def thickSeq (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaFiniteRVSchema B p a k sp) (N : ℕ) :
    (m : ℕ) → m ≤ k → GammaFiniteRVSchema B p (thickArity a (thickC hc B) m) k sp
  | 0,_ => F
  | m+1,h => thickAt hc (thickSeq hc F N m (Nat.le_of_succ_le h)) ⟨m,h⟩ N

theorem thickSeq_valid (F : GammaFiniteRVSchema B p a k sp) (N : ℕ)
    (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N)
    (z : Fin p → M) (hz : F.valid z) : ∀ (m : ℕ) (h : m ≤ k),(thickSeq hc F N m h).valid z
  | 0,_ => hz
  | m+1,h => thickAt_valid _ _ N hN z (thickSeq_valid F N hN z hz m (Nat.le_of_succ_le h))

theorem thickSeq_nonzero (F : GammaFiniteRVSchema B p a k sp) (N : ℕ) (z : Fin p → M) :
    ∀ (m : ℕ) (h : m ≤ k) (x : Fin (thickArity a (thickC hc B) m) → M) (y : Fin k → M),
      Fin.append (Fin.append z x) y ∈ (thickSeq hc F N m h).volume → ∀ j : Fin k,j.val < m → y j ≠ iRVZero
  | 0,_,_,_,_,j,hj => absurd hj (Nat.not_lt_zero _)
  | m+1,h,x,y,hxy,j,hj => by
    change Fin.append (Fin.append z x) y ∈ thickVolume hc (thickSeq hc F N m (Nat.le_of_succ_le h)) ⟨m,h⟩ at hxy
    rw [thickVolume_mem'] at hxy
    by_cases hjm : j = ⟨m,h⟩
    · subst hjm
      rcases hxy with ⟨_,hi,_⟩ | ⟨_,hq⟩
      · exact hi
      · exact thickPadGraph_nonzero hq
    · have hjlt : j.val < m := by
        have hne : j.val ≠ m := fun he => hjm (Fin.ext he)
        omega
      rcases hxy with ⟨hv,_,_⟩ | ⟨hv,_⟩
      · exact thickSeq_nonzero F N z m (Nat.le_of_succ_le h) _ _ hv j hjlt
      · have := thickSeq_nonzero F N z m (Nat.le_of_succ_le h) _ _ hv j hjlt
        simpa [Function.update_of_ne hjm] using this

/-- The fully thickened schema. -/
abbrev thickFull (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaFiniteRVSchema B p a k sp) (N : ℕ) :
    GammaFiniteRVSchema B p (thickArity a (thickC hc B) k) k sp :=
  thickSeq hc F N k le_rfl

theorem thickFull_strict (F : GammaFiniteRVSchema B p a k sp) (N : ℕ)
    (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N)
    (z : Fin p → M) (hz : F.valid z) : nativeFiniteRVSchemaValid (thickFull hc F N) z :=
  ⟨thickSeq_valid F N hN z hz k le_rfl,fun x y hxy j => thickSeq_nonzero F N z k le_rfl x y hxy j j.isLt⟩

end ThickeningSequence

/-! ### Row values: exact-degree strata of a finite RV schema -/
section RowStrata
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

/-- The rows on which exactly the labels in `I` are nonzero. -/
def schemaPatternDomain (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaFiniteRVSchema B p a k sp)
    (I : Finset (Fin k)) : GammaDomainFormula B p a sp :=
  ⟨{x | x ∈ sortedUniverse (Fin.append sp (fun _ : Fin a => .rv)) ∧
    ∃ y : Fin k → M,y ∈ sortedUniverse (fun _ : Fin k => SortTag.rv) ∧
      Fin.append x y ∈ F.volume ∧ nativeRVZeroPattern id I y},by
    have h1 := OriginalSortedPredicate.of_definable F.volume_definable
    have h2 := (nativeRVZeroPattern_definable (B := B) hc (id : Fin k → Fin k) I).pullback
      (t := Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin k => .rv)) (Fin.natAdd (p+a))
      (by intro j; simp)
    have h3 := (h1.conj h2).ex
    apply h3.congr
    intro x _
    constructor
    · rintro ⟨y,hy,hv,hp⟩
      refine ⟨y,hy,hv,?_⟩
      have he : Fin.append x y ∘ Fin.natAdd (p+a) = y := funext (fun j => Fin.append_right _ _ j)
      rwa [he] at hp
    · rintro ⟨y,hy,hv,hp⟩
      refine ⟨y,hy,hv,?_⟩
      have he : Fin.append x y ∘ Fin.natAdd (p+a) = y := funext (fun j => Fin.append_right _ _ j)
      rwa [he]⟩

theorem schemaPatternDomain_row (F : GammaFiniteRVSchema B p a k sp) (I : Finset (Fin k))
    (z : Fin p → M) (v : Fin a → M) :
    Fin.append z v ∈ (schemaPatternDomain hc F I).val ↔
      ∃ y : Fin k → M,Fin.append (Fin.append z v) y ∈ F.volume ∧ nativeRVZeroPattern id I y := by
  constructor
  · rintro ⟨_,y,_,hv,hp⟩
    exact ⟨y,hv,hp⟩
  · rintro ⟨y,hv,hp⟩
    have hpr := F.volume_definable.proper _ hv
    refine ⟨?_,y,?_,hv,hp⟩
    · intro j
      simpa using hpr (Fin.castAdd k j)
    · intro j
      simpa using hpr (Fin.natAdd (p+a) j)

/-- The single tuple of RV zeros, as a constant domain formula. -/
def zeroConstDomain (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (sp : Fin p → SortTag) (c : ℕ) :
    GammaDomainFormula B p c sp :=
  ⟨{x | x ∈ sortedUniverse (Fin.append sp (fun _ : Fin c => .rv)) ∧ ∀ j : Fin c,x (Fin.natAdd p j) = iRVZero},
    OriginalSortedPredicate.finite_all (fun j => coord_eq_zero_predicate hc _ (Fin.natAdd p j))⟩

theorem zeroConstDomain_row {c : ℕ} (z : Fin p → M) (hz : ∀ j,sortEval (sp j) (z j)) (w : Fin c → M) :
    Fin.append z w ∈ (zeroConstDomain hc B sp c).val ↔ ∀ j,w j = iRVZero := by
  constructor
  · rintro ⟨_,h⟩ j
    simpa using h j
  · intro h
    refine ⟨?_,fun j => by simpa using h j⟩
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hz j
    · simpa [sortEval,iRV,h j] using iRV_iRVZero

end RowStrata

section RowValueAlgebra
variable {R : Type*} [CommRing R]

theorem geometricDegreeValue_add (L a b : R) (n : ℕ) :
    geometricDegreeValue L (a+b) n = geometricDegreeValue L a n + geometricDegreeValue L b n := by
  unfold geometricDegreeValue
  rw [IsLocalization.mk'_eq_mul_mk'_one,IsLocalization.mk'_eq_mul_mk'_one (x := a),
    IsLocalization.mk'_eq_mul_mk'_one (x := b),map_add,add_mul]

theorem geometricDegreeValue_zero (L : R) (n : ℕ) : geometricDegreeValue L 0 n = 0 := by
  unfold geometricDegreeValue
  simp

theorem geometricDegreeValue_affine_succ (L a : R) (n : ℕ) :
    geometricDegreeValue L (a*L) (n+1) = geometricDegreeValue L a n := by
  have h := geometricDegreeValue_affine_padding L a n 1
  rwa [pow_one,mul_comm] at h

theorem finset_sum_erase_split {S : Type*} [AddCommMonoid S] {k : ℕ} (i : Fin k)
    (φ : Finset (Fin k) → S) :
    ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin k) => i ∈ J),φ (J.erase i) =
      ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin k) => i ∉ J),φ J := by
  apply Finset.sum_nbij' (fun J => J.erase i) (fun J => insert i J)
  · intro J hJ
    simp
  · intro J hJ
    simp
  · intro J hJ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hJ
    exact Finset.insert_erase hJ
  · intro J hJ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hJ
    exact Finset.erase_insert hJ
  · intro J _
    rfl

end RowValueAlgebra

/-! ### Row values of exact-degree strata -/
section RowValues
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

theorem nativeRVSetValue_singleton (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (D0 : Base (M := M))
    (hr : Cardinal.mk D0.real < κ) (hγ : Cardinal.mk D0.gamma < κ) (hΓ : Section2.NontrivialDefinableGamma D0)
    (kind : EulerKind) {n : ℕ} (X : GammaGroundDefSet hc D0 (rawRVSpace (M := M) n))
    (x0 : Fin n → CanonicalRV.RVSort M) (hX : ∀ x,x ∈ X.carrier ↔ x = x0) :
    nativeRVSetValue h00 linear hκ hs hc D0 hr hγ hΓ kind X = 1 := by
  let U := GammaGroundRVObject.unit hc D0
  have hU : ∀ t : Fin 0 → CanonicalRV.RVSort M,t ∈ U.domain.carrier := fun t => Set.mem_univ t
  let f : GammaGroundMap X U.domain :=
    (gammaGroundRVSelectCoordinates (Fin.elim0 : Fin 0 → Fin n) X).corestrict (fun a => hU _)
  have hf : Function.Bijective f := by
    constructor
    · intro a b _
      exact Subtype.ext (((hX a.val).mp a.property).trans ((hX b.val).mp b.property).symm)
    · intro b
      refine ⟨⟨x0,(hX x0).mpr rfl⟩,Subtype.ext (funext (fun j => j.elim0))⟩
  have he := nativeRVSetValue_bijection h00 linear hκ hs hc D0 hr hγ hΓ kind X U.domain ⟨f,hf⟩
  rw [he,nativeRVSetValue_object]
  change nativeGroundRVEvaluation h00 linear hκ hs hc D0 hr hγ hΓ kind
    (of (gammaGroundRVSemiringClass (GammaGroundRVObject.unit hc D0))) = 1
  rw [gammaGroundRVSemiringClass_unit,← one_def,map_one]

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

/-- The RV[*] geometric value of the row of a finite RV schema. -/
def rowWeakValue (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) :
    RESAffineLocalization.Target ⟨B.real ∪ Set.range z,B.gamma⟩ :=
  ∑ I : Finset (Fin k),geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine ⟨B.real ∪ Set.range z,B.gamma⟩)
    (nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric (schemaPatternDomain hc F I) z) (Fintype.card I)

variable (kind : EulerKind)

theorem rowValue_congr {b : ℕ} (D D' : GammaDomainFormula B p b sp) (z : Fin p → M)
    (h : ∀ v,Fin.append z v ∈ D.val ↔ Fin.append z v ∈ D'.val) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D' z := by
  unfold nativeRVRowValue
  apply nativeRVSetValue_bijection
  apply gammaGroundBijectionOfRawDomainEq
  rw [originalRVRowDomain_raw,originalRVRowDomain_raw]
  ext v
  exact h v

theorem rowValue_empty {b : ℕ} (D : GammaDomainFormula B p b sp) (z : Fin p → M)
    (h : ∀ v,Fin.append z v ∉ D.val) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z = 0 := by
  unfold nativeRVRowValue
  apply nativeRVSetValue_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact h _ hx

theorem rowValue_split {b : ℕ} (D D1 D2 : GammaDomainFormula B p b sp) (z : Fin p → M)
    (h : ∀ v,Fin.append z v ∈ D.val ↔ Fin.append z v ∈ D1.val ∨ Fin.append z v ∈ D2.val)
    (hd : ∀ v,Fin.append z v ∈ D1.val → Fin.append z v ∉ D2.val) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D1 z +
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D2 z := by
  unfold nativeRVRowValue
  let A : Bool → GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) b) :=
    fun t => cond t (originalRVRowDomain hc D1 z) (originalRVRowDomain hc D2 z)
  have hp := nativeRVSetValue_finite_partition h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
    (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind
    (originalRVRowDomain hc D z) A (by
      intro t t' htt'
      apply Set.disjoint_left.mpr
      intro x hx hx'
      cases t <;> cases t'
      · exact htt' rfl
      · exact hd _ hx' hx
      · exact hd _ hx hx'
      · exact htt' rfl) (by
      intro x
      constructor
      · intro hx
        rcases (h _).mp hx with h1 | h2
        · exact ⟨true,h1⟩
        · exact ⟨false,h2⟩
      · rintro ⟨t,ht⟩
        cases t
        · exact (h _).mpr (Or.inr ht)
        · exact (h _).mpr (Or.inl ht))
  rw [hp,Fintype.sum_bool]
  rfl

theorem rowValue_product {b c : ℕ} (D : GammaDomainFormula B p b sp) (E : GammaDomainFormula B p c sp) (z : Fin p → M) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (originalDomainProduct D E) z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z *
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind E z := by
  unfold nativeRVRowValue
  rw [nativeRVSetValue_bijection _ _ _ _ _ _ _ _ _ _ _ _ (originalRVRowProductBijection (hc := hc) D E z),
    nativeRVSetValue_product]

theorem rowValue_zeroConst {c : ℕ} (z : Fin p → M) (hz : ∀ j,sortEval (sp j) (z j)) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (zeroConstDomain hc B sp c) z = 1 := by
  unfold nativeRVRowValue
  apply nativeRVSetValue_singleton _ _ _ _ _ _ _ _ _ _ (fun _ => 0)
  intro x
  change Fin.append z (rvValues x) ∈ (zeroConstDomain hc B sp c).val ↔ _
  rw [zeroConstDomain_row z hz]
  constructor
  · intro h
    funext j
    apply Subtype.ext
    exact (h j).trans RVOperations.zero_val.symm
  · intro h j
    rw [h]
    exact RVOperations.zero_val

/-- (R-c) On a schema with nonzero labels, the RV[*] row value is the single-degree one. -/
theorem rowWeakValue_strict (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M)
    (hv : nativeFiniteRVSchemaValid F z) :
    rowWeakValue (hc := hc) h00 linear hκ hs hr hγ hΓ F z =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine ⟨B.real ∪ Set.range z,B.gamma⟩)
        (nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric (finiteRVSchemaDomain F) z) k := by
  obtain ⟨⟨_,huniq,hdom,_⟩,hnz⟩ := hv
  have hall : ∀ v y,Fin.append (Fin.append z v) y ∈ F.volume → nativeRVZeroPattern id Finset.univ y := by
    intro v y hvy j
    simpa using hnz v y hvy j
  unfold rowWeakValue
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin k))]
  · rw [Fintype.card_coe,Finset.card_univ,Fintype.card_fin]
    congr 1
    apply rowValue_congr
    intro v
    rw [schemaPatternDomain_row]
    constructor
    · rintro ⟨y,hy,_⟩
      exact hdom v y hy
    · intro hd
      obtain ⟨y,hy,_⟩ := huniq v hd
      exact ⟨y,hy,hall v y hy⟩
  · intro I _ hI
    rw [rowValue_empty]
    · exact geometricDegreeValue_zero _ _
    · intro v hv
      obtain ⟨y,hy,hp⟩ := (schemaPatternDomain_row F I z v).mp hv
      apply hI
      ext j
      exact (hp j).trans (hall v y hy j).symm
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- (R-a) A presented RV[*] object has the row value of its schema. -/
theorem rowWeakValue_presentation (z : Fin p → M) (U : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (F : GammaFiniteRVSchema B p U.arity k sp)
    (hV : ∀ x : Fin U.arity → M,∀ y : Fin k → M,
      Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append x y ∈ nativeWeakRVLabelGraph U) :
    rowWeakValue (hc := hc) h00 linear hκ hs hr hγ hΓ F z =
      nativeWeakGeometricValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) U := by
  unfold rowWeakValue nativeWeakGeometricValue
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  unfold nativeRVRowValue
  apply nativeRVSetValue_bijection
  apply gammaGroundBijectionOfRawDomainEq
  rw [originalRVRowDomain_raw]
  ext v
  change Fin.append z v ∈ (schemaPatternDomain hc F I).val ↔ _
  rw [schemaPatternDomain_row]
  constructor
  · rintro ⟨y,hy,hp⟩
    obtain ⟨u,hu,hvol⟩ := (nativeWeakRVLabelGraph_append_iff U _ y).mp ((hV v y).mp hy)
    exact ⟨u.val,(weakZeroPatternDomain_mem U I u).mpr (hvol ▸ hp),hu⟩
  · rintro ⟨u,hu,rfl⟩
    have hu' := weakZeroPatternDomain_subset U I hu
    refine ⟨rvValues (U.volume ⟨u,hu'⟩).val,(hV _ _).mpr ?_,
      (weakZeroPatternDomain_mem U I ⟨u,hu'⟩).mp hu⟩
    exact (nativeWeakRVLabelGraph_append_iff U _ _).mpr ⟨⟨u,hu'⟩,rfl,rfl⟩

end RowValues

/-! ### Thickening preserves the RV[*] row value -/
section ThickRowValues
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

theorem rawDomain_pad_iff (w : Fin (thickC hc B) → M) :
    w ∈ rawDomain (nativeAffineRVPower hc B 1).domain ↔ ∃ t : M,Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B := by
  constructor
  · rintro ⟨q,hq,rfl⟩
    refine ⟨rvValues ((nativeAffineRVPower hc B 1).volume ⟨q,hq⟩).val 0,?_⟩
    refine (nativeWeakRVLabelGraph_append_iff _ _ _).mpr ⟨⟨q,hq⟩,rfl,?_⟩
    funext j
    rw [Fin.fin_one_eq_zero j]
    rfl
  · rintro ⟨t,ht⟩
    obtain ⟨u,hu,_⟩ := (nativeWeakRVLabelGraph_append_iff _ _ _).mp ht
    exact ⟨u.val,u.property,hu⟩

theorem thickAt_pattern_row (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) (N : ℕ)
    (z : Fin p → M) (hz : ∀ j,sortEval (sp j) (z j)) (J : Finset (Fin k)) (hiJ : i ∈ J)
    (v : Fin (a+thickC hc B) → M) :
    Fin.append z v ∈ (schemaPatternDomain hc (thickAt hc F i N) J).val ↔
      Fin.append z v ∈ (originalDomainProduct (schemaPatternDomain hc F J) (zeroConstDomain hc B sp (thickC hc B))).val ∨
      Fin.append z v ∈ (originalPaddedRVDomain hc (schemaPatternDomain hc F (J.erase i)) 1).val := by
  unfold originalPaddedRVDomain
  rw [schemaPatternDomain_row,originalDomainProduct_row,originalDomainProduct_row,schemaPatternDomain_row,
    schemaPatternDomain_row,zeroConstDomain_row z hz,originalConstantRVDomain_row _ _ z hz,rawDomain_pad_iff]
  constructor
  · rintro ⟨y,hrel,hp⟩
    change Fin.append (Fin.append z v) y ∈ thickVolume hc F i at hrel
    rw [thickVolume_mem'] at hrel
    rcases hrel with ⟨hv,_,hw⟩ | ⟨hv,hq⟩
    · exact Or.inl ⟨⟨y,hv,hp⟩,hw⟩
    · refine Or.inr ⟨⟨Function.update y i iRVZero,hv,?_⟩,⟨y i,hq⟩⟩
      intro j
      change j ∈ J.erase i ↔ Function.update y i iRVZero j ≠ iRVZero
      have hpj : j ∈ J ↔ y j ≠ iRVZero := hp j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Finset.mem_erase,Function.update_of_ne hj]
        exact ⟨fun h => hpj.mp h.2,fun h => ⟨hj,hpj.mpr h⟩⟩
  · rintro (⟨⟨y,hv,hp⟩,hw⟩ | ⟨⟨y0,hv,hp0⟩,⟨t,ht⟩⟩)
    · refine ⟨y,?_,hp⟩
      change Fin.append (Fin.append z v) y ∈ thickVolume hc F i
      rw [thickVolume_mem']
      exact Or.inl ⟨hv,(hp i).mp hiJ,hw⟩
    · have hy0i : y0 i = iRVZero := by
        by_contra hne
        exact (by simp : i ∉ J.erase i) ((hp0 i).mpr hne)
      refine ⟨Function.update y0 i t,?_,?_⟩
      · change Fin.append (Fin.append z v) (Function.update y0 i t) ∈ thickVolume hc F i
        rw [thickVolume_mem']
        refine Or.inr ⟨?_,by simpa using ht⟩
        rw [Function.update_idem,← hy0i,Function.update_eq_self]
        exact hv
      · intro j
        change j ∈ J ↔ Function.update y0 i t j ≠ iRVZero
        have hpj : j ∈ J.erase i ↔ y0 j ≠ iRVZero := hp0 j
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self]
          exact ⟨fun _ => thickPadGraph_nonzero ht,fun _ => hiJ⟩
        · rw [Function.update_of_ne hj,← hpj,Finset.mem_erase]
          exact ⟨fun h => ⟨hj,h⟩,fun h => h.2⟩

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem thickAt_pattern_value (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) (N : ℕ)
    (z : Fin p → M) (hz : F.valid z) (kind : EulerKind) (J : Finset (Fin k)) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (schemaPatternDomain hc (thickAt hc F i N) J) z =
      if i ∈ J then nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (schemaPatternDomain hc F J) z +
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (schemaPatternDomain hc F (J.erase i)) z *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M))
      else 0 := by
  obtain ⟨hzs,huniq,hdom,_⟩ := hz
  split_ifs with hiJ
  · rw [rowValue_split h00 linear hκ hs hr hγ hΓ kind _ _ _ z (thickAt_pattern_row F i N z hzs J hiJ),
      rowValue_product,rowValue_zeroConst h00 linear hκ hs hr hγ hΓ kind z hzs,mul_one,
      nativePaddedRV_row_value h00 linear hκ hs hr hγ hΓ kind _ 1 z hzs,pow_one]
    intro v h1 h2
    unfold originalPaddedRVDomain at h2
    rw [originalDomainProduct_row,schemaPatternDomain_row] at h1 h2
    obtain ⟨⟨y,hy,hp⟩,_⟩ := h1
    obtain ⟨⟨y0,hy0,hp0⟩,_⟩ := h2
    have he := (huniq _ (hdom _ _ hy)).unique hy hy0
    subst he
    exact (by simp : i ∉ J.erase i) ((hp0 i).mpr ((hp i).mp hiJ))
  · apply rowValue_empty
    intro v hv
    obtain ⟨y,hrel,hp⟩ := (schemaPatternDomain_row _ J z v).mp hv
    change Fin.append (Fin.append z v) y ∈ thickVolume hc F i at hrel
    rw [thickVolume_mem'] at hrel
    have hyi : y i ≠ iRVZero := by
      rcases hrel with ⟨_,hi,_⟩ | ⟨_,hq⟩
      · exact hi
      · exact thickPadGraph_nonzero hq
    exact hiJ ((hp i).mpr hyi)

/-- (R-b) Thickening one label does not change the RV[*] row value. -/
theorem rowWeakValue_thickAt (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) (N : ℕ)
    (z : Fin p → M) (hz : F.valid z) :
    rowWeakValue (hc := hc) h00 linear hκ hs hr hγ hΓ (thickAt hc F i N) z =
      rowWeakValue (hc := hc) h00 linear hκ hs hr hγ hΓ F z := by
  let L := RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M))
  let v : Finset (Fin k) → RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩ := fun J =>
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric (schemaPatternDomain hc F J) z
  let φ : Finset (Fin k) → RESAffineLocalization.Target ⟨B.real ∪ Set.range z,B.gamma⟩ := fun J =>
    geometricDegreeValue L (v J) (Fintype.card J)
  unfold rowWeakValue
  simp only [thickAt_pattern_value h00 linear hκ hs hr hγ hΓ F i N z hz]
  have hstep : ∀ J : Finset (Fin k),geometricDegreeValue L (if i ∈ J then v J + v (J.erase i) * L else 0)
      (Fintype.card J) = if i ∈ J then φ J + φ (J.erase i) else 0 := by
    intro J
    split_ifs with hiJ
    · rw [geometricDegreeValue_add]
      congr 1
      have hc : Fintype.card J = Fintype.card (J.erase i) + 1 := by
        simp only [Fintype.card_coe]
        exact (Finset.card_erase_add_one hiJ).symm
      rw [hc,geometricDegreeValue_affine_succ]
    · exact geometricDegreeValue_zero _ _
  change ∑ J,geometricDegreeValue L (if i ∈ J then v J + v (J.erase i) * L else 0) (Fintype.card J) = ∑ J,φ J
  simp only [hstep]
  rw [← Finset.sum_filter,Finset.sum_add_distrib,finset_sum_erase_split i φ]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

end ThickRowValues

/-! ### Iterated row values -/
section ThickSeqRowValues
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem rowWeakValue_thickSeq (F : GammaFiniteRVSchema B p a k sp) (N : ℕ)
    (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N)
    (z : Fin p → M) (hz : F.valid z) : ∀ (m : ℕ) (h : m ≤ k),
      rowWeakValue (hc := hc) h00 linear hκ hs hr hγ hΓ (thickSeq hc F N m h) z =
        rowWeakValue (hc := hc) h00 linear hκ hs hr hγ hΓ F z
  | 0,_ => rfl
  | m+1,h => (rowWeakValue_thickAt h00 linear hκ hs hr hγ hΓ _ _ N z
      (thickSeq_valid F N hN z hz m (Nat.le_of_succ_le h))).trans
        (rowWeakValue_thickSeq F N hN z hz m (Nat.le_of_succ_le h))

/-- The single-degree value of the full thickening is the RV[*] row value. -/
theorem thickFull_row_value (F : GammaFiniteRVSchema B p a k sp) (N : ℕ)
    (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N)
    (z : Fin p → M) (hz : F.valid z) :
    geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine ⟨B.real ∪ Set.range z,B.gamma⟩)
        (nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric (finiteRVSchemaDomain (thickFull hc F N)) z) k =
      rowWeakValue (hc := hc) h00 linear hκ hs hr hγ hΓ F z :=
  (rowWeakValue_strict h00 linear hκ hs hr hγ hΓ _ z (thickFull_strict F N hN z hz)).symm.trans
    (rowWeakValue_thickSeq h00 linear hκ hs hr hγ hΓ F N hN z hz k le_rfl)

end ThickSeqRowValues

/-! ### The VF side of one thickening step -/
section ThickVF
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p r a k : ℕ}

theorem rvValues_append' {m n : ℕ} (u : Fin m → CanonicalRV.RVSort M) (w : Fin n → CanonicalRV.RVSort M) :
    rvValues (Fin.append u w) = Fin.append (rvValues u) (rvValues w) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [rvValues]

theorem rvValues_tupleRV_update {n : ℕ} (y : Fin n → Section2.VF M) (i : Fin n) :
    rvValues (Section2.tupleRV M (Function.update y i 0)) =
      Function.update (rvValues (Section2.tupleRV M y)) i iRVZero := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact (rvValues_tupleRV_zero_iff _ j).mpr (by simp)
  · rw [Function.update_of_ne hj]
    simp [rvValues,Section2.tupleRV,Function.update_of_ne hj]

theorem rvValues_tupleRV_update_val {n : ℕ} (y : Fin n → Section2.VF M) (i : Fin n) (x : Section2.VF M) :
    rvValues (Section2.tupleRV M (Function.update y i x)) i = rvValues (Section2.tupleRV M (fun _ : Fin 1 => x)) 0 := by
  simp [rvValues,Section2.tupleRV]

theorem mixed_eta {n m s t : ℕ} (ξ : Section2.Mixed M (n+m) (s+t)) :
    ξ = (Fin.append (ξ.1 ∘ Fin.castAdd m) (ξ.1 ∘ Fin.natAdd n),Fin.append (ξ.2 ∘ Fin.castAdd t) (ξ.2 ∘ Fin.natAdd s)) :=
  Prod.ext Fin.append_castAdd_natAdd.symm Fin.append_castAdd_natAdd.symm

variable (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p r))
variable (F : GammaFiniteRVSchema B (p+r) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin r => .rv)))

theorem thickLift_mem (i : Fin k) (N : ℕ) (b : Fin p → Section2.VF M) (v : Fin r → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) (w : Fin (thickC hc B) → CanonicalRV.RVSort M) :
    (Fin.append b y,Fin.append v (Fin.append u w)) ∈ (nativeVFLiftFamily Z (thickAt hc F i N)).carrier ↔
      (b,v) ∈ Z.carrier ∧ thickRel hc F i (nativeMixedCode (b,v)) (rvValues u) (rvValues w)
        (rvValues (Section2.tupleRV M y)) := by
  rw [nativeVFLiftFamily_mem,rvValues_append']
  exact and_congr Iff.rfl (thickVolume_mem F i _ _ _ _)

/-- The two strata of the old lift family according to the VF coordinate `i`. -/
def thickXs (i : Fin k) (t : Bool) : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (r+a)) :=
  nativeVFSelectedZeroStratum (nativeVFLiftFamily Z F) (fun _ : Fin 1 => Fin.natAdd p i)
    (if t then Finset.univ else ∅)

theorem thickXs_mem (i : Fin k) (t : Bool) (ξ : Section2.Mixed M (p+k) (r+a)) :
    ξ ∈ (thickXs Z F i t).carrier ↔ ξ ∈ (nativeVFLiftFamily Z F).carrier ∧ (ξ.1 (Fin.natAdd p i) ≠ 0 ↔ t = true) := by
  rw [thickXs,nativeVFSelectedZeroStratum_mem]
  cases t <;> simp

theorem nativeVFClass_two_partition (A : GammaGroundFiniteVFObject hc B)
    (D1 D2 : GammaGroundDefSet hc B (rawMixedSpace (M := M) A.vfArity A.rvArity))
    (hd : Disjoint D1.carrier D2.carrier)
    (hcov : ∀ x,x ∈ A.domain.carrier ↔ x ∈ D1.carrier ∨ x ∈ D2.carrier) :
    nativeVFClass A = nativeVFClass (A.restrict D1 (fun x hx => (hcov x).mpr (Or.inl hx))) +
      nativeVFClass (A.restrict D2 (fun x hx => (hcov x).mpr (Or.inr hx))) := by
  have h := nativeVFClass_finite_partition A (fun t : Bool => cond t D1 D2) (by
    intro t t' htt'
    cases t <;> cases t'
    · exact absurd rfl htt'
    · exact hd.symm
    · exact hd
    · exact absurd rfl htt') (by
    intro x
    rw [hcov]
    constructor
    · rintro (h | h)
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    · rintro ⟨t,ht⟩
      cases t
      · exact Or.inr ht
      · exact Or.inl ht)
  rw [h,Fintype.sum_bool]
  rfl

end ThickVF

section ThickVFMaps
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p r a k : ℕ}
variable (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p r))
variable (F : GammaFiniteRVSchema B (p+r) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin r => .rv)))
variable (i : Fin k) (N : ℕ)
variable (hfX : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFLiftFamily Z F).carrier}.Finite)

/-- The zero stratum of the coordinate `i`, as a finite VF object. -/
def thickXfObj : GammaGroundFiniteVFObject hc B :=
  ⟨p+k,r+a,thickXs Z F i false,fun x => (hfX x).subset (fun _ ht => nativeVFSelectedZeroStratum_subset _ _ _ ht)⟩

/-- The zero stratum times the lift `𝒪^× ⊔ (1+𝔪)` of the padding object. -/
def thickPr : GammaGroundFiniteVFObject hc B :=
  (thickXfObj Z F i hfX).product (gammaGroundObjectLiftFinite (nativeAffineRVPower hc B 1))

def thickJV : Fin (p+k) → Fin ((p+k)+1) :=
  fun m => if m = Fin.natAdd p i then Fin.natAdd (p+k) 0 else Fin.castAdd 1 m

def thickHR : Fin (r+(a+thickC hc B)) → Fin ((r+a)+thickC hc B) :=
  Fin.cast (Nat.add_assoc r a (thickC hc B)).symm

/-- Reinsert the padding VF coordinate in position `i` and reassociate the RV coordinates. -/
def thickPhi : GammaGroundMap (thickPr Z F i hfX).domain
    (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) (p+k) (r+(a+thickC hc B)))) :=
  nativeMixedCoordinateMap (thickPr Z F i hfX).domain (thickJV (p := p) i) (thickHR (hc := hc) (B := B) (r := r) (a := a))

theorem thickJV_comp (π1 : Fin ((p+k)+1) → Section2.VF M) :
    π1 ∘ thickJV (p := p) i = Fin.append (π1 ∘ Fin.castAdd 1 ∘ Fin.castAdd k)
      (Function.update (π1 ∘ Fin.castAdd 1 ∘ Fin.natAdd p) i (π1 (Fin.natAdd (p+k) 0))) := by
  funext m
  refine Fin.addCases (fun m => ?_) (fun j => ?_) m
  · have hne : Fin.castAdd k m ≠ Fin.natAdd p i := by
      intro h
      have := congrArg Fin.val h
      simp at this
      try omega
    simp [thickJV,hne]
  · by_cases hj : j = i
    · subst hj; simp [thickJV]
    · have hne : Fin.natAdd p j ≠ Fin.natAdd p i := by
        intro h
        apply hj
        apply Fin.ext
        have := congrArg Fin.val h
        simp at this
        try omega
      simp [thickJV,hne,Function.update_of_ne hj]

theorem thickHR_comp {α : Type} (π2 : Fin ((r+a)+thickC hc B) → α) :
    π2 ∘ thickHR (hc := hc) (B := B) (r := r) (a := a) = Fin.append (π2 ∘ Fin.castAdd (thickC hc B) ∘ Fin.castAdd a)
      (Fin.append (π2 ∘ Fin.castAdd (thickC hc B) ∘ Fin.natAdd r) (π2 ∘ Fin.natAdd (r+a))) := by
  funext m
  refine Fin.addCases (fun m => ?_) (fun j => ?_) m
  · simp only [Function.comp_apply,Fin.append_left,thickHR]
    congr 1
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply,Fin.append_left,Fin.append_right,thickHR]
      congr 1
    · simp only [Function.comp_apply,Fin.append_right,thickHR]
      congr 1
      exact Fin.ext (by simp; omega)

theorem thickPr_mem (π : Section2.Mixed M ((p+k)+1) ((r+a)+thickC hc B)) :
    π ∈ (thickPr Z F i hfX).domain.carrier ↔
      (π.1 ∘ Fin.castAdd 1,π.2 ∘ Fin.castAdd (thickC hc B)) ∈ (thickXs Z F i false).carrier ∧
      (π.1 ∘ Fin.natAdd (p+k),π.2 ∘ Fin.natAdd (r+a)) ∈ (gammaGroundObjectLift (nativeAffineRVPower hc B 1)).carrier :=
  mem_gammaGroundMixedProductDomain _ _ π

theorem thickPhi_injective : Function.Injective (thickPhi Z F i hfX) := by
  intro π π' h
  have h' := congrArg Subtype.val h
  rw [thickPhi,nativeMixedCoordinateMap_value,nativeMixedCoordinateMap_value] at h'
  have h1 := congrArg Prod.fst h'
  have h2 := congrArg Prod.snd h'
  simp only at h1 h2
  have hz : ∀ ρ : (thickPr Z F i hfX).domain,ρ.val.1 (Fin.castAdd 1 (Fin.natAdd p i)) = 0 := by
    intro ρ
    have hm := ((thickXs_mem Z F i false _).mp ((thickPr_mem Z F i hfX ρ.val).mp ρ.property).1).2
    by_contra hne
    exact absurd (hm.mp hne) (by simp)
  apply Subtype.ext
  apply Prod.ext
  · have key : ∀ m : Fin ((p+k)+1),π.val.1 m = π'.val.1 m := by
      intro m
      refine Fin.addCases (fun m => ?_) (fun j => ?_) m
      · by_cases hm : m = Fin.natAdd p i
        · subst hm
          exact (hz π).trans (hz π').symm
        · have := congrFun h1 m
          simp only [Function.comp_apply,thickJV,hm,ite_false] at this
          exact this
      · have hj : j = 0 := Fin.fin_one_eq_zero j
        subst hj
        have := congrFun h1 (Fin.natAdd p i)
        simp only [Function.comp_apply,thickJV,ite_true] at this
        exact this
    exact funext key
  · have key : ∀ m : Fin ((r+a)+thickC hc B),π.val.2 m = π'.val.2 m := by
      intro m
      have := congrFun h2 (Fin.cast (Nat.add_assoc r a (thickC hc B)) m)
      simp only [Function.comp_apply,thickHR,Fin.cast_eq_self] at this
      exact this
    exact funext key

/-- The second branch of the thickened relation. -/
theorem thickPhi_rel (π : (thickPr Z F i hfX).domain) (b : Fin p → Section2.VF M) (v : Fin r → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) (w : Fin (thickC hc B) → CanonicalRV.RVSort M)
    (he : (thickPhi Z F i hfX π).val = (Fin.append b y,Fin.append v (Fin.append u w))) :
    (b,v) ∈ Z.carrier ∧
      Fin.append (Fin.append (nativeMixedCode (b,v)) (rvValues u))
        (Function.update (rvValues (Section2.tupleRV M y)) i iRVZero) ∈ F.volume ∧
      Fin.append (rvValues w) (fun _ : Fin 1 => rvValues (Section2.tupleRV M y) i) ∈ thickPadGraph hc B := by
  obtain ⟨hX,hQ⟩ := (thickPr_mem Z F i hfX π.val).mp π.property
  rw [thickPhi,nativeMixedCoordinateMap_value,thickJV_comp,thickHR_comp] at he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only at h1 h2
  have hb : π.val.1 ∘ Fin.castAdd 1 ∘ Fin.castAdd k = b := by
    funext m; have := congrFun h1 (Fin.castAdd k m); simpa using this
  have hy : Function.update (π.val.1 ∘ Fin.castAdd 1 ∘ Fin.natAdd p) i (π.val.1 (Fin.natAdd (p+k) (0 : Fin 1))) = y := by
    funext m; have := congrFun h1 (Fin.natAdd p m); simpa using this
  have hv : π.val.2 ∘ Fin.castAdd (thickC hc B) ∘ Fin.castAdd a = v := by
    funext m; have := congrFun h2 (Fin.castAdd (a+thickC hc B) m); simpa using this
  have hu : π.val.2 ∘ Fin.castAdd (thickC hc B) ∘ Fin.natAdd r = u := by
    funext m; have := congrFun h2 (Fin.natAdd r (Fin.castAdd (thickC hc B) m)); simpa using this
  have hw : π.val.2 ∘ Fin.natAdd (r+a) = w := by
    funext m; have := congrFun h2 (Fin.natAdd r (Fin.natAdd a m)); simpa using this
  obtain ⟨hXl,hzero⟩ := (thickXs_mem Z F i false _).mp hX
  have hy0 : π.val.1 (Fin.castAdd 1 (Fin.natAdd p i)) = 0 := by
    by_contra hne
    exact absurd (hzero.mp hne) (by simp)
  rw [mixed_eta (π.val.1 ∘ Fin.castAdd 1,π.val.2 ∘ Fin.castAdd (thickC hc B))] at hXl
  rw [nativeVFLiftFamily_mem] at hXl
  have hb' : (π.val.1 ∘ Fin.castAdd 1,π.val.2 ∘ Fin.castAdd (thickC hc B)).1 ∘ Fin.castAdd k = b := hb
  have hv' : (π.val.1 ∘ Fin.castAdd 1,π.val.2 ∘ Fin.castAdd (thickC hc B)).2 ∘ Fin.castAdd a = v := hv
  rw [hb',hv'] at hXl
  refine ⟨hXl.1,?_,?_⟩
  · have hyy : (π.val.1 ∘ Fin.castAdd 1,π.val.2 ∘ Fin.castAdd (thickC hc B)).1 ∘ Fin.natAdd p =
        Function.update y i 0 := by
      rw [← hy]
      funext m
      by_cases hm : m = i
      · subst hm; simpa using hy0
      · simp [Function.update_of_ne hm]
    have huu : (π.val.1 ∘ Fin.castAdd 1,π.val.2 ∘ Fin.castAdd (thickC hc B)).2 ∘ Fin.natAdd r = u := hu
    rw [hyy,huu,rvValues_tupleRV_update] at hXl
    exact hXl.2
  · obtain ⟨q0,hq0,hvol⟩ := (mem_gammaGroundObjectLift _ _).mp hQ
    refine (nativeWeakRVLabelGraph_append_iff _ _ _).mpr ⟨q0,?_,?_⟩
    · rw [← hw]; exact congrArg rvValues hq0
    · funext m
      have hm : m = 0 := Fin.fin_one_eq_zero m
      subst hm
      have h0 := congrArg (fun f => rvValues f 0) hvol
      simp only at h0
      refine h0.trans ?_
      rw [← hy]
      simp [rvValues,Section2.tupleRV]

theorem thickPhi_mem (π : (thickPr Z F i hfX).domain) :
    (thickPhi Z F i hfX π).val ∈ (nativeVFLiftFamily Z (thickAt hc F i N)).carrier := by
  set ξ : Section2.Mixed M (p+k) (r+(a+thickC hc B)) := (thickPhi Z F i hfX π).val with hξ
  have he' : ξ = (Fin.append (ξ.1 ∘ Fin.castAdd k) (ξ.1 ∘ Fin.natAdd p),
      Fin.append (ξ.2 ∘ Fin.castAdd (a+thickC hc B)) (Fin.append ((ξ.2 ∘ Fin.natAdd r) ∘ Fin.castAdd (thickC hc B))
        ((ξ.2 ∘ Fin.natAdd r) ∘ Fin.natAdd a))) := by
    apply Prod.ext
    · exact Fin.append_castAdd_natAdd.symm
    · funext m
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp
      · refine Fin.addCases (fun m => ?_) (fun m => ?_) m <;> simp
  obtain ⟨hZ,hV,hP⟩ := thickPhi_rel Z F i hfX π _ _ _ _ _ (hξ ▸ he')
  rw [he',thickLift_mem]
  exact ⟨hZ,Or.inr ⟨hV,hP⟩⟩

end ThickVFMaps

section ThickVFStep
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p r a k : ℕ}
variable (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p r))
variable (F : GammaFiniteRVSchema B (p+r) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin r => .rv)))
variable (i : Fin k) (N : ℕ)
variable (hfX : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFLiftFamily Z F).carrier}.Finite)

theorem thick_eta (ξ : Section2.Mixed M (p+k) (r+(a+thickC hc B))) :
    ξ = (Fin.append (ξ.1 ∘ Fin.castAdd k) (ξ.1 ∘ Fin.natAdd p),
      Fin.append (ξ.2 ∘ Fin.castAdd (a+thickC hc B)) (Fin.append ((ξ.2 ∘ Fin.natAdd r) ∘ Fin.castAdd (thickC hc B))
        ((ξ.2 ∘ Fin.natAdd r) ∘ Fin.natAdd a))) := by
  apply Prod.ext
  · exact Fin.append_castAdd_natAdd.symm
  · funext m
    refine Fin.addCases (fun m => ?_) (fun m => ?_) m
    · simp
    · refine Fin.addCases (fun m => ?_) (fun m => ?_) m <;> simp

theorem thickCase2_mem_image (b : Fin p → Section2.VF M) (v : Fin r → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) (w : Fin (thickC hc B) → CanonicalRV.RVSort M)
    (hZ : (b,v) ∈ Z.carrier)
    (hV : Fin.append (Fin.append (nativeMixedCode (b,v)) (rvValues u))
      (Function.update (rvValues (Section2.tupleRV M y)) i iRVZero) ∈ F.volume)
    (hP : Fin.append (rvValues w) (fun _ : Fin 1 => rvValues (Section2.tupleRV M y) i) ∈ thickPadGraph hc B) :
    (Fin.append b y,Fin.append v (Fin.append u w)) ∈ (thickPhi Z F i hfX).image.carrier := by
  let π0 : Section2.Mixed M ((p+k)+1) ((r+a)+thickC hc B) :=
    (Fin.append (Fin.append b (Function.update y i 0)) (fun _ : Fin 1 => y i),Fin.append (Fin.append v u) w)
  have hX : (π0.1 ∘ Fin.castAdd 1,π0.2 ∘ Fin.castAdd (thickC hc B)) ∈ (thickXs Z F i false).carrier := by
    have h1 : π0.1 ∘ Fin.castAdd 1 = Fin.append b (Function.update y i 0) := by funext m; simp [π0]
    have h2 : π0.2 ∘ Fin.castAdd (thickC hc B) = Fin.append v u := by funext m; simp [π0]
    rw [h1,h2,thickXs_mem,nativeVFLiftFamily_mem,rvValues_tupleRV_update]
    refine ⟨⟨hZ,hV⟩,?_⟩
    simp
  have hQ : (π0.1 ∘ Fin.natAdd (p+k),π0.2 ∘ Fin.natAdd (r+a)) ∈
      (gammaGroundObjectLift (nativeAffineRVPower hc B 1)).carrier := by
    obtain ⟨q0,hq,hvol⟩ := (nativeWeakRVLabelGraph_append_iff _ _ _).mp hP
    refine (mem_gammaGroundObjectLift _ _).mpr ⟨q0,?_,?_⟩
    · apply rvValues_injective
      rw [hq]
      funext m; simp [π0,rvValues]
    · apply rvValues_injective
      refine hvol.trans ?_
      funext m
      simp [π0,rvValues,Section2.tupleRV]
  refine ⟨⟨π0,(thickPr_mem Z F i hfX π0).mpr ⟨hX,hQ⟩⟩,?_⟩
  change ((thickPhi Z F i hfX) ⟨π0,_⟩).val = _
  rw [thickPhi,nativeMixedCoordinateMap_value,thickJV_comp,thickHR_comp]
  apply Prod.ext
  · simp only
    congr 1
    · funext m; simp [π0]
    · funext m
      by_cases hm : m = i
      · subst hm; simp [π0]
      · simp [π0,Function.update_of_ne hm]
  · simp only
    congr 1
    · funext m; simp [π0]
    · congr 1 <;> (funext m; simp [π0])

/-- The complement of the second branch. -/
def thickX1 : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (r+(a+thickC hc B))) :=
  (nativeVFLiftFamily Z (thickAt hc F i N)).sdiff (thickPhi Z F i hfX).image

theorem thickX1_case1 (b : Fin p → Section2.VF M) (v : Fin r → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) (w : Fin (thickC hc B) → CanonicalRV.RVSort M)
    (h : (Fin.append b y,Fin.append v (Fin.append u w)) ∈ (thickX1 Z F i N hfX).carrier) :
    (b,v) ∈ Z.carrier ∧ Fin.append (Fin.append (nativeMixedCode (b,v)) (rvValues u)) (rvValues (Section2.tupleRV M y)) ∈ F.volume ∧
      rvValues (Section2.tupleRV M y) i ≠ iRVZero ∧ w = fun _ => 0 := by
  obtain ⟨hp,hn⟩ := h
  obtain ⟨hZ,hrel⟩ := (thickLift_mem Z F i N b v y u w).mp hp
  rcases hrel with ⟨hV,hi,hw⟩ | ⟨hV,hP⟩
  · refine ⟨hZ,hV,hi,?_⟩
    funext m
    apply Subtype.ext
    exact (hw m).trans RVOperations.zero_val.symm
  · exact False.elim (hn (thickCase2_mem_image Z F i hfX b v y u w hZ hV hP))

def thickDrop : Fin (r+a) → Fin (r+(a+thickC hc B)) :=
  Fin.append (fun j => Fin.castAdd (a+thickC hc B) j) (fun j => Fin.natAdd r (Fin.castAdd (thickC hc B) j))

/-- Forget the padding coordinates on the first branch. -/
def thickPsi : GammaGroundMap (thickX1 Z F i N hfX)
    (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) (p+k) (r+a))) :=
  nativeMixedCoordinateMap (thickX1 Z F i N hfX) id (thickDrop (hc := hc) (B := B) (r := r) (a := a))

theorem thickDrop_comp {α : Type} (v : Fin r → α) (u : Fin a → α) (w : Fin (thickC hc B) → α) :
    Fin.append v (Fin.append u w) ∘ thickDrop (hc := hc) (B := B) (r := r) (a := a) = Fin.append v u := by
  funext m
  refine Fin.addCases (fun m => ?_) (fun m => ?_) m <;> simp [thickDrop]

theorem thickPsi_value (ρ : thickX1 Z F i N hfX) :
    ((thickPsi Z F i N hfX) ρ).val = (ρ.val.1,Fin.append (ρ.val.2 ∘ Fin.castAdd (a+thickC hc B))
      ((ρ.val.2 ∘ Fin.natAdd r) ∘ Fin.castAdd (thickC hc B))) := by
  rw [thickPsi,nativeMixedCoordinateMap_value]
  have he := thick_eta (k := k) ρ.val
  apply Prod.ext
  · rfl
  · simp only
    conv_lhs => rw [he]
    exact thickDrop_comp _ _ _

theorem thickPsi_injective : Function.Injective (thickPsi Z F i N hfX) := by
  intro ρ ρ' h
  have h' := congrArg Subtype.val h
  rw [thickPsi_value,thickPsi_value] at h'
  have hw : ∀ σ : thickX1 Z F i N hfX,(σ.val.2 ∘ Fin.natAdd r) ∘ Fin.natAdd a = fun _ => 0 := by
    intro σ
    have hσ := σ.property
    rw [thick_eta σ.val] at hσ
    exact (thickX1_case1 Z F i N hfX _ _ _ _ _ hσ).2.2.2
  apply Subtype.ext
  rw [thick_eta ρ.val,thick_eta ρ'.val,hw ρ,hw ρ']
  have h1 := congrArg Prod.fst h'
  have h2 := congrArg Prod.snd h'
  simp only at h1 h2
  have hv : ρ.val.2 ∘ Fin.castAdd (a+thickC hc B) = ρ'.val.2 ∘ Fin.castAdd (a+thickC hc B) := by
    funext m; have := congrFun h2 (Fin.castAdd a m); simpa using this
  have hu : (ρ.val.2 ∘ Fin.natAdd r) ∘ Fin.castAdd (thickC hc B) = (ρ'.val.2 ∘ Fin.natAdd r) ∘ Fin.castAdd (thickC hc B) := by
    funext m; have := congrFun h2 (Fin.natAdd r m); simpa using this
  rw [h1,hv,hu]

theorem thickPsi_image (hv : ∀ z ∈ nativeMixedDomain Z,F.valid z) :
    (thickPsi Z F i N hfX).image.carrier = (thickXs Z F i true).carrier := by
  ext ξ
  constructor
  · rintro ⟨ρ,rfl⟩
    show ((thickPsi Z F i N hfX) ρ).val ∈ (thickXs Z F i true).carrier
    rw [thickPsi_value]
    have hρ := ρ.property
    rw [thick_eta ρ.val] at hρ
    obtain ⟨hZ,hV,hi,_⟩ := thickX1_case1 Z F i N hfX _ _ _ _ _ hρ
    rw [thickXs_mem]
    have he : (ρ.val.1,Fin.append (ρ.val.2 ∘ Fin.castAdd (a+thickC hc B))
        ((ρ.val.2 ∘ Fin.natAdd r) ∘ Fin.castAdd (thickC hc B))) =
        (Fin.append (ρ.val.1 ∘ Fin.castAdd k) (ρ.val.1 ∘ Fin.natAdd p),Fin.append (ρ.val.2 ∘ Fin.castAdd (a+thickC hc B))
        ((ρ.val.2 ∘ Fin.natAdd r) ∘ Fin.castAdd (thickC hc B))) :=
      Prod.ext Fin.append_castAdd_natAdd.symm rfl
    rw [he,nativeVFLiftFamily_mem]
    refine ⟨⟨hZ,hV⟩,?_⟩
    simp only [Fin.append_right,iff_true]
    intro h0
    exact hi ((rvValues_tupleRV_zero_iff _ i).mpr (by simpa using h0))
  · intro hξ
    rw [mixed_eta ξ] at hξ
    obtain ⟨hX,hnz⟩ := (thickXs_mem Z F i true _).mp hξ
    rw [nativeVFLiftFamily_mem] at hX
    obtain ⟨hZ,hV⟩ := hX
    set b := ξ.1 ∘ Fin.castAdd k
    set y := ξ.1 ∘ Fin.natAdd p
    set v := ξ.2 ∘ Fin.castAdd a
    set u := ξ.2 ∘ Fin.natAdd r
    have hyi : y i ≠ 0 := by simpa [y] using hnz.mpr rfl
    have hYi : rvValues (Section2.tupleRV M y) i ≠ iRVZero := fun h => hyi ((rvValues_tupleRV_zero_iff _ i).mp h)
    let w0 : Fin (thickC hc B) → CanonicalRV.RVSort M := fun _ => 0
    have hw0 : rvValues w0 = fun _ => iRVZero := by funext m; exact RVOperations.zero_val
    have hmem : (Fin.append b y,Fin.append v (Fin.append u w0)) ∈ (thickX1 Z F i N hfX).carrier := by
      refine ⟨(thickLift_mem Z F i N b v y u w0).mpr ⟨hZ,Or.inl ⟨hV,hYi,fun m => by rw [hw0]⟩⟩,?_⟩
      rintro ⟨π,hπ⟩
      obtain ⟨_,hV2,_⟩ := thickPhi_rel Z F i hfX π b v y u w0 hπ
      have hdom := (hv _ ⟨(b,v),hZ,rfl⟩).2.2.1 _ _ hV
      have he := ((hv _ ⟨(b,v),hZ,rfl⟩).2.1 _ hdom).unique hV hV2
      have := congrFun he i
      simp at this
      exact hYi this
    refine ⟨⟨_,hmem⟩,?_⟩
    show ((thickPsi Z F i N hfX) ⟨_,hmem⟩).val = ξ
    rw [thickPsi_value]
    simp only
    conv_rhs => rw [mixed_eta ξ]
    apply Prod.ext
    · rfl
    · simp only
      congr 1 <;> (funext m; simp [v,u])

end ThickVFStep

/-! ### One thickening step preserves the geometric VF value of the lift family -/
section ThickVFValue
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M} {p r a k : ℕ}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)

theorem geometricDegreeValue_affine_one {R : Type*} [CommRing R] (L : R) :
    geometricDegreeValue L (L^1) 1 = 1 := by
  have h := geometricDegreeValue_affine_padding L 1 0 1
  rw [mul_one,zero_add] at h
  rw [h]
  unfold geometricDegreeValue
  have h1 : IsLocalization.mk' (Localization.Away L) ((⟨L^0,⟨0,rfl⟩⟩ : Submonoid.powers L) : R)
      (⟨L^0,⟨0,rfl⟩⟩ : Submonoid.powers L) = 1 := IsLocalization.mk'_self' (Localization.Away L)
  rw [← h1]
  congr 1
  simp

theorem nativeVFGeometricValue_padLift :
    nativeVFGeometricValue linear H (nativeVFClass (gammaGroundObjectLiftFinite (nativeAffineRVPower hc G.base 1))) = 1 := by
  refine (nativeVFGeometricValue_lift_class linear H (nativeAffineRVPower hc G.base 1)).trans ?_
  rw [nativeGroundGeometricRetraction_class,nativeAffineRVPower_raw_value]
  exact geometricDegreeValue_affine_one _

theorem thickAt_vf_step (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p r))
    (F : GammaFiniteRVSchema G.base (p+r) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin r => .rv)))
    (i : Fin k) (N : ℕ) (hv : ∀ z ∈ nativeMixedDomain Z,F.valid z)
    (hfX : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFLiftFamily Z F).carrier}.Finite) :
    ∃ hf : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFLiftFamily Z (thickAt hc F i N)).carrier}.Finite,
      nativeVFGeometricValue linear H (nativeVFClass
          (⟨p+k,r+(a+thickC hc G.base),nativeVFLiftFamily Z (thickAt hc F i N),hf⟩ : GammaGroundFiniteVFObject hc G.base)) =
        nativeVFGeometricValue linear H (nativeVFClass
          (⟨p+k,r+a,nativeVFLiftFamily Z F,hfX⟩ : GammaGroundFiniteVFObject hc G.base)) := by
  let Xp := nativeVFLiftFamily Z (thickAt hc F i N)
  let X2 := (thickPhi Z F i hfX).image
  let X1 := thickX1 Z F i N hfX
  have hX2 : X2.carrier ⊆ Xp.carrier := by
    rintro _ ⟨π,rfl⟩
    exact thickPhi_mem Z F i N hfX π
  let e2 : GammaGroundBijection (thickPr Z F i hfX).domain X2 :=
    ⟨(thickPhi Z F i hfX).toImage,(thickPhi Z F i hfX).toImage_bijective (thickPhi_injective Z F i hfX)⟩
  let e1 : GammaGroundBijection X1 (thickXs Z F i true) :=
    (GammaGroundBijection.ofCarrierEq (thickPsi_image Z F i N hfX hv)).comp
      ⟨(thickPsi Z F i N hfX).toImage,(thickPsi Z F i N hfX).toImage_bijective (thickPsi_injective Z F i N hfX)⟩
  have hfXt : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (thickXs Z F i true).carrier}.Finite :=
    fun x => (hfX x).subset (fun _ ht => nativeVFSelectedZeroStratum_subset _ _ _ ht)
  have hf1 := (gammaGroundFiniteRVFibres_iff e1 G.uncountable.le G.saturated G.model00 G.small_real).mpr hfXt
  have hf2 := (gammaGroundFiniteRVFibres_iff e2 G.uncountable.le G.saturated G.model00 G.small_real).mp
    (thickPr Z F i hfX).finite
  have hcov : ∀ x,x ∈ Xp.carrier ↔ x ∈ X1.carrier ∨ x ∈ X2.carrier := by
    intro x
    constructor
    · intro hx
      by_cases h2 : x ∈ X2.carrier
      · exact Or.inr h2
      · exact Or.inl ⟨hx,h2⟩
    · rintro (h1 | h2)
      · exact h1.1
      · exact hX2 h2
  have hf : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ Xp.carrier}.Finite := by
    intro x
    apply ((hf1 x).union (hf2 x)).subset
    intro t ht
    exact (hcov _).mp ht
  refine ⟨hf,?_⟩
  let XpO : GammaGroundFiniteVFObject hc G.base := ⟨p+k,r+(a+thickC hc G.base),Xp,hf⟩
  let XO : GammaGroundFiniteVFObject hc G.base := ⟨p+k,r+a,nativeVFLiftFamily Z F,hfX⟩
  have hd : Disjoint X1.carrier X2.carrier := Set.disjoint_left.mpr (fun x h1 h2 => h1.2 h2)
  have hpartP := nativeVFClass_two_partition XpO X1 X2 hd hcov
  have hcovX : ∀ x,x ∈ XO.domain.carrier ↔ x ∈ (thickXs Z F i true).carrier ∨ x ∈ (thickXs Z F i false).carrier := by
    intro x
    rw [thickXs_mem,thickXs_mem]
    constructor
    · intro hx
      by_cases h0 : x.1 (Fin.natAdd p i) = 0
      · exact Or.inr ⟨hx,by simp [h0]⟩
      · exact Or.inl ⟨hx,by simp [h0]⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdX : Disjoint (thickXs Z F i true).carrier (thickXs Z F i false).carrier := by
    apply Set.disjoint_left.mpr
    intro x h1 h2
    have a1 := ((thickXs_mem Z F i true x).mp h1).2
    have a2 := ((thickXs_mem Z F i false x).mp h2).2
    exact absurd (a2.mp (a1.mpr rfl)) (by simp)
  have hpartX := nativeVFClass_two_partition XO _ _ hdX hcovX
  have hc1 := nativeVFClass_bijection (XpO.restrict X1 (fun x hx => (hcov x).mpr (Or.inl hx)))
    (XO.restrict (thickXs Z F i true) (fun x hx => (hcovX x).mpr (Or.inl hx))) e1
  have hc2 := nativeVFClass_bijection (XpO.restrict X2 (fun x hx => (hcov x).mpr (Or.inr hx)))
    (thickPr Z F i hfX) e2.symm
  have hprod : nativeVFClass (thickPr Z F i hfX) =
      nativeVFClass (thickXfObj Z F i hfX) * nativeVFClass (gammaGroundObjectLiftFinite (nativeAffineRVPower hc G.base 1)) := by
    unfold nativeVFClass thickPr
    rw [gammaGroundVFSemiringClass_product]
    exact (of_mul_of _ _).symm
  change nativeVFGeometricValue linear H (nativeVFClass XpO) = nativeVFGeometricValue linear H (nativeVFClass XO)
  rw [hpartP,hpartX,hc1,hc2,hprod,map_add,map_add,map_mul,nativeVFGeometricValue_padLift,mul_one]
  rfl

end ThickVFValue

section ThickSeqVF
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M} {p r a k : ℕ}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)

theorem thickSeq_vf (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p r))
    (F : GammaFiniteRVSchema G.base (p+r) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin r => .rv)))
    (N : ℕ) (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc G.base}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc G.base}.ncard ≤ N)
    (hv : ∀ z ∈ nativeMixedDomain Z,F.valid z)
    (hfX : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFLiftFamily Z F).carrier}.Finite) :
    ∀ (m : ℕ) (h : m ≤ k),∃ hf : ∀ x : Fin (p+k) → Section2.VF M,
        {t | (x,t) ∈ (nativeVFLiftFamily Z (thickSeq hc F N m h)).carrier}.Finite,
      nativeVFGeometricValue linear H (nativeVFClass
          (⟨p+k,r+thickArity a (thickC hc G.base) m,nativeVFLiftFamily Z (thickSeq hc F N m h),hf⟩ :
            GammaGroundFiniteVFObject hc G.base)) =
        nativeVFGeometricValue linear H (nativeVFClass
          (⟨p+k,r+a,nativeVFLiftFamily Z F,hfX⟩ : GammaGroundFiniteVFObject hc G.base))
  | 0,_ => ⟨hfX,rfl⟩
  | m+1,h => by
    obtain ⟨hf,he⟩ := thickSeq_vf Z F N hN hv hfX m (Nat.le_of_succ_le h)
    obtain ⟨hf',he'⟩ := thickAt_vf_step linear H Z (thickSeq hc F N m (Nat.le_of_succ_le h)) ⟨m,h⟩ N
      (fun z hz => thickSeq_valid F N hN z (hv z hz) m (Nat.le_of_succ_le h)) hf
    exact ⟨hf',he'.trans he⟩

end ThickSeqVF

/-! ### Identity bijection charts -/
section IdentityCharts
variable {B : Base (M := M)} {p n : ℕ} {sp : Fin p → SortTag} {sx : Fin n → SortTag}

/-- The graph of the identity of a parameterized family. -/
def idChart (hc : CanonicalStructure.IsCanonical (M := M)) (D : Set (Fin (p+n) → M))
    (hD : DefinableOverBase B (Fin.append sp sx) D) : GammaSortedBijectionChart B sp sx sx := by
  let st := Fin.append (Fin.append sp sx) sx
  refine ⟨{w | w ∈ sortedUniverse st ∧ (w ∘ Fin.castAdd n ∈ D ∧
    ∀ j : Fin n,w (Fin.natAdd (p+n) j) = w (Fin.castAdd n (Fin.natAdd p j)))},?_⟩
  have h1 := (OriginalSortedPredicate.of_definable hD).pullback (t := st) (Fin.castAdd n) (by intro j; simp [st])
  have h2 : OriginalSortedPredicate B st
      (fun w => ∀ j : Fin n,w (Fin.natAdd (p+n) j) = w (Fin.castAdd n (Fin.natAdd p j))) := by
    apply OriginalSortedPredicate.finite_all
    intro j
    have h := parameter_free_formula_original_definable hc B st
      ((Term.var (Fin.natAdd (p+n) j)).equal (Term.var (Fin.castAdd n (Fin.natAdd p j))))
    apply OriginalSortedPredicate.congr h
    intro w _
    simp only [Formula.realize_equal,Term.realize_var]
  exact h1.conj h2

theorem idChart_valid (hc : CanonicalStructure.IsCanonical (M := M)) (D : Set (Fin (p+n) → M))
    (hD : DefinableOverBase B (Fin.append sp sx) D) (z : Fin p → M) (hz : ∀ j,sortEval (sp j) (z j)) :
    (idChart hc D hD).valid D D z := by
  have hmem : ∀ x y : Fin n → M,Fin.append (Fin.append z x) y ∈ (idChart hc D hD).carrier ↔
      Fin.append z x ∈ D ∧ y = x := by
    intro x y
    have hcomp : Fin.append (Fin.append z x) y ∘ Fin.castAdd n = Fin.append z x :=
      funext (fun j => Fin.append_left _ _ j)
    constructor
    · rintro ⟨_,hxD,heq⟩
      refine ⟨by rw [← hcomp]; exact hxD,?_⟩
      funext j
      simpa using heq j
    · rintro ⟨hxD,rfl⟩
      refine ⟨?_,by rw [hcomp]; exact hxD,fun j => by simp⟩
      have hp := hD.proper _ hxD
      intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hp j
      · simpa using hp (Fin.natAdd p j)
  refine ⟨⟨hz,?_,?_,?_⟩,?_⟩
  · intro x hx
    refine ⟨x,(hmem x x).mpr ⟨hx,rfl⟩,fun y hy => ((hmem x y).mp hy).2⟩
  · intro x y hxy
    exact ((hmem x y).mp hxy).1
  · intro y _
    have hs : {x | Fin.append (Fin.append z x) y ∈ (idChart hc D hD).carrier} ⊆ {y} := by
      intro x hx
      exact ((hmem x y).mp hx).2.symm
    exact ⟨(Set.finite_singleton y).subset hs,(Set.ncard_le_ncard hs (Set.finite_singleton y)).trans
      (by rw [Set.ncard_singleton])⟩
  · intro y
    constructor
    · intro hy
      exact ⟨y,(hmem y y).mpr ⟨hy,rfl⟩⟩
    · rintro ⟨x,hx⟩
      obtain ⟨hxD,rfl⟩ := (hmem x y).mp hx
      exact hxD

end IdentityCharts

/-! ### Complete first-order witnesses for RV[*] fibre equalities -/
section WeakGeometricSchema
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p n r m s : ℕ} {sp : Fin p → SortTag}

/-- A whole RV[*] fibre witness: both RV[<=k] schemas, both actual lift graphs, a common
degree, and the stabilized RES certificate comparing the affine-padded full thickenings. -/
structure NativeGeometricWeakVFLiftEqualitySchema (hc : CanonicalStructure.IsCanonical (M := M)) (N : ℕ)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M)) where
  leftDegree : ℕ
  leftArity : ℕ
  leftRV : GammaFiniteRVSchema B p leftArity leftDegree sp
  rightDegree : ℕ
  rightArity : ℕ
  rightRV : GammaFiniteRVSchema B p rightArity rightDegree sp
  commonDegree : ℕ
  left_le : leftDegree ≤ commonDegree
  right_le : rightDegree ≤ commonDegree
  leftLift : GammaSortedBijectionChart B sp
    (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
    (Fin.append (fun _ : Fin leftDegree => .vf) (fun _ : Fin leftArity => .rv))
  rightLift : GammaSortedBijectionChart B sp
    (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))
    (Fin.append (fun _ : Fin rightDegree => .vf) (fun _ : Fin rightArity => .rv))
  evaluation : RVEvaluationEqualitySchema hc .geometric
    (originalPaddedRVDomain hc (finiteRVSchemaDomain (thickFull hc leftRV N)) (commonDegree-leftDegree))
    (originalPaddedRVDomain hc (finiteRVSchemaDomain (thickFull hc rightRV N)) (commonDegree-rightDegree))

def NativeGeometricWeakVFLiftEqualitySchema.Valid {N : ℕ}
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeGeometricWeakVFLiftEqualitySchema (B := B) (sp := sp) hc N D E) (z : Fin p → M) : Prop :=
  W.leftRV.valid z ∧ W.rightRV.valid z ∧
    W.leftLift.valid D (finiteRVSchemaLiftDomain hc W.leftRV).val z ∧
      W.rightLift.valid E (finiteRVSchemaLiftDomain hc W.rightRV).val z ∧ W.evaluation.Valid hc z

theorem NativeGeometricWeakVFLiftEqualitySchema.valid_definable {N : ℕ}
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (W : NativeGeometricWeakVFLiftEqualitySchema (B := B) (sp := sp) hc N D E) :
    DefinableOverBase B sp {z | W.Valid z} :=
  W.leftRV.valid_definable.inter
    (W.rightRV.valid_definable.inter
      ((W.leftLift.valid_definable hD (finiteRVSchemaLiftDomain hc W.leftRV).property).inter
        ((W.rightLift.valid_definable hE (finiteRVSchemaLiftDomain hc W.rightRV).property).inter
          (W.evaluation.valid_definable hc))))

theorem native_geometric_weak_vf_lift_schema_at_parameter
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (N : ℕ) (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i))
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) n r))
    (C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) m s))
    (hA : {w | Fin.append z w ∈ D} = nativeMixedDomain A)
    (hC : {w | Fin.append z w ∈ E} = nativeMixedDomain C)
    {k l : ℕ} (U : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (V : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l)
    (H : GammaGroundBijection A (nativeWeakRVObjectLift U))
    (K : GammaGroundBijection C (nativeWeakRVObjectLift V))
    (he : nativeWeakGeometricValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) U =
      nativeWeakGeometricValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) V) :
    ∃ W : NativeGeometricWeakVFLiftEqualitySchema (B := B) (sp := sp) hc N D E,W.Valid z := by
  obtain ⟨F,hF,_,hFv⟩ := native_weak_finite_rv_schema_at_parameter hκ hs hr hγ z hz U
  obtain ⟨G,hG,_,hGv⟩ := native_weak_finite_rv_schema_at_parameter hκ hs hr hγ z hz V
  obtain ⟨HP,hHP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    D (finiteRVSchemaLiftDomain hc F).val A (nativeWeakRVObjectLift U) hA
    (finiteRVSchemaLiftDomain_presents_weak_native_lift z hz U F hFv) H
  obtain ⟨KP,hKP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    E (finiteRVSchemaLiftDomain hc G).val C (nativeWeakRVObjectLift V) hC
    (finiteRVSchemaLiftDomain_presents_weak_native_lift z hz V G hGv) K
  have hUF := rowWeakValue_presentation h00 linear hκ hs hr hγ hΓ z U F hFv
  have hVG := rowWeakValue_presentation h00 linear hκ hs hr hγ hΓ z V G hGv
  have hTF := thickFull_row_value h00 linear hκ hs hr hγ hΓ F N hN z hF
  have hTG := thickFull_row_value h00 linear hκ hs hr hγ hΓ G N hN z hG
  have heq := hTF.trans (hUF.trans (he.trans (hVG.symm.trans hTG.symm)))
  obtain ⟨N',hk,hl,hePad⟩ := (geometricRowValue_eq_iff_padded h00 linear hκ hs hr hγ hΓ
    (finiteRVSchemaDomain (thickFull hc F N)) (finiteRVSchemaDomain (thickFull hc G N)) k l z hz).mp heq
  obtain ⟨W,hW⟩ := rv_evaluation_equality_schema_at_parameter h00 linear hκ hs hr hγ hΓ .geometric
    (originalPaddedRVDomain hc (finiteRVSchemaDomain (thickFull hc F N)) (N'-k))
    (originalPaddedRVDomain hc (finiteRVSchemaDomain (thickFull hc G N)) (N'-l)) z hz hePad
  exact ⟨⟨k,U.arity,F,l,V.arity,G,N',hk,hl,HP,KP,W⟩,hF,hG,hHP,hKP,hW⟩

theorem native_geometric_weak_vf_lift_finite_catalog
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (N : ℕ)
    (X : Set (Fin p → M)) (hX : DefinableOverBase B sp X)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (hrow : ∀ z ∈ X,∃ W : NativeGeometricWeakVFLiftEqualitySchema (B := B) (sp := sp) hc N D E,W.Valid z) :
    ∃ J : Finset (NativeGeometricWeakVFLiftEqualitySchema (B := B) (sp := sp) hc N D E),
      ∀ z ∈ X,∃ W ∈ J,W.Valid z :=
  gamma_finite_witnesses hκ hs hr hγ sp X hX
    (fun W : NativeGeometricWeakVFLiftEqualitySchema (B := B) (sp := sp) hc N D E => {z | W.Valid z})
    (fun W => W.valid_definable hD hE) hrow

end WeakGeometricSchema

/-! ### Proposition 5.23 with RV[*] fibre representatives -/
section WeakGeometricFubini
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r m s p q : ℕ}

/-- The fibre hypothesis of Proposition 5.23 with representatives in RV[*]: every fibre has
RV[<=k] representatives whose normalized geometric values agree. -/
def NativeGeometricWeakVFFibreLiftEquality
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C) (z : Fin (p+q) → M) : Prop :=
  ∃ k l : ℕ,
    ∃ U : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k,
    ∃ V : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l,
      Nonempty (GammaGroundBijection (nativeMixedMapFibreAt f z) (nativeWeakRVObjectLift U)) ∧
      Nonempty (GammaGroundBijection (nativeMixedMapFibreAt f' z) (nativeWeakRVObjectLift V)) ∧
      nativeWeakGeometricValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
          (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) U =
        nativeWeakGeometricValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
          (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) V

/-- The single-degree hypothesis is a special case. -/
theorem NativeGeometricVFFibreLiftEquality.toWeak
    {h00 : M ⊨ Axioms.ACVF00} {linear : Section2.GammaPiecewiseRationalAffineInput (M := M)}
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {hr : Cardinal.mk B.real < κ} {hγ : Cardinal.mk B.gamma < κ}
    {hΓ : Section2.NontrivialDefinableGamma B}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    {f : GammaGroundMap A C} {f' : GammaGroundMap A' C} {z : Fin (p+q) → M}
    (h : NativeGeometricVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z) :
    NativeGeometricWeakVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z := by
  obtain ⟨k,l,U,V,⟨e⟩,⟨e'⟩,he⟩ := h
  refine ⟨k,l,nativeStrictToWeak U,nativeStrictToWeak V,
    ⟨(GammaGroundBijection.ofCarrierEq (nativeStrictToWeak_lift U).symm).comp e⟩,
    ⟨(GammaGroundBijection.ofCarrierEq (nativeStrictToWeak_lift V).symm).comp e'⟩,?_⟩
  rw [nativeWeakGeometricValue_toWeak,nativeWeakGeometricValue_toWeak]
  unfold nativeGroundGeometricRetraction
  simp only [RingHom.comp_apply,Section3RVChartRingMaps.ordinary_class]
  exact he

theorem native_geometric_weak_vf_map_whole_witness_partition
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (N : ℕ) (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N)
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeGeometricWeakVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z) :
    ∃ K : ℕ,∃ P : Fin K → GammaGroundDefSet hc B (rawMixedSpace (M := M) p q),
      (∀ i,(P i).carrier ⊆ C.carrier ∧ ((P i).carrier = ∅ ∨
        ∃ W : NativeGeometricWeakVFLiftEqualitySchema (B := B)
          (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc N
            (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val,
          ∀ b : P i,W.Valid (nativeMixedCode b.val))) ∧
      (∀ i j,i ≠ j → Disjoint (P i).carrier (P j).carrier) ∧
      ∀ b,b ∈ C.carrier ↔ ∃ i,b ∈ (P i).carrier := by
  obtain ⟨J,hJ⟩ := native_geometric_weak_vf_lift_finite_catalog hκ hs hr hγ N (nativeMixedDomain C)
    (nativeMixedDomain_definable C) (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val
    (nativeMixedMapFibreFormula f).property (nativeMixedMapFibreFormula f').property (by
      intro z hz
      obtain ⟨k,l,U,V,⟨e⟩,⟨e'⟩,he⟩ := h z hz
      exact native_geometric_weak_vf_lift_schema_at_parameter h00 linear hκ hs hr hγ hΓ N hN
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val z
        ((nativeMixedDomain_definable C).proper z hz)
        (nativeMixedMapFibreAt f z) (nativeMixedMapFibreAt f' z)
        (nativeMixedMapFibreAt_domain f z).symm (nativeMixedMapFibreAt_domain f' z).symm U V e e' he)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let V : Fin (Fintype.card J) → GammaGroundDefSet hc B (rawMixedSpace (M := M) p q) := fun i =>
    nativeMixedOfRaw {z | (e i).val.Valid z}
      ((e i).val.valid_definable (nativeMixedMapFibreFormula f).property (nativeMixedMapFibreFormula f').property)
  have hcover : ∀ b ∈ C.carrier,∃ i,b ∈ (V i).carrier := by
    intro b hb
    obtain ⟨W,hW,hw⟩ := hJ (nativeMixedCode b) ⟨b,hb,rfl⟩
    obtain ⟨i,hi⟩ := e.surjective ⟨W,hW⟩
    refine ⟨i,?_⟩
    change (e i).val.Valid (nativeMixedCode b)
    rw [hi]
    exact hw
  obtain ⟨K,P,hP,hd,hcov⟩ := gammaGround_finite_cover_partition C V hcover
  refine ⟨K,P,?_,hd,hcov⟩
  intro i
  refine ⟨(hP i).1,?_⟩
  rcases (hP i).2 with hempty | ⟨j,hj⟩
  · exact Or.inl hempty
  · exact Or.inr ⟨(e j).val,fun b => hj b.property⟩

variable {G : GammaGroundContext M}

theorem nativeVFGeometricValue_map_fixed_weak_witness
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A A' : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (N : ℕ) (hN : ∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc G.base}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc G.base}.ncard ≤ N)
    (W : NativeGeometricWeakVFLiftEqualitySchema (B := G.base)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc N
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val)
    (hW : ∀ b : Z,W.Valid (nativeMixedCode b.val)) :
    nativeVFGeometricValue linear H (nativeVFClass (A.restrict (f.preimage Z) (f.preimage_subset Z))) =
      nativeVFGeometricValue linear H (nativeVFClass (A'.restrict (f'.preimage Z) (f'.preimage_subset Z))) := by
  have hWr : ∀ z ∈ nativeMixedDomain Z,W.Valid z := by
    rintro z ⟨b,hb,he⟩
    exact he ▸ hW ⟨b,hb⟩
  have hL := fun z hz => (hWr z hz).2.2.1
  have hR := fun z hz => (hWr z hz).2.2.2.1
  let eL := nativeVFMapLiftWitnessBijection f Z W.leftRV W.leftLift hL
  let eR := nativeVFMapLiftWitnessBijection f' Z W.rightRV W.rightLift hR
  have hfL := nativeVFMapLiftWitness_finite G.uncountable.le G.saturated G.model00 G.small_real
    f Z W.leftRV W.leftLift hL A.finite
  have hfR := nativeVFMapLiftWitness_finite G.uncountable.le G.saturated G.model00 G.small_real
    f' Z W.rightRV W.rightLift hR A'.finite
  obtain ⟨hfTL,heTL⟩ := thickSeq_vf linear H Z W.leftRV N hN (fun z hz => (hWr z hz).1) hfL W.leftDegree le_rfl
  obtain ⟨hfTR,heTR⟩ := thickSeq_vf linear H Z W.rightRV N hN (fun z hz => (hWr z hz).2.1) hfR W.rightDegree le_rfl
  let TL := thickFull hc W.leftRV N
  let TR := thickFull hc W.rightRV N
  let W' : NativeGeometricVFLiftEqualitySchema (B := G.base)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc
        (finiteRVSchemaLiftDomain hc TL).val (finiteRVSchemaLiftDomain hc TR).val :=
    ⟨W.leftDegree,_,TL,W.rightDegree,_,TR,W.commonDegree,W.left_le,W.right_le,
      idChart hc _ (finiteRVSchemaLiftDomain hc TL).property,
      idChart hc _ (finiteRVSchemaLiftDomain hc TR).property,W.evaluation⟩
  have hW' : ∀ b : Z,W'.Valid (nativeMixedCode b.val) := by
    intro b
    obtain ⟨h1,h2,_,_,h5⟩ := hW b
    exact ⟨thickFull_strict W.leftRV N hN _ h1,thickFull_strict W.rightRV N hN _ h2,
      idChart_valid hc _ (finiteRVSchemaLiftDomain hc TL).property _ (nativeMixedCode_proper b.val),
      idChart_valid hc _ (finiteRVSchemaLiftDomain hc TR).property _ (nativeMixedCode_proper b.val),h5⟩
  have he := native_vf_fixed_geometric_whole_witness_fubini linear H Z W' hW' hfTL hfTR
  let L : GammaGroundFiniteVFObject hc G.base :=
    ⟨p+W.leftDegree,q+W.leftArity,nativeVFLiftFamily Z W.leftRV,hfL⟩
  let R : GammaGroundFiniteVFObject hc G.base :=
    ⟨p+W.rightDegree,q+W.rightArity,nativeVFLiftFamily Z W.rightRV,hfR⟩
  exact (congrArg (nativeVFGeometricValue linear H) (nativeVFClass_bijection _ L eL)).trans
    (heTL.symm.trans (he.trans (heTR.trans
      (congrArg (nativeVFGeometricValue linear H) (nativeVFClass_bijection _ R eR)).symm)))

theorem thickPad_uniform_bound (B : Base (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) :
    ∃ N : ℕ,∀ t : M,iRV t → {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.Finite ∧
      {w | Fin.append w (fun _ : Fin 1 => t) ∈ thickPadGraph hc B}.ncard ≤ N := by
  obtain ⟨N,hN⟩ := nativeWeakRVLabelGraph_uniform_bound hκ hs hr hγ (nativeStrictToWeak (nativeAffineRVPower hc B 1))
  exact ⟨N,fun t ht => hN (fun _ => t) (fun _ => by simpa [sortEval,iRV] using ht)⟩

/-- Proposition 5.23 (geometric Fubini) for fibre representatives in RV[*]. -/
theorem nativeGeometricWeakVFFubini
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A A' : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeGeometricWeakVFFibreLiftEquality G.model00 linear G.uncountable.le
      G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma f f' z) :
    nativeVFGeometricValue linear H (nativeVFClass A) =
      nativeVFGeometricValue linear H (nativeVFClass A') := by
  obtain ⟨N,hN⟩ := thickPad_uniform_bound (hc := hc) G.base G.uncountable.le G.saturated G.small_real G.small_gamma
  obtain ⟨K,P,hP,hd,hcov⟩ := native_geometric_weak_vf_map_whole_witness_partition G.model00 linear
    G.uncountable.le G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma N hN f f' h
  have hp := nativeMap_preimage_partition f P hd hcov
  have hp' := nativeMap_preimage_partition f' P hd hcov
  let L (i : Fin K) := A.restrict (f.preimage (P i)) (f.preimage_subset (P i))
  let R (i : Fin K) := A'.restrict (f'.preimage (P i)) (f'.preimage_subset (P i))
  have hLclass : nativeVFClass A = ∑ i,nativeVFClass (L i) :=
    nativeVFClass_finite_partition A (fun i => f.preimage (P i)) hp.1 hp.2
  have hRclass : nativeVFClass A' = ∑ i,nativeVFClass (R i) :=
    nativeVFClass_finite_partition A' (fun i => f'.preimage (P i)) hp'.1 hp'.2
  have hL := (congrArg (nativeVFGeometricValue linear H) hLclass).trans (map_sum _ _ _)
  have hR := (congrArg (nativeVFGeometricValue linear H) hRclass).trans (map_sum _ _ _)
  refine hL.trans ((Finset.sum_congr rfl (fun i _ => ?_)).trans hR.symm)
  rcases (hP i).2 with hempty | ⟨W,hW⟩
  · have he (A0 : GammaGroundFiniteVFObject hc G.base) (g : GammaGroundMap A0.domain C) :
        (g.preimage (P i)).carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨a,ha,hz⟩
      exact Set.notMem_empty _ (hempty ▸ hz)
    have heL : nativeVFClass (L i) = 0 := nativeVFClass_of_empty (L i) (he A f)
    have heR : nativeVFClass (R i) = 0 := nativeVFClass_of_empty (R i) (he A' f')
    exact (congrArg (nativeVFGeometricValue linear H) heL).trans
      (congrArg (nativeVFGeometricValue linear H) heR).symm
  · exact nativeVFGeometricValue_map_fixed_weak_witness linear H A A' C f f' (P i) N hN W hW

end WeakGeometricFubini

/-! ### Discharged entry point -/
section WeakGeometricDischarged
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

/-- Proposition 5.23 for RV[*] fibre representatives, with both earlier-section inputs
instantiated by checked proofs. -/
theorem geometric_weak_fubini_discharged (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z∈nativeMixedDomain C,NativeGeometricWeakVFFibreLiftEquality G.model00
      GammaQE.gamma_piecewise_rational_affine G.uncountable.le G.saturated G.small_real
      G.small_gamma G.nontrivial_definable_gamma f f' z) :
    section5GeometricVFIntegral G hc (nativeVFClass A)=section5GeometricVFIntegral G hc (nativeVFClass A') :=
  nativeGeometricWeakVFFubini GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc) A A' C f f' h

end WeakGeometricDischarged

/-! ### Consistency checks for the RV[*] values -/
section WeakValueConsistency
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M} {k : ℕ}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)

/-- Over the original ground the RV[*] value is the geometric value of the integral of the
lift: the definition used in the fibre hypothesis is the intrinsic one. -/
theorem nativeVFGeometricValue_weak_lift (U : NativeWeakRVObject hc G.base k) :
    nativeVFGeometricValue linear H (nativeVFClass
      (⟨k,U.arity,nativeWeakRVObjectLift U,nativeWeakRVObjectLift_finite U⟩ : GammaGroundFiniteVFObject hc G.base)) =
    nativeWeakGeometricValue G.model00 linear G.uncountable.le G.saturated hc G.base
      G.small_real G.small_gamma G.nontrivial_definable_gamma U := by
  rw [nativeVFGeometricValue_pullback linear H _ (nativeWeakRVObjectLift_pullback U)]
  unfold nativeWeakGeometricValue
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  let X := (nativeMixedFullKeyMap (nativeWeakRVObjectLift U)).image
  let P := nativeRVZeroPatternBase X (Fin.castAdd U.arity) I
  have hkey : ∀ t : P,∃ u : U.domain,t.val = Fin.append (U.volume u).val u.val := by
    intro t
    exact nativeWeakLiftKey_graph U ⟨t.val,((nativeRVZeroPatternBase_mem X _ I t.val).mp t.property).1⟩
  have hmap : ∀ t : P,t.val ∘ Fin.natAdd k ∈ (weakZeroPatternDomain U I).carrier := by
    intro t
    obtain ⟨u,hu⟩ := hkey t
    have he : t.val ∘ Fin.natAdd k = u.val := by
      rw [hu]; exact funext (fun j => Fin.append_right _ _ j)
    rw [he]
    refine (weakZeroPatternDomain_mem U I u).mpr ?_
    intro j
    have hp := ((nativeRVZeroPatternBase_mem X _ I t.val).mp t.property).2 j
    rw [hu] at hp
    simpa [rvValues] using hp
  let g : GammaGroundMap P (weakZeroPatternDomain U I) :=
    (gammaGroundRVSelectCoordinates (Fin.natAdd k) P).corestrict hmap
  have hg : Function.Bijective g := by
    constructor
    · intro t t' he
      have he' : t.val ∘ Fin.natAdd k = t'.val ∘ Fin.natAdd k := congrArg Subtype.val he
      obtain ⟨u,hu⟩ := hkey t
      obtain ⟨u',hu'⟩ := hkey t'
      have huu : u = u' := by
        apply Subtype.ext
        rw [hu,hu'] at he'
        funext j
        have := congrFun he' j
        simpa using this
      subst huu
      exact Subtype.ext (hu.trans hu'.symm)
    · intro w
      have hw := weakZeroPatternDomain_subset U I w.property
      let u : U.domain := ⟨w.val,hw⟩
      obtain ⟨x,hx⟩ := Section2.tupleRV_surjective (U.volume u).val
      let a : nativeWeakRVObjectLift U := ⟨(x,u.val),u,rfl,hx.symm⟩
      have hval : ((nativeMixedFullKeyMap (nativeWeakRVObjectLift U)) a).val = Fin.append (U.volume u).val u.val :=
        (nativeMixedFullKeyMap_value _ a).trans (congrArg₂ Fin.append hx rfl)
      have hP : ((nativeMixedFullKeyMap (nativeWeakRVObjectLift U)) a).val ∈ P.carrier := by
        refine (nativeRVZeroPatternBase_mem X _ I _).mpr ⟨⟨a,rfl⟩,?_⟩
        rw [hval]
        intro j
        have := (weakZeroPatternDomain_mem U I u).mp w.property j
        simpa [rvValues] using this
      refine ⟨⟨_,hP⟩,Subtype.ext ?_⟩
      change ((nativeMixedFullKeyMap (nativeWeakRVObjectLift U)) a).val ∘ Fin.natAdd k = w.val
      rw [hval]
      exact funext (fun j => Fin.append_right _ _ j)
  exact nativeRVSetValue_bijection _ _ _ _ _ _ _ _ _ _ _ _ ⟨g,hg⟩

/-- The bounded single-degree hypothesis is a special case of the RV[*] one. -/
theorem NativeBoundedVFFibreLiftEquality.toWeak {B : Base (M := M)} {n r m s p q : ℕ}
    {h00 : M ⊨ Axioms.ACVF00} {linear : Section2.GammaPiecewiseRationalAffineInput (M := M)}
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {hr : Cardinal.mk B.real < κ} {hγ : Cardinal.mk B.gamma < κ}
    {hΓ : Section2.NontrivialDefinableGamma B}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    {f : GammaGroundMap A C} {f' : GammaGroundMap A' C} {z : Fin (p+q) → M}
    (h : NativeBoundedVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z) :
    NativeBoundedWeakVFFibreLiftEquality h00 linear hκ hs hr hγ hΓ f f' z := by
  obtain ⟨k,l,U,V,⟨e⟩,⟨e'⟩,he⟩ := h
  refine ⟨k,l,nativeStrictToWeak U,nativeStrictToWeak V,
    ⟨(GammaGroundBijection.ofCarrierEq (nativeStrictToWeak_lift U).symm).comp e⟩,
    ⟨(GammaGroundBijection.ofCarrierEq (nativeStrictToWeak_lift V).symm).comp e'⟩,?_⟩
  change nativeRVSetValue _ _ _ _ _ _ _ _ _ _ U.domain = nativeRVSetValue _ _ _ _ _ _ _ _ _ _ V.domain
  rw [nativeRVSetValue_object,nativeRVSetValue_object,nativeGroundRVEvaluation_class,nativeGroundRVEvaluation_class]
  exact he

/-- The existing single-degree geometric Fubini theorem is recovered from the RV[*] version. -/
theorem nativeGeometricVFFubini_via_weak {p q : ℕ}
    (A A' : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeGeometricVFFibreLiftEquality G.model00 linear G.uncountable.le
      G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma f f' z) :
    nativeVFGeometricValue linear H (nativeVFClass A) =
      nativeVFGeometricValue linear H (nativeVFClass A') :=
  nativeGeometricWeakVFFubini linear H A A' C f f' (fun z hz => (h z hz).toWeak)

end WeakValueConsistency

end DiamondIntegral.Section5
