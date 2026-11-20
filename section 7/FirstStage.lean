import «section 7».FiberwiseInput
import «section 6».MeasuredOrderedContractions
import «section 6».OrderedContractionHeadStarts

/-! The first stage and the rest of a standard contraction.

An ordered program in positive VF dimension is a first stage `T`
(`headStage`), which contracts the last VF coordinate, followed by a program on
the contracted set `T.contracted` (`restProgram`). A measured program
`(P, ρ)` on `(A, ω)` restricts to the measured program `(restProgram P, ρ)` on
`(T.contracted, ρ ∘ restProgram P)` (`restData`), and with a lift of the rest
(`restLift`) to a measured ordered contraction of the first-stage set
(`restContraction`).

**Head starts.** The head-start object of a contraction (Section 6) depends only
on the RV target `U` of its program, on its volume labels (the volume indices of
the VF coordinates, then the selected head-start labels) and on the RV form on
`U` (`cls_labelObject_eq`): its domain is `U`, its volume at `u` is `u` read at
these labels, and its form is the RV form. The volume labels of the whole
program with head start `k` are those of the rest with head start `k + 1`, the
extra label being the leading label of the first stage; only their order
differs. Hence the head-start-`k` class of a contraction equals the
head-start-`(k + 1)` class of its rest (`cls_headStart_rest` for Section 6's
normalized contractions, `cls_headStart_rest_ordered` for measured ordered
contractions), in degree `(n + 1) + k = n + (k + 1)`.

This is step 1 of the Lean plan for Corollary 7.15 and the reduction step of
Lemma 7.14. The rest object `restObject` is definitionally Section 6's
head-start object of `restContraction` (`restObject_eq`) whenever the finite
fibre hypothesis for the first-stage set is available. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.FiberwiseInput

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### First stage and rest of a program -/

section Program
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {n r q : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}

/-- The first stage of an ordered program in positive VF dimension. -/
def headStage : OrderedStandardContractionProgram (G := G) S A U → StandardContractionStage (G := G) A
  | .step T _ => T

/-- The rest of an ordered program, on the contracted set of its first stage. -/
def restProgram : (P : OrderedStandardContractionProgram (G := G) S A U) →
    OrderedStandardContractionProgram (G := G) S (headStage P).contracted U
  | .step _ tail => tail

theorem volumeIndex_last (P : OrderedStandardContractionProgram (G := G) S A U) :
    P.volumeIndex (Fin.last n) = (restProgram P).oldLabels (headStage P).leading := by
  match P with
  | .step T tail => exact OrderedStandardContractionProgram.volumeIndex_step_last T tail

theorem volumeIndex_castSucc (P : OrderedStandardContractionProgram (G := G) S A U) (i : Fin n) :
    P.volumeIndex i.castSucc = (restProgram P).volumeIndex i := by
  match P with
  | .step T tail => exact OrderedStandardContractionProgram.volumeIndex_step_castSucc T tail i

theorem oldLabels_eq (P : OrderedStandardContractionProgram (G := G) S A U) (i : Fin r) :
    P.oldLabels i = (restProgram P).oldLabels ((headStage P).oldLabels i) := by
  match P with
  | .step T tail => rfl

theorem toMap_eq (P : OrderedStandardContractionProgram (G := G) S A U) (p : A) :
    P.toMap p = (restProgram P).toMap ((headStage P).contraction p) := by
  match P with
  | .step T tail => rfl

end Program

/-! ### The rest as a measured ordered contraction -/

section Data
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {n r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

/-- The form induced on the first-stage set. -/
def restForm (D : MeasuredOrderedProgram (G := G) A ω) :
    Map (headStage D.program).contracted (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  D.rvForm.comp (restProgram D.program).toMap

theorem restForm_contraction (D : MeasuredOrderedProgram (G := G) A ω) (p : A) :
    (restForm D ((headStage D.program).contraction p)).val = (ω p).val := by
  have h := D.factor p
  rw [toMap_eq] at h
  exact h

/-- The rest of a measured program, on the first-stage set. -/
def restData (D : MeasuredOrderedProgram (G := G) A ω) :
    MeasuredOrderedProgram (G := G) (headStage D.program).contracted (restForm D) where
  arity := D.arity
  rvTarget := D.rvTarget
  program := restProgram D.program
  rvForm := D.rvForm
  factor _ := rfl

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))

/-- A lift of the rest of a measured program. -/
def restLift (D : MeasuredOrderedProgram (G := G) A ω) : OrderedStandardContractionLift (restData D).program :=
  Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
    (headStage D.program).contracted_proper)

/-- The rest of a measured program as a measured ordered contraction of the
first-stage set. -/
def restContraction (D : MeasuredOrderedProgram (G := G) A ω) :
    MeasuredOrderedContraction (G := G) (headStage D.program).contracted (restForm D) :=
  ⟨restData D, restLift h00 hc linear hκ hs hv hsmall hΓ D⟩

end Data

/-! ### Objects determined by volume labels -/

section Labels
variable {S : Set M} {a q : ℕ}

theorem headStartBaseVF_eq {X : Type*} (n k : ℕ) (x : Fin (n + k) → X) :
    headStartBaseVF n k x = fun i => x (Fin.castAdd k i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change headStartBaseVF n k (Fin.init x) = _
    rw [ih]
    rfl

theorem headStartExtraVF_eq {X : Type*} (n k : ℕ) (x : Fin (n + k) → X) :
    headStartExtraVF n k x = fun j => x (Fin.natAdd n j) := by
  induction k with
  | zero => funext j; exact j.elim0
  | succ k ih =>
    funext j
    induction j using Fin.lastCases with
    | last => rw [headStartExtraVF]; beta_reduce; rw [Fin.lastCases_last]; rfl
    | cast j => rw [headStartExtraVF]; beta_reduce; rw [Fin.lastCases_castSucc, ih]; rfl

variable {X : DefSet (rawMixedSpace (M := M) a q) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {ν : Fin a → Fin q}

/-- Membership in a head-start bundle of a set described by its RV target and
volume labels. -/
theorem mem_bundle_labels
    (hX : ∀ p : Mixed M a q, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (ν i))
    {k : ℕ} (l : Fin k → Fin q) (p : Mixed M (a + k) q) :
    p ∈ (rvHeadStartBundle X k l).carrier ↔
      (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (Fin.append ν l i) := by
  obtain ⟨x, u⟩ := p
  rw [mem_rvHeadStartBundle, hX, headStartBaseVF_eq, headStartExtraVF_eq]
  constructor
  · rintro ⟨⟨hU, hν⟩, hl⟩
    refine ⟨hU, fun i => ?_⟩
    refine Fin.addCases (motive := fun i => rv M (x i) = u (Fin.append ν l i)) (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hν i
    · rw [Fin.append_right]; exact congrFun hl j
  · rintro ⟨hU, h⟩
    refine ⟨⟨hU, fun i => ?_⟩, funext fun j => ?_⟩
    · have hi := h (Fin.castAdd k i)
      rwa [Fin.append_left] at hi
    · have hj := h (Fin.natAdd a j)
      rwa [Fin.append_right] at hj

variable (hX : ∀ p : Mixed M a q, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (ν i))
include hX

/-- The domain of the head-start object is the RV target. -/
theorem mem_domain_labels {k : ℕ} (l : Fin k → Fin q)
    (hT : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (u : Fin q → RVInfinity M) :
    u ∈ (preparedHeadStartRVObject X k l hT).domain.carrier ↔ (Fin.elim0, u) ∈ U.carrier := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ((mem_bundle_labels hX l p.val).mp p.property).1
  · intro hu
    obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (u ∘ Fin.append ν l)
    exact ⟨⟨(x, u), (mem_bundle_labels hX l _).mpr ⟨hu, fun i => congrFun hx i⟩⟩, rfl⟩

/-- The volume of the head-start object reads its point at the volume labels. -/
theorem value_labels {k : ℕ} (l : Fin k → Fin q)
    (hT : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (u : (preparedHeadStartRVObject X k l hT).domain) :
    (preparedHeadStartRVObject X k l hT).value u = fun i => u.val (Fin.append ν l i) := by
  obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ u
  have h := preparedRVObject_value (rvHeadStartBundle X k l) (rvHeadStartBundle_tagged X k l hT) p
  refine h.trans (funext fun i => ?_)
  exact ((mem_bundle_labels hX l p.val).mp p.property).2 i

omit hX in
/-- The measured head-start object with a given form. -/
def labelObject (X : DefSet (rawMixedSpace (M := M) a q) S) (k : ℕ) (l : Fin k → Fin q)
    (hT : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hfin : (preparedHeadStartRVObject X k l hT).volume.FiniteFibres)
    (hnz : ∀ u : (preparedHeadStartRVObject X k l hT).domain, ∀ i,
      ((preparedHeadStartRVObject X k l hT).value u i).val ≠ iRVZero)
    (η : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hη : ∀ p z : X, p.val.2 = z.val.2 → η p = η z) :
    MeasuredRVObject (M := M) S (a + k) :=
  ⟨preparedHeadStartRVObject X k l hT, hfin, hnz, headStartRVForm X k l η hη⟩

end Labels

/-- The `Γ`-value of an RV entry (`1` at `rv(0)`). -/
def gam (x : CanonicalRV.RVSort M) : Gamma M := if h : x.val ≠ iRVZero then Values.gammaOf x h else 1

theorem volumeGamma_eq {S : Set M} {d : ℕ} (W : MeasuredRVObject (M := M) S d) (u : W.object.domain) :
    W.volumeGamma u = ∏ i, gam (W.object.value u i) := by
  unfold MeasuredRVObject.volumeGamma rvVolumeGamma
  refine Finset.prod_congr rfl (fun i _ => ?_)
  unfold gam
  split_ifs with h
  · rfl
  · exact absurd (W.nonzero u i) h

section Classes
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}

/-- Measured objects related by a bijection of domains preserving the volume and
the form have the same class, across an equality of degrees. -/
theorem cls_eq_of_volume {d d' : ℕ} (h : d = d')
    {U : MeasuredRVObject (M := M) (T : Set M) d} {V : MeasuredRVObject (M := M) (T : Set M) d'}
    (hU : U.doublyBounded) (hV : V.doublyBounded)
    (F : Map U.object.domain V.object.domain) (hF : Function.Bijective F)
    (hvol : ∀ u, U.volumeGamma u = V.volumeGamma (F u))
    (hform : ∀ u, gammaMapValue U.form u = gammaMapValue V.form (F u)) :
    cls (objOf hc T U hU) = castCls h.symm (cls (objOf hc T V hV)) := by
  subst h
  refine cls_objOf_eq hc hU hV ⟨rvIsoOfFiniteFibres F hF U.finiteVolume V.finiteVolume U.nonzero V.nonzero,
    fun u => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  unfold MeasuredRVObject.totalWeight
  rw [hform u, hvol u]

variable {a b q kX kY : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) a q) (T : Set M)} {Y : DefSet (rawMixedSpace (M := M) b q) (T : Set M)}
variable {U : DefSet (rawMixedSpace (M := M) 0 q) (T : Set M)} {νX : Fin a → Fin q} {νY : Fin b → Fin q}

/-- Finite volume fibres pass to a head-start object with more volume labels
over the same RV target. -/
theorem finiteFibres_labels
    (hX : ∀ p : Mixed M a q, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νX i))
    (hY : ∀ p : Mixed M b q, p ∈ Y.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νY i))
    (lX : Fin kX → Fin q) (lY : Fin kY → Fin q)
    (hrange : ∀ i, ∃ j, Fin.append νY lY j = Fin.append νX lX i)
    (hTX : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hTY : ∀ p ∈ Y.carrier, ∀ z ∈ Y.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hfin : (preparedHeadStartRVObject X kX lX hTX).volume.FiniteFibres) :
    (preparedHeadStartRVObject Y kY lY hTY).volume.FiniteFibres := by
  have hYX : ∀ v : (preparedHeadStartRVObject Y kY lY hTY).domain,
      v.val ∈ (preparedHeadStartRVObject X kX lX hTX).domain.carrier := fun v =>
    (mem_domain_labels hX lX hTX v.val).mpr ((mem_domain_labels hY lY hTY v.val).mp v.property)
  intro t
  by_cases hne : ∃ v₀, (preparedHeadStartRVObject Y kY lY hTY).volume v₀ = t
  · obtain ⟨v₀, hv₀⟩ := hne
    let u₀ : (preparedHeadStartRVObject X kX lX hTX).domain := ⟨v₀.val, hYX v₀⟩
    have hf := (hfin ((preparedHeadStartRVObject X kX lX hTX).volume u₀)).preimage
      (f := fun v : (preparedHeadStartRVObject Y kY lY hTY).domain =>
        (⟨v.val, hYX v⟩ : (preparedHeadStartRVObject X kX lX hTX).domain))
      (fun x _ y _ he => by have h := congrArg Subtype.val he; exact Subtype.ext h)
    refine hf.subset ?_
    intro v hv
    have hvv : (preparedHeadStartRVObject Y kY lY hTY).value v = (preparedHeadStartRVObject Y kY lY hTY).value v₀ :=
      congrArg Subtype.val (hv.trans hv₀.symm)
    rw [value_labels hY lY hTY, value_labels hY lY hTY] at hvv
    apply Subtype.ext
    change (preparedHeadStartRVObject X kX lX hTX).value _ = (preparedHeadStartRVObject X kX lX hTX).value u₀
    rw [value_labels hX lX hTX, value_labels hX lX hTX]
    funext i
    obtain ⟨j, hj⟩ := hrange i
    have := congrFun hvv j
    simp only [hj] at this
    exact this
  · exact Set.finite_empty.subset (fun v hv => hne ⟨v, hv⟩)

/-- **Head-start objects are determined by volume labels.** Two head-start
objects over the same RV target `U`, whose volume labels agree up to order and
whose forms are the same RV form `ρ`, have the same class. -/
theorem cls_labelObject_eq (h : a + kX = b + kY)
    (hX : ∀ p : Mixed M a q, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νX i))
    (hY : ∀ p : Mixed M b q, p ∈ Y.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νY i))
    (lX : Fin kX → Fin q) (lY : Fin kY → Fin q)
    (hprod : ∀ f : Fin q → Gamma M, ∏ i, f (Fin.append νX lX i) = ∏ i, f (Fin.append νY lY i))
    (ρ : Map U (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (hTX : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hTY : ∀ p ∈ Y.carrier, ∀ z ∈ Y.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hfinX hfinY hnzX hnzY)
    (ηX : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (hηX)
    (ηY : Map Y (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (hηY)
    (hρX : ∀ (p : X) (z : U), z.val.2 = p.val.2 → (ηX p).val = (ρ z).val)
    (hρY : ∀ (p : Y) (z : U), z.val.2 = p.val.2 → (ηY p).val = (ρ z).val)
    (hdX : (labelObject X kX lX hTX hfinX hnzX ηX hηX).doublyBounded)
    (hdY : (labelObject Y kY lY hTY hfinY hnzY ηY hηY).doublyBounded) :
    cls (objOf hc T (labelObject X kX lX hTX hfinX hnzX ηX hηX) hdX) =
      castCls h.symm (cls (objOf hc T (labelObject Y kY lY hTY hfinY hnzY ηY hηY) hdY)) := by
  have hsub : (preparedHeadStartRVObject X kX lX hTX).domain.carrier ⊆
      (preparedHeadStartRVObject Y kY lY hTY).domain.carrier := fun u hu =>
    (mem_domain_labels hY lY hTY u).mpr ((mem_domain_labels hX lX hTX u).mp hu)
  let F := Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun x y he => by have h := congrArg Subtype.val he; exact Subtype.ext h, fun v => ?_⟩
    exact ⟨⟨v.val, (mem_domain_labels hX lX hTX v.val).mpr ((mem_domain_labels hY lY hTY v.val).mp v.property)⟩, rfl⟩
  refine cls_eq_of_volume hc h hdX hdY F hF (fun u => ?_) (fun u => ?_)
  · rw [volumeGamma_eq, volumeGamma_eq]
    change ∏ i, gam ((preparedHeadStartRVObject X kX lX hTX).value u i) =
      ∏ i, gam ((preparedHeadStartRVObject Y kY lY hTY).value (F u) i)
    rw [value_labels hX lX hTX, value_labels hY lY hTY]
    exact hprod (fun l => gam (u.val l))
  · obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ u
    obtain ⟨p', hp'⟩ := pureRVTagQuotient_surjective _ (F (pureRVTagQuotient _ p))
    have hpp : p'.val.2 = p.val.2 := congrArg Subtype.val hp'
    have hU : (Fin.elim0, p.val.2) ∈ U.carrier := ((mem_bundle_labels hX lX p.val).mp p.property).1
    let z : U := ⟨(Fin.elim0, p.val.2), hU⟩
    change (headStartRVForm X kX lX ηX hηX (pureRVTagQuotient _ p)).val =
      (headStartRVForm Y kY lY ηY hηY (F (pureRVTagQuotient _ p))).val
    rw [← hp', headStartRVForm_at, headStartRVForm_at]
    refine (hρX _ z ?_).trans (hρY _ z ?_).symm
    · rw [headStartBaseProjection_value]
    · rw [headStartBaseProjection_value]
      exact hpp.symm

end Classes

/-! ### The head-start class of a contraction is that of its rest -/

section Rest
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}

/-- The RV form of a measured program, read on a set over its RV target. -/
theorem rvForm_read {a q : ℕ} {U : DefSet (rawMixedSpace (M := M) 0 q) (T : Set M)}
    {X : DefSet (rawMixedSpace (M := M) a q) (T : Set M)}
    (ρ : Map U (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (f : Map X U) (hf : ∀ p : X, (f p).val.2 = p.val.2) (p : X) (z : U) (hz : z.val.2 = p.val.2) :
    ((ρ.comp f) p).val = (ρ z).val := by
  have he : f p = z := Subtype.ext (Prod.ext (funext fun i => i.elim0) ((hf p).trans hz.symm))
  change (ρ (f p)).val = _
  rw [he]

section Normalized
variable {e : Equiv.Perm (Fin (n + 1))}

/-- The labels of the rest: the selected labels of the source, carried through
the first stage, followed by the leading label of the first stage. -/
def restLabels (F : NormalizedMeasuredContraction (G := G) A ω e) {k : ℕ} (π : Fin k → Fin r) :
    Fin (k + 1) → Fin (headStage F.preparedContraction.data.program).arity :=
  Fin.snoc (α := fun _ => Fin (headStage F.preparedContraction.data.program).arity)
    (fun j => (headStage F.preparedContraction.data.program).oldLabels (Fin.natAdd (n + 1) (π j)))
    (headStage F.preparedContraction.data.program).leading

theorem restLabels_prod (F : NormalizedMeasuredContraction (G := G) A ω e) {k : ℕ} (π : Fin k → Fin r)
    (f : Fin F.preparedContraction.data.arity → Gamma M) :
    ∏ i, f (Fin.append (fun i => F.preparedContraction.data.program.volumeIndex (e.symm i)) (F.oldIndex ∘ π) i) =
      ∏ i, f (Fin.append (restProgram F.preparedContraction.data.program).volumeIndex
        ((restProgram F.preparedContraction.data.program).oldLabels ∘ restLabels F π) i) := by
  rw [Fin.prod_univ_add (a := n + 1) (b := k), Fin.prod_univ_add (a := n) (b := k + 1)]
  simp only [Fin.append_left, Fin.append_right]
  rw [Equiv.prod_comp e.symm (fun i => f (F.preparedContraction.data.program.volumeIndex i)),
    Fin.prod_univ_castSucc (fun i => f (F.preparedContraction.data.program.volumeIndex i)),
    Fin.prod_univ_castSucc (fun j => f (((restProgram F.preparedContraction.data.program).oldLabels ∘
      restLabels F π) j))]
  simp only [volumeIndex_castSucc, volumeIndex_last, restLabels, Function.comp_apply, Fin.snoc_castSucc,
    Fin.snoc_last, NormalizedMeasuredContraction.oldIndex, oldLabels_eq]
  rw [mul_assoc, mul_comm (f _)]

theorem restLabels_range (F : NormalizedMeasuredContraction (G := G) A ω e) {k : ℕ} (π : Fin k → Fin r) :
    ∀ i, ∃ j, Fin.append (restProgram F.preparedContraction.data.program).volumeIndex
        ((restProgram F.preparedContraction.data.program).oldLabels ∘ restLabels F π) j =
      Fin.append (fun i => F.preparedContraction.data.program.volumeIndex (e.symm i)) (F.oldIndex ∘ π) i := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    generalize e.symm i = i₁
    induction i₁ using Fin.lastCases with
    | last =>
      refine ⟨Fin.natAdd n (Fin.last k), ?_⟩
      rw [Fin.append_right, volumeIndex_last]
      simp only [restLabels, Function.comp_apply, Fin.snoc_last]
    | cast i₂ =>
      refine ⟨Fin.castAdd (k + 1) i₂, ?_⟩
      rw [Fin.append_left, volumeIndex_castSucc]
  | right j =>
    refine ⟨Fin.natAdd n j.castSucc, ?_⟩
    rw [Fin.append_right, Fin.append_right]
    simp only [restLabels, Function.comp_apply, Fin.snoc_castSucc, NormalizedMeasuredContraction.oldIndex,
      oldLabels_eq]

/-- The head-start-`(k + 1)` object of the rest of a normalized contraction. -/
def restObject (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    MeasuredRVObject (M := M) (T : Set M) (n + (k + 1)) :=
  labelObject (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).target (k + 1)
    ((restProgram F.preparedContraction.data.program).oldLabels ∘ restLabels F π)
    (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).target_tagged
    (finiteFibres_labels F.preparedContraction.lift.originalTarget_recover
      (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).recover _ _ (restLabels_range F π)
      F.target_tagged _ (F.headStartObject_finite_volume h00 hc linear hκ hs hv hsmall hΓ k π hFin))
    (preparedRVObject_nonzero _ _
      (rvHeadStartBundle_doublyBounded _ (k + 1) _
        (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).doublyBounded
        (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).proper.rvBounded))
    (restContraction h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).form
    (restContraction h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).form_same_tags

theorem restObject_doublyBounded (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    (restObject h00 hc linear hκ hs hv hsmall hΓ F k π hFin).doublyBounded :=
  preparedHeadStartRVObject_doublyBounded _ (k + 1) _
    (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).target_tagged
    (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).doublyBounded
    (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).proper.rvBounded

/-- With finite fibres on the first-stage set, the rest object is Section 6's
head-start object of the rest contraction. -/
theorem restObject_eq (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hFin₁ : ∀ a : Fin n → VF M, ∀ t : Fin (k + 1) → RVInfinity M,
      {u | (a, u) ∈ (headStage F.preparedContraction.data.program).contracted.carrier ∧ u ∘ restLabels F π = t}.Finite) :
    restObject h00 hc linear hκ hs hv hsmall hΓ F k π hFin =
      (restContraction h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).headStartObject
        hc h00 hκ.le hs hsmall (k + 1) (restLabels F π) hFin₁ := rfl

/-- **First stage and rest.** The head-start-`k` class of a normalized
contraction is the head-start-`(k + 1)` class of the rest of its program on the
first-stage set, with the leading label of the first stage as the extra label. -/
theorem cls_headStart_rest (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    cls (objOf hc T (F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin)
        (F.headStartObject_doublyBounded k π)) =
      castCls (show n + (k + 1) = (n + 1) + k by omega)
        (cls (objOf hc T (restObject h00 hc linear hκ hs hv hsmall hΓ F k π hFin)
          (restObject_doublyBounded h00 hc linear hκ hs hv hsmall hΓ F k π hFin))) :=
  cls_labelObject_eq hc (show (n + 1) + k = n + (k + 1) by omega)
    F.preparedContraction.lift.originalTarget_recover
    (restLift h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data).recover
    _ _ (restLabels_prod F π) F.preparedContraction.data.rvForm _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

end Normalized

section Ordered

/-- The labels of the rest of a measured ordered contraction. -/
def restLabelsOrdered (C : MeasuredOrderedContraction (G := G) A ω) {k : ℕ} (π : Fin k → Fin r) :
    Fin (k + 1) → Fin (headStage C.data.program).arity :=
  Fin.snoc (α := fun _ => Fin (headStage C.data.program).arity)
    (fun j => (headStage C.data.program).oldLabels (π j)) (headStage C.data.program).leading

theorem restLabelsOrdered_prod (C : MeasuredOrderedContraction (G := G) A ω) {k : ℕ} (π : Fin k → Fin r)
    (f : Fin C.data.arity → Gamma M) :
    ∏ i, f (Fin.append C.data.program.volumeIndex (C.data.program.oldLabels ∘ π) i) =
      ∏ i, f (Fin.append (restProgram C.data.program).volumeIndex
        ((restProgram C.data.program).oldLabels ∘ restLabelsOrdered C π) i) := by
  rw [Fin.prod_univ_add (a := n + 1) (b := k), Fin.prod_univ_add (a := n) (b := k + 1)]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fin.prod_univ_castSucc (fun i => f (C.data.program.volumeIndex i)),
    Fin.prod_univ_castSucc (fun j => f (((restProgram C.data.program).oldLabels ∘ restLabelsOrdered C π) j))]
  simp only [volumeIndex_castSucc, volumeIndex_last, restLabelsOrdered, Function.comp_apply, Fin.snoc_castSucc,
    Fin.snoc_last, oldLabels_eq]
  rw [mul_assoc, mul_comm (f _)]

theorem restLabelsOrdered_range (C : MeasuredOrderedContraction (G := G) A ω) {k : ℕ} (π : Fin k → Fin r) :
    ∀ i, ∃ j, Fin.append (restProgram C.data.program).volumeIndex
        ((restProgram C.data.program).oldLabels ∘ restLabelsOrdered C π) j =
      Fin.append C.data.program.volumeIndex (C.data.program.oldLabels ∘ π) i := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    induction i using Fin.lastCases with
    | last =>
      refine ⟨Fin.natAdd n (Fin.last k), ?_⟩
      rw [Fin.append_right, volumeIndex_last]
      simp only [restLabelsOrdered, Function.comp_apply, Fin.snoc_last]
    | cast i₂ =>
      refine ⟨Fin.castAdd (k + 1) i₂, ?_⟩
      rw [Fin.append_left, volumeIndex_castSucc]
  | right j =>
    refine ⟨Fin.natAdd n j.castSucc, ?_⟩
    rw [Fin.append_right, Fin.append_right]
    simp only [restLabelsOrdered, Function.comp_apply, Fin.snoc_castSucc, oldLabels_eq]

/-- The head-start-`(k + 1)` object of the rest of a measured ordered
contraction. -/
def restObjectOrdered (C : MeasuredOrderedContraction (G := G) A ω) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    MeasuredRVObject (M := M) (T : Set M) (n + (k + 1)) :=
  labelObject (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).target (k + 1)
    ((restProgram C.data.program).oldLabels ∘ restLabelsOrdered C π)
    (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).target_tagged
    (finiteFibres_labels C.lift.recover (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).recover _ _
      (restLabelsOrdered_range C π) C.lift.target_tagged _
      (C.lift.headStartObject_finite_volume hc h00 hκ.le hs hsmall k π hFin))
    (preparedRVObject_nonzero _ _
      (rvHeadStartBundle_doublyBounded _ (k + 1) _
        (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).doublyBounded
        (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).proper.rvBounded))
    (restContraction h00 hc linear hκ hs hv hsmall hΓ C.data).form
    (restContraction h00 hc linear hκ hs hv hsmall hΓ C.data).form_same_tags

theorem restObjectOrdered_doublyBounded (C : MeasuredOrderedContraction (G := G) A ω) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    (restObjectOrdered h00 hc linear hκ hs hv hsmall hΓ C k π hFin).doublyBounded :=
  preparedHeadStartRVObject_doublyBounded _ (k + 1) _
    (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).target_tagged
    (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).doublyBounded
    (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).proper.rvBounded

theorem headStartObject_doublyBounded (C : MeasuredOrderedContraction (G := G) A ω) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    (C.headStartObject hc h00 hκ.le hs hsmall k π hFin).doublyBounded :=
  preparedHeadStartRVObject_doublyBounded _ k _ C.lift.target_tagged C.lift.doublyBounded C.lift.proper.rvBounded

theorem restObjectOrdered_eq (C : MeasuredOrderedContraction (G := G) A ω) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hFin₁ : ∀ a : Fin n → VF M, ∀ t : Fin (k + 1) → RVInfinity M,
      {u | (a, u) ∈ (headStage C.data.program).contracted.carrier ∧ u ∘ restLabelsOrdered C π = t}.Finite) :
    restObjectOrdered h00 hc linear hκ hs hv hsmall hΓ C k π hFin =
      (restContraction h00 hc linear hκ hs hv hsmall hΓ C.data).headStartObject
        hc h00 hκ.le hs hsmall (k + 1) (restLabelsOrdered C π) hFin₁ := rfl

/-- **First stage and rest, for measured ordered contractions.** -/
theorem cls_headStart_rest_ordered (C : MeasuredOrderedContraction (G := G) A ω) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    cls (objOf hc T (C.headStartObject hc h00 hκ.le hs hsmall k π hFin)
        (headStartObject_doublyBounded h00 hc hκ hs hsmall C k π hFin)) =
      castCls (show n + (k + 1) = (n + 1) + k by omega)
        (cls (objOf hc T (restObjectOrdered h00 hc linear hκ hs hv hsmall hΓ C k π hFin)
          (restObjectOrdered_doublyBounded h00 hc linear hκ hs hv hsmall hΓ C k π hFin))) :=
  cls_labelObject_eq hc (show (n + 1) + k = n + (k + 1) by omega) C.lift.recover
    (restLift h00 hc linear hκ hs hv hsmall hΓ C.data).recover
    _ _ (restLabelsOrdered_prod C π) C.data.rvForm _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

end Ordered
end Rest

end DiamondIntegral.Section7.FirstStage
