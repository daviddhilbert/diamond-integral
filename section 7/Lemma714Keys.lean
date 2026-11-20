import «section 7».Lemma714PullData

/-! Lemma 7.14, part 26: keys, the key relation and row constancy.

After freezing, `f : B₀ → Bk` is followed by the regularization, so the labels
`x` of the regularized target `Bk^reg` carry the leading term `rv(y)` at the
designated coordinate (`regT_lead`). The keys are these labels (`keySet`); a
key `x` is related to the parameters `ψ(frz(p))` of the frozen points `frz(p)`
of all `p ∈ B₀` with labels `x` (`keyRel`, `keyRel_R`). Row equality of the
pulled-back data at frozen points with equal labels gives row constancy of the
data on key classes (`keyRel_rowConst`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Prod
open DiamondIntegral.Section6 DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {s : ℕ}
variable {B₀ : DefSet (rawMixedSpace (M := M) 1 s) S} {P : DefSet (rawMixedSpace (M := M) 1 0) S}

/-! ### The frozen point -/

/-- The freezing map of a focus freezing datum on `B₀`. -/
def frz (F : FMT.FocusFreezingData B₀) : Map B₀ B₀ := F.unaryBaseFreeze F.product_domain

theorem frz_val (F : FMT.FocusFreezingData B₀) (p : B₀) :
    (frz F p).val = ((fun _ : Fin 1 => FMT.vfFamilyFreeze F.balls F.centers (p.val.1 0)), p.val.2) := by
  show FMT.mixedFamilyFreeze F.balls F.centers 0 p.val = _
  refine Prod.ext ?_ rfl
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp [FMT.mixedFamilyFreeze]

/-! ### The regularized frozen target -/

section Reg
variable {sk : ℕ} (Bk : DefSet (rawMixedSpace (M := M) 1 sk) S)

/-- The regularized frozen target. -/
abbrev regT : DefSet (rawMixedSpace (M := M) 1 (1 + sk)) S := (regularizeMap Bk).image

theorem regT_lead {p : Mixed M 1 (1 + sk)} (hp : p ∈ (regT Bk).carrier) : p.2 (Fin.castAdd sk 0) = rv M (p.1 0) := by
  obtain ⟨q, -, rfl⟩ := (SpecialChains.mem_regularize Bk).mp hp
  rw [SpecialChains.regularize_snd_left]
  rfl

variable {Bk} (f : Map B₀ Bk)

/-- The frozen map followed by the regularization. -/
def fReg : Map B₀ (regT Bk) := (regularization Bk).comp f

theorem fReg_val (p : B₀) : (fReg f p).val = regularize (f p).val := rfl

theorem fReg_labels {p z : B₀} (h : (fReg f p).val.2 = (fReg f z).val.2) : (f p).val.2 = (f z).val.2 :=
  (SpecialChains.regularize_snd_eq.mp h).2

theorem fReg_surjective (hf : Function.Surjective f) : Function.Surjective (fReg f) :=
  (regularization_bijective Bk).2.comp hf

end Reg

/-! ### The key relation -/

section KeyRelSec
variable {sk : ℕ} {Bk : DefSet (rawMixedSpace (M := M) 1 sk) S} (f : Map B₀ Bk) (ψ : Map B₀ P)
  (F : FMT.FocusFreezingData B₀)

/-- `p ↦ (ψ(frz p)_VF, labels of fReg p)`. -/
def keyMap : Map B₀ (DefSet.univ (rawMixedSpace (M := M) 1 (1 + sk)) S) :=
  (assembleVR _).comp ((fReg f).pair (ψ.comp (frz F)))

theorem keyMap_val (p : B₀) : (keyMap f ψ F p).val = ((ψ (frz F p)).val.1, (fReg f p).val.2) := rfl

variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- **The key relation**: `x` is related to `ψ(frz(p))` for every `p ∈ B₀` with
regularized labels `x`. -/
def keyRel : KeyRel (⟨S, ∅⟩ : Base (M := M)) (rvs (1 + sk)) (vfs 1) where
  rel := rvvfPart (keyMap f ψ F).image.carrier
  rel_definable := real_base hc (rvvfPart_definable _) (by
    rintro _ ⟨p, -, rfl⟩
    exact sorted_append (fun i => (p.2 i).property) (fun i => (p.1 i).property))

omit hM in
theorem append_inj' {a b : ℕ} {x x' : Fin a → M} {z z' : Fin b → M} :
    Fin.append x z = Fin.append x' z' ↔ x = x' ∧ z = z' := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa using congrFun h (Fin.castAdd b i)
    · simpa using congrFun h (Fin.natAdd a i)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem keyRel_R (x : Fin (1 + sk) → M) (z : Fin 1 → M) :
    (keyRel f ψ F hc).R x z ↔ ∃ p : B₀, rvValues (fReg f p).val.2 = x ∧ vfValues (ψ (frz F p)).val.1 = z := by
  change (∃ q ∈ (keyMap f ψ F).image.carrier, Fin.append (rvValues q.2) (vfValues q.1) = Fin.append x z) ↔ _
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, he⟩
    exact ⟨p, (append_inj'.mp he).1, (append_inj'.mp he).2⟩
  · rintro ⟨p, hx, hz⟩
    exact ⟨_, ⟨p, rfl⟩, append_inj'.mpr ⟨hx, hz⟩⟩

theorem keyRel_mk (p : B₀) :
    (keyRel f ψ F hc).R (rvValues (fReg f p).val.2) (vfValues (ψ (frz F p)).val.1) :=
  (keyRel_R f ψ F hc _ _).mpr ⟨p, rfl, rfl⟩

include hc in
/-- `S`-definability of a component, from its definability over the real base. -/
theorem compDef (c : Comp (⟨S, ∅⟩ : Base (M := M)) (vfs 1)) : S.Definable LRV c.D :=
  ((real_base_iff hc).mp c.hD).1

/-- **Row constancy on key classes.** If the pulled-back data have equal rows at
frozen points with equal labels, every listed set has constant rows on every key
class. -/
theorem keyRel_rowConst (L : List (Comp (⟨S, ∅⟩ : Base (M := M)) (vfs 1)))
    (hrows : ∀ p z : B₀, (f p).val.2 = (f z).val.2 → ∀ c ∈ L,
      unaryRVDataRow (pullSet ψ c.D (compDef hc c)) (frz F p).val =
        unaryRVDataRow (pullSet ψ c.D (compDef hc c)) (frz F z).val)
    (x : Fin (1 + sk) → M) : AllRowConst (keyRel f ψ F hc) L x := by
  intro c hcL z z' hz hz' v
  obtain ⟨p, hpx, rfl⟩ := (keyRel_R f ψ F hc x z).mp hz
  obtain ⟨p', hpx', rfl⟩ := (keyRel_R f ψ F hc x z').mp hz'
  have hl : (f p).val.2 = (f p').val.2 := fReg_labels f (rvValues_injective (hpx.trans hpx'.symm))
  have hrow := hrows p p' hl c hcL
  rw [pull_row ψ c.D (compDef hc c) _ (frz F p).property,
    pull_row ψ c.D (compDef hc c) _ (frz F p').property] at hrow
  by_cases hv : ∀ j, sortEval SortTag.rv (v j)
  · let t : Fin c.n → RVInfinity M := fun j => ⟨v j, hv j⟩
    have ht : rvValues t = v := rfl
    rw [← ht]
    exact Set.ext_iff.mp hrow t
  · have hno : ∀ w : Fin 1 → M, Fin.append w v ∉ c.D := by
      intro w hw
      apply hv
      intro j
      have := c.hD.proper _ hw (Fin.natAdd 1 j)
      simpa only [Fin.append_right] using this
    exact ⟨fun h => (hno _ h).elim, fun h => (hno _ h).elim⟩

end KeyRelSec

/-! ### The key set -/

section KeySetSec
variable {sk : ℕ} (Bk : DefSet (rawMixedSpace (M := M) 1 sk) S) (hc : CanonicalStructure.IsCanonical (M := M))
  (hRB : RVSupportDoublyBounded (regT Bk).carrier) (hRP : IsRVPullback (regT Bk).carrier)
  (hfin : ∀ y : Fin 1 → VF M, {u : Fin (1 + sk) → RVInfinity M | (y, u) ∈ (regT Bk).carrier}.Finite)

include hRB in
theorem regT_labels_nonzero : ∀ p ∈ (regT Bk).carrier, ∀ i, NonzeroRV (p.2 i).val := by
  obtain ⟨γ, hγ⟩ := hRB
  have hU : RVValueDoublyBounded {u : Fin (1 + sk) → RVInfinity M | ∃ y, (y, u) ∈ (regT Bk).carrier} :=
    ⟨γ, fun u ⟨y, hy⟩ i => hγ (y, u) hy i⟩
  intro p hp i
  exact ⟨(p.2 i).property, fun he => hU.nonzero p.2 ⟨p.1, hp⟩ i (Subtype.ext he)⟩

include hRB hRP hfin in
/-- **The key set**: the labels of the regularized frozen target, with designated
coordinate the leading term. -/
def keySet : KeySet (⟨S, ∅⟩ : Base (M := M)) (1 + sk) where
  carrier := rvPart (regT Bk).carrier
  definable := real_base hc (rvPart_definable _) (by
    rintro _ ⟨p, -, rfl⟩ i
    exact (p.2 i).property)
  idx := Fin.castAdd sk 0
  nonzero := by
    rintro _ ⟨p, hp, rfl⟩
    exact regT_labels_nonzero Bk hRB p hp _
  finite := by
    intro c
    by_cases hne : {x | x ∈ rvPart (regT Bk).carrier ∧ x (Fin.castAdd sk 0) = c}.Nonempty
    · obtain ⟨_, ⟨p₀, hp₀, rfl⟩, hc₀⟩ := hne
      apply ((hfin p₀.1).image rvValues).subset
      rintro _ ⟨⟨p, hp, rfl⟩, hpc⟩
      refine ⟨p.2, ?_, rfl⟩
      have h1 : p.2 (Fin.castAdd sk 0) = p₀.2 (Fin.castAdd sk 0) := Subtype.ext (hpc.trans hc₀.symm)
      rw [regT_lead Bk hp, regT_lead Bk hp₀] at h1
      have hrv : tupleRV M p.1 = tupleRV M p₀.1 := by
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact h1
      exact rvPullback_mem_of_sameRV hRP hp (q := (p₀.1, p.2)) hrv rfl
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty

theorem keySet_carrier : (keySet Bk hc hRB hRP hfin).carrier = rvPart (regT Bk).carrier := rfl

theorem keySet_nonzero_all : ∀ x ∈ (keySet Bk hc hRB hRP hfin).carrier, ∀ i, NonzeroRV (x i) := by
  rintro _ ⟨p, hp, rfl⟩ i
  exact regT_labels_nonzero Bk hRB p hp i

theorem keySet_codeBounded : RVCodeDoublyBounded (keySet Bk hc hRB hRP hfin).carrier := by
  obtain ⟨γ, hγ⟩ := hRB
  refine ⟨γ, ?_⟩
  rintro _ ⟨p, hp, rfl⟩ i
  have hne : p.2 i ≠ rvZero M := fun he =>
    (regT_labels_nonzero Bk ⟨γ, hγ⟩ p hp i).2 (congrArg Subtype.val he)
  change (γ⁻¹).val ≤ (codeValue (p.2 i).val).val ∧ (codeValue (p.2 i).val).val ≤ γ.val
  rw [nonzero_rv_codeValue_val (p.2 i) hne]
  exact hγ p hp i

end KeySetSec

end DiamondIntegral.Section7.Lemma714Prod
