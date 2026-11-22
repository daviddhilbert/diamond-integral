import «section 8».TruncConstructible
import «section 8».TruncNormalForm
import Section5.PolynomialPreparation
import Section3.SortedBoolean
import Section4.CanonicalNormalization

/-! The coefficient set of a definable set of the concrete model is constructible.

Let `X` be definable in the concrete model over a parameter set `S` whose field-sort elements are
`m`-rational, at a tuple of sorts `sn`. For a polynomial point `p` in the field slots and labels
`rv(c_{lab i} t^{e_i/m})` in the RV slots, the set of parameters `c ∈ ℂ^σ` whose point lies in `X` is
constructible (`coefficient_constructible`).

Proof: by `NormalForm.definable_agree`, membership in `X` depends only on the RV slots and on
`rv P(x)` for finitely many polynomials `P` over `ℂ((t^{1/m}))`. So `X` is the preimage of the RV set
`Ψ` of these data (`psiSet`, definable as the image of `X` under a definable map). At a polynomial
point each `rv P(x_c)` is piecewise `rv(G(c) t^{e/m})` (`isPiecewise_fam`), and `rdef_piecewise`
applies. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.RingDefinable DiamondIntegral.Section8.NormalForm

local instance truncDefStructure : LRV.Structure Carrier := canonicalInterpret
local instance truncDefModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {σ : Type} {N : ℕ}

/-- The raw point of the concrete model at the parameter `c`: a polynomial point in the field
slots and `rv(c_{lab i} t^{e_i/m})` in the RV slots. -/
def rawPoint (m : ℕ+) (sn : Fin N → SortTag) (p : PolyPoint σ N) (e : Fin N → ℤ) (lab : Fin N → σ)
    (c : σ → ℂ) : Fin N → Carrier :=
  fun i => match sn i with
    | .vf => Sum.inl (p.eval m c i)
    | .rv => Sum.inr (linePoint (zlev m (e i)) (c (lab i)))

theorem rawPoint_sorted (m : ℕ+) (sn : Fin N → SortTag) (p : PolyPoint σ N) (e : Fin N → ℤ)
    (lab : Fin N → σ) (c : σ → ℂ) (i : Fin N) : sortEval (sn i) (rawPoint m sn p e lab c i) := by
  unfold rawPoint
  cases sn i with
  | vf => exact trivial
  | rv => exact not_false

/-- `ℂ((t^{1/m}))` inside the field sort of the concrete model. -/
def ratSubring' (m : ℕ+) : Subring (VFType (M := Carrier)) :=
  (ratSubring m).comap taggedFieldEquiv.toRingHom

/-- The identification of `ratSubring' m` with `ratSubring m`. -/
def ratHom (m : ℕ+) : ratSubring' m →+* ratSubring m :=
  (taggedFieldEquiv.toRingHom.comp (ratSubring' m).subtype).codRestrict (ratSubring m)
    (fun x => x.property)

theorem vfPoint_rawPoint (m : ℕ+) (sn : Fin N → SortTag) (p : PolyPoint σ N)
    (hp : ∀ i, sn i = .rv → p.len i = 0) (e : Fin N → ℤ) (lab : Fin N → σ) (c : σ → ℂ) :
    vfPoint (rawPoint m sn p e lab c) = fun i => taggedFieldEquiv.symm (p.eval m c i) := by
  funext i
  unfold vfPoint rawPoint
  cases hi : sn i with
  | vf =>
    simp only
    have h : sortEval .vf (Sum.inl (p.eval m c i) : Carrier) := trivial
    exact (dif_pos h).trans rfl
  | rv =>
    simp only
    have hlen := hp i hi
    have h0 : p.eval m c i = 0 := by
      unfold PolyPoint.eval
      rw [hlen, Finset.range_zero, Finset.sum_empty]
    have h : ¬ sortEval .vf (Sum.inr (linePoint (zlev m (e i)) (c (lab i))) : Carrier) := fun h => h
    rw [h0]
    exact (dif_neg h).trans (taggedFieldEquiv.symm.map_zero).symm

/-- The value of a polynomial over `ratSubring' m` at a raw point, as a Puiseux series. -/
theorem polyValue_rawPoint (m : ℕ+) (sn : Fin N → SortTag) (p : PolyPoint σ N)
    (hp : ∀ i, sn i = .rv → p.len i = 0) (e : Fin N → ℤ) (lab : Fin N → σ)
    (P : MvPolynomial (Fin N) (ratSubring' m)) (c : σ → ℂ) :
    taggedFieldEquiv (polyValue (ratSubring' m) P (rawPoint m sn p e lab c)) =
      MvPolynomial.eval₂ (ratSubring m).subtype (p.eval m c) (MvPolynomial.map (ratHom m) P) := by
  rw [polyValue, vfPoint_rawPoint m sn p hp, MvPolynomial.eval₂_map]
  have h := MvPolynomial.eval₂_comp_left taggedFieldEquiv.toRingHom (ratSubring' m).subtype
    (fun i => taggedFieldEquiv.symm (p.eval m c i)) P
  have h' : (taggedFieldEquiv.toRingHom ∘ fun i => taggedFieldEquiv.symm (p.eval m c i)) = p.eval m c := by
    funext i
    exact taggedFieldEquiv.apply_symm_apply _
  rw [h'] at h
  exact h

/-- `rv P(x_c)` is piecewise `rv(G(c) t^{e/m})`. -/
theorem isPiecewise_poly [Finite σ] (m : ℕ+) (sn : Fin N → SortTag) (p : PolyPoint σ N)
    (hp : ∀ i, sn i = .rv → p.len i = 0) (e : Fin N → ℤ) (lab : Fin N → σ)
    (P : MvPolynomial (Fin N) (ratSubring' m)) :
    IsPiecewise m (fun c => rvOfField (taggedFieldEquiv
      (polyValue (ratSubring' m) P (rawPoint m sn p e lab c)))) := by
  have h := isPiecewise_fam (fam_poly m p (MvPolynomial.map (ratHom m) P))
  convert h using 3 with c
  exact polyValue_rawPoint m sn p hp e lab P c

/-! ### The RV set of leading data -/

section Data

variable (m : ℕ+) (sn : Fin N → SortTag) {k : ℕ} (Pj : Fin k → MvPolynomial (Fin N) (ratSubring' m))

/-- The raw tuple read by the polynomial codes: the field slots, and `0` at the RV slots. -/
def codePoint (xs : Fin N → Carrier) : Fin N ⊕ Fin 0 → Carrier :=
  Sum.elim (fun i => match sn i with
    | .vf => xs i
    | .rv => iVFZero) Fin.elim0

/-- The data of a raw tuple: `rv P_j(xs)`, then the RV slots (`rv(0)` at the field slots). -/
def dataMap (xs : Fin N → Carrier) : Fin (k + N) → Carrier :=
  Fin.append
    (fun j => iRv (SpecialTransformations.Section5.mvPolynomialCode
      (MvPolynomial.map (ratSubring' m).subtype (Pj j)) (codePoint sn xs)))
    (fun i => match sn i with
      | .vf => iRVZero
      | .rv => xs i)

theorem dataMap_poly {xs : Fin N → Carrier} (hx : ∀ i, sortEval (sn i) (xs i)) (j : Fin k) :
    dataMap m sn Pj xs (Fin.castAdd N j) = iRv (polyValue (ratSubring' m) (Pj j) xs).val := by
  rw [dataMap, Fin.append_left]
  congr 1
  rw [SpecialTransformations.Section5.mvPolynomialCode_eq _ _ (vfPoint xs), MvPolynomial.eval_map]
  · rfl
  · intro i
    unfold codePoint
    simp only [Sum.elim_inl]
    have hxi := hx i
    cases hi : sn i with
    | vf =>
      rw [hi] at hxi
      simp only
      have hv : vfPoint xs i = (⟨xs i, hxi⟩ : VFType (M := Carrier)) := dif_pos hxi
      rw [hv]
    | rv =>
      rw [hi] at hxi
      simp only
      have hn : ¬ sortEval .vf (xs i) := by
        cases hxs : xs i with
        | inl f => rw [hxs] at hxi; exact absurd trivial hxi
        | inr r => exact fun h => h
      have hv : vfPoint xs i = (0 : VFType (M := Carrier)) := dif_neg hn
      rw [hv]
      rfl

theorem dataMap_rv {xs : Fin N → Carrier} (i : Fin N) (hi : sn i = .rv) :
    dataMap m sn Pj xs (Fin.natAdd k i) = xs i := by
  rw [dataMap, Fin.append_right]
  simp only [hi]

theorem univ_definable_of_definableOver {S : Set Carrier} {X : Set (Fin N → Carrier)}
    (hX : DefinableOver S sn X) :
    (Set.univ : Set Carrier).Definable LRV X ∧ ∀ x ∈ X, ∀ i, sortEval (sn i) (x i) := by
  obtain ⟨hraw, hsort⟩ := (definableOver_iff_normalized_raw S sn X).mp hX
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hraw
  exact ⟨hraw.mono (Set.subset_univ _), hsort⟩

theorem dataMap_definableFun (j' : Fin (k + N)) :
    (Set.univ : Set Carrier).DefinableFun LRV
      (fun z : Fin N ⊕ Fin (k + N) → Carrier => dataMap m sn Pj (z ∘ Sum.inl) j') := by
  have hcodePoint : (Set.univ : Set Carrier).DefinableMap LRV
      (fun z : Fin N ⊕ Fin (k + N) → Carrier => codePoint sn (z ∘ Sum.inl)) := by
    intro a
    cases a with
    | inr a => exact a.elim0
    | inl i =>
      unfold codePoint
      simp only [Sum.elim_inl]
      cases sn i with
      | vf => exact Set.DefinableFun.proj LRV
      | rv => exact LRV.definableFun_const _ (Set.mem_univ _)
  refine Fin.addCases (fun j => ?_) (fun i => ?_) j'
  · have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0)
      (S := (Set.univ : Set Carrier)) (MvPolynomial.map (ratSubring' m).subtype (Pj j))
      (fun _ => Set.mem_univ _)
    change @Set.DefinableFun Carrier LRV (CanonicalStructure.normalize (M := Carrier)) (Fin N ⊕ Fin 0)
      (Set.univ : Set Carrier) (SpecialTransformations.Section5.mvPolynomialCode (m := 0)
        (MvPolynomial.map (ratSubring' m).subtype (Pj j))) at hp
    rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hp
    have hF := (Set.DefinableFun.of_empty (A := (Set.univ : Set Carrier))
      (Set.DefinableFun.fun_symbol (M := Carrier) (L := LRV) Fn.rvMap)).comp
      (show (Set.univ : Set Carrier).DefinableMap LRV
          (fun z : Fin N ⊕ Fin (k + N) → Carrier =>
            ![SpecialTransformations.Section5.mvPolynomialCode
              (MvPolynomial.map (ratSubring' m).subtype (Pj j)) (codePoint sn (z ∘ Sum.inl))]) from by
        intro a
        fin_cases a
        exact hp.comp hcodePoint)
    convert hF using 2 with z
    rw [dataMap, Fin.append_left]
    rfl
  · have he : (fun z : Fin N ⊕ Fin (k + N) → Carrier => dataMap m sn Pj (z ∘ Sum.inl) (Fin.natAdd k i)) =
        fun z => match sn i with
          | .vf => iRVZero
          | .rv => z (Sum.inl i) := by
      funext z
      rw [dataMap, Fin.append_right]
      rfl
    rw [he]
    cases sn i with
    | vf => exact LRV.definableFun_const _ (Set.mem_univ _)
    | rv => exact Set.DefinableFun.proj LRV

/-- The image of a definable set under the data map is definable. -/
theorem dataImage_definable {X : Set (Fin N → Carrier)} (hX : (Set.univ : Set Carrier).Definable LRV X) :
    (Set.univ : Set Carrier).Definable LRV (dataMap m sn Pj '' X) := by
  let Zg : Set (Fin N ⊕ Fin (k + N) → Carrier) :=
    ((fun g : Fin N ⊕ Fin (k + N) → Carrier => g ∘ Sum.inl) ⁻¹' X) ∩
      ⋂ j' : Fin (k + N), {z | z (Sum.inr j') = dataMap m sn Pj (z ∘ Sum.inl) j'}
  have hZg : (Set.univ : Set Carrier).Definable LRV Zg :=
    (hX.preimage_comp Sum.inl).inter (Set.definable_iInter_of_finite fun j' =>
      (Set.DefinableFun.proj (L := LRV) (A := (Set.univ : Set Carrier))
        (i := (Sum.inr j' : Fin N ⊕ Fin (k + N)))).ofPred_eq (dataMap_definableFun m sn Pj j'))
  convert hZg.image_comp (Sum.inr : Fin (k + N) → Fin N ⊕ Fin (k + N)) using 1
  ext w
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    refine ⟨Sum.elim xs (dataMap m sn Pj xs), ⟨hxs, ?_⟩, rfl⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro j'
    rfl
  · rintro ⟨z, ⟨hz, hz'⟩, rfl⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hz'
    exact ⟨z ∘ Sum.inl, hz, funext fun j' => (hz' j').symm⟩

/-- The RV set of the data of `X`. -/
def psiSet {X : Set (Fin N → Carrier)} (hX : (Set.univ : Set Carrier).Definable LRV X) :
    DefSet (rawRVSpace (M := Carrier) (k + N)) (Set.univ : Set Carrier) :=
  ⟨{w | rvValues w ∈ dataMap m sn Pj '' X}, by
    let P := rawRVSpace (M := Carrier) (k + N)
    change (Set.univ : Set Carrier).Definable LRV (P.preimage {w | rvValues w ∈ dataMap m sn Pj '' X})
    convert (P.definable_domain (Set.univ : Set Carrier)).inter (dataImage_definable m sn Pj hX) using 1
    ext z
    constructor
    · rintro ⟨hz, hzR⟩
      have hzR' : rvValues (P.decode ⟨z, hz⟩) ∈ dataMap m sn Pj '' X := hzR
      have he : rvValues (P.decode ⟨z, hz⟩) = z := rvValues_decode ⟨z, hz⟩
      rw [he] at hzR'
      exact ⟨hz, hzR'⟩
    · rintro ⟨hz, hzR⟩
      refine ⟨hz, ?_⟩
      show rvValues (P.decode ⟨z, hz⟩) ∈ dataMap m sn Pj '' X
      have he : rvValues (P.decode ⟨z, hz⟩) = z := rvValues_decode ⟨z, hz⟩
      rw [he]
      exact hzR⟩

end Data

/-! ### The main statement -/

theorem iRv_inl (f : Ser) : iRv (Sum.inl f : Carrier) = Sum.inr (rvOfField f) := by
  change (if ∀ i : Fin 1, @sortEval Carrier interpret .vf
    ((![Sum.inl f] : Fin 1 → Carrier) i) then Sum.inr (rvOfField f) else _) = _
  rw [if_pos (by intro i; fin_cases i; trivial)]

theorem iRv_val (a : VFType (M := Carrier)) : iRv a.val = Sum.inr (rvOfField (taggedFieldEquiv a)) := by
  have h := vfType_tag a
  rw [← h, iRv_inl]
  rfl

/-- **The coefficient set of a definable set is constructible.** Let `X` be definable in the
concrete model over `S`, whose field-sort elements are `m`-rational. The set of parameters `c` whose
raw point (a polynomial point in the field slots, `rv(c_{lab i} t^{e_i/m})` in the RV slots) lies in
`X` is constructible. -/
theorem coefficient_constructible [Finite σ] (m : ℕ+) (sn : Fin N → SortTag) {S : Set Carrier}
    (hS : ∀ f : Ser, (Sum.inl f : Carrier) ∈ S → IsRational m f)
    {X : Set (Fin N → Carrier)} (hX : DefinableOver S sn X)
    (p : PolyPoint σ N) (hp : ∀ i, sn i = .rv → p.len i = 0) (e : Fin N → ℤ) (lab : Fin N → σ) :
    RDef {c : σ → ℂ | rawPoint m sn p e lab c ∈ X} := by
  obtain ⟨hraw, hsorted⟩ := univ_definable_of_definableOver sn hX
  have hR : ∀ x ∈ S, ∀ h : sortEval .vf x, (⟨x, h⟩ : VFType (M := Carrier)) ∈ ratSubring' m := by
    intro x hx h
    cases x with
    | inl f => exact hS f hx
    | inr r => exact False.elim h
  obtain ⟨F, hF⟩ := definable_agree sn (ratSubring' m) hX hR
  let Pj : Fin F.card → MvPolynomial (Fin N) (ratSubring' m) := fun j => (F.equivFin.symm j).val
  let lam : Fin (F.card + N) → (σ → ℂ) → RV := fun j' c =>
    Fin.append
      (fun j => rvOfField (taggedFieldEquiv
        (polyValue (ratSubring' m) (Pj j) (rawPoint m sn p e lab c))))
      (fun i => match sn i with
        | .vf => none
        | .rv => linePoint (zlev m (e i)) (c (lab i))) j'
  have hlam : ∀ j', IsPiecewise m (lam j') := by
    intro j'
    refine Fin.addCases (fun j => ?_) (fun i => ?_) j'
    · have h := isPiecewise_poly m sn p hp e lab (Pj j)
      convert h using 2 with c
      simp only [lam, Fin.append_left]
    · cases hi : sn i with
      | vf =>
        convert isPiecewise_none (σ := σ) m using 2 with c
        simp only [lam, Fin.append_right, hi]
      | rv =>
        convert isPiecewise_label m (e i) (lab i) using 2 with c
        simp only [lam, Fin.append_right, hi]
  have hdata : ∀ c, rvValues (fun j' => rvTag (lam j' c)) =
      dataMap m sn Pj (rawPoint m sn p e lab c) := by
    intro c
    funext j'
    refine Fin.addCases (fun j => ?_) (fun i => ?_) j'
    · rw [dataMap_poly m sn Pj (rawPoint_sorted m sn p e lab c) j]
      show Sum.inr (lam (Fin.castAdd N j) c) = _
      simp only [lam, Fin.append_left]
      exact (iRv_val _).symm
    · show Sum.inr (lam (Fin.natAdd F.card i) c) = _
      simp only [lam, Fin.append_right]
      cases hi : sn i with
      | vf =>
        rw [dataMap, Fin.append_right]
        simp only [hi]
        rfl
      | rv =>
        rw [dataMap_rv m sn Pj i hi]
        unfold rawPoint
        simp only [hi]
  have h := rdef_piecewise m lam hlam (psiSet m sn Pj hraw)
  convert h using 1
  ext c
  change rawPoint m sn p e lab c ∈ X ↔
    rvValues (fun j' => rvTag (lam j' c)) ∈ dataMap m sn Pj '' X
  rw [hdata c]
  constructor
  · exact fun hc => ⟨_, hc, rfl⟩
  · rintro ⟨xs, hxs, he⟩
    have hx := hsorted xs hxs
    have hc := rawPoint_sorted m sn p e lab c
    refine (hF xs _ hx hc ⟨?_, ?_⟩).mp hxs
    · intro i hi
      have := congrFun he (Fin.natAdd F.card i)
      rwa [dataMap_rv m sn Pj i hi, dataMap_rv m sn Pj i hi] at this
    · intro P hP
      have hj : Pj (F.equivFin ⟨P, hP⟩) = P := by simp [Pj]
      have := congrFun he (Fin.castAdd N (F.equivFin ⟨P, hP⟩))
      rw [dataMap_poly m sn Pj hx, dataMap_poly m sn Pj hc, hj] at this
      exact this

end DiamondIntegral.Section8.Truncation
