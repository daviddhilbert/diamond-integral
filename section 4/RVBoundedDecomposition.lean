import «section 4».RVStrictBoundedComparison
import «section 4».RVBoundedBalancedTensor
import «section 4».GammaBoundedMapImage
import «section 5».GammaQEFiniteLaws

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBoundedDecomposition
open RVMeasuredCharts RVMeasuredBounds FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Isomorphisms out of strict bounded charts land in bounded charts (Lemma 2.41) -/

/-- The source points whose image has a nonzero `j`-th coordinate. -/
def coordinateDomain {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) (j : Fin Y.arity) :
    Set (Fin X.arity → M) :=
  {x | ∃ hx : x ∈ X.domain, NonzeroRV ((F.equiv ⟨x, hx⟩).val j)}

/-- The Gamma value of the `j`-th image coordinate. -/
def coordinateValue {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) (j : Fin Y.arity)
    (x : Fin X.arity → M) : Values.Gamma (M := M) :=
  if hx : x ∈ X.domain then codeValue ((F.equiv ⟨x, hx⟩).val j) else 1

theorem coordinateValue_of {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) (j : Fin Y.arity)
    (u : X.domain) : coordinateValue F j u.val = codeValue ((F.equiv u).val j) :=
  dite_eq_left u.property

theorem coordinate_volume_definable {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y)
    (j : Fin Y.arity) :
    DefinableOverBase B (fun _ : Fin (X.arity + 1) => .rv)
      {w | Fin.tail w ∈ coordinateDomain F j ∧ NonzeroRV (w 0) ∧
        codeValue (w 0) = coordinateValue F j (Fin.tail w)} := by
  let n := X.arity
  let m := Y.arity
  let EQ : Set (Fin 2 → M) := {z | Proper z ∧ codeValue (z 0) = codeValue (z 1)}
  have hEQ : DefinableOverBase B (fun _ : Fin 2 => .rv) EQ :=
    GammaDefinableMaps.eq_definable_base B (0 : Fin 2) 1
  let π2 : Fin 2 → Fin (m + n + 1) := ![0, (tailIndex m n j).succ]
  let ρ : Fin (n + 1) → Fin (m + n + 1) := Fin.cases 0 (fun i => (headIndex m n i).succ)
  have hG := F.graph_definable.preimage_real (fun _ : Fin (m + n + 1) => .rv) Fin.succ
  have hE := hEQ.preimage_real (fun _ : Fin (m + n + 1) => .rv) π2
  have hR := (hG.inter hE).image_real ρ
  refine (congrArg (fun A => DefinableOverBase B (fun _ : Fin (X.arity + 1) => .rv) A) ?_).mpr hR
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hx, hy⟩, h0, hv⟩
    let u : X.domain := ⟨Fin.tail w, hx⟩
    let y := (F.equiv u).val
    rw [coordinateValue_of F j u] at hv
    let z : Fin (m + n + 1) → M := Fin.cons (w 0) (join m n u.val y)
    have hzs : z ∈ sortedUniverse (fun _ : Fin (m + n + 1) => .rv) := by
      intro i
      refine Fin.cases h0.1 (fun l => ?_) i
      change iRV (join m n u.val y l)
      apply GammaBoundedProducts.all_coordinates m n iRV (join m n u.val y)
      · intro l
        rw [join_head]
        exact X.domain_definable.proper _ u.property l
      · intro l
        rw [join_tail]
        exact Y.domain_definable.proper _ (F.equiv u).property l
    refine ⟨z, ⟨⟨⟨u, rfl⟩, hzs⟩, ⟨?_, ?_⟩, hzs⟩, ?_⟩
    · intro i
      fin_cases i
      · exact h0
      · change NonzeroRV (join m n u.val y (tailIndex m n j))
        rw [join_tail]
        exact hy
    · change codeValue (w 0) = codeValue (join m n u.val y (tailIndex m n j))
      rw [join_tail]
      exact hv
    · funext i
      refine Fin.cases rfl (fun l => ?_) i
      change join m n u.val y (headIndex m n l) = w l.succ
      rw [join_head]
      rfl
  · rintro ⟨z, ⟨⟨⟨u, hu⟩, _⟩, ⟨hp, hv⟩, _⟩, rfl⟩
    have htail : Fin.tail (z ∘ ρ) = u.val := by
      funext l
      change z (headIndex m n l).succ = u.val l
      have h := congrFun hu (headIndex m n l)
      change z (headIndex m n l).succ = join m n u.val (F.equiv u).val (headIndex m n l) at h
      rw [h, join_head]
    have hj : z (tailIndex m n j).succ = (F.equiv u).val j := by
      have h := congrFun hu (tailIndex m n j)
      change z (tailIndex m n j).succ = join m n u.val (F.equiv u).val (tailIndex m n j) at h
      rw [h, join_tail]
    change Fin.tail (z ∘ ρ) ∈ coordinateDomain F j ∧ NonzeroRV ((z ∘ ρ) 0) ∧
      codeValue ((z ∘ ρ) 0) = coordinateValue F j (Fin.tail (z ∘ ρ))
    rw [htail]
    have h1 : NonzeroRV (z (tailIndex m n j).succ) := hp 1
    rw [hj] at h1
    refine ⟨⟨u.property, h1⟩, hp 0, ?_⟩
    rw [coordinateValue_of F j u]
    change codeValue (z 0) = _
    rw [← hj]
    exact hv

theorem coordinateDomain_definable {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y)
    (j : Fin Y.arity) : DefinableOverBase B (fun _ : Fin X.arity => .rv) (coordinateDomain F j) := by
  have h := (coordinate_volume_definable F j).image_real (Fin.succ : Fin X.arity → Fin (X.arity + 1))
  refine (congrArg (fun A => DefinableOverBase B (fun _ : Fin X.arity => .rv) A) ?_).mpr h
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨t, ht, htv⟩ := EndpointLogic.codeValue_surjective (coordinateValue F j x)
    exact ⟨Fin.cons t x, ⟨hx, ht, htv⟩, rfl⟩
  · rintro ⟨w, ⟨hw, _, _⟩, rfl⟩
    exact hw

/-- **Bounded targets.** A measured isomorphism out of a doubly bounded chart without `∞`
coordinates lands in a chart whose nonzero coordinates are doubly bounded. Each nonzero image
coordinate is a definable Gamma-valued function on a definable piece of the source, hence bounded
by Lemma 2.41 (`Section2.lemma_2_41_gamma_raw`); its rational-affine input is
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem iso_domainBounded (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} {X Y : Chart B k} (F : Iso X Y)
    (hX : DomainBounded X) (hXf : RVStrictBoundedComparison.InfinityFree X) : DomainBounded Y := by
  have hbound : ∀ j : Fin Y.arity, ∃ γ : Values.Gamma (M := M), ∀ x ∈ coordinateDomain F j,
      γ⁻¹ ≤ coordinateValue F j x ∧ coordinateValue F j x ≤ γ := by
    intro j
    let n := X.arity
    let S := commonRealNames B
    let D := coordinateDomain F j
    have hD : S.Definable LRV D :=
      DefinableOver.raw_definable (DefinableOverBase.common_names (coordinateDomain_definable F j))
    have hraw := DefinableOver.raw_definable (DefinableOverBase.common_names (coordinate_volume_definable F j))
    let π : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cases (.inr 0) Sum.inl
    have hf : S.Definable LRV (Section2.rawGammaFamilyGraph D (fun x => {coordinateValue F j x})) := by
      refine (congrArg (fun A => S.Definable LRV A) ?_).mpr (hraw.preimage_comp π)
      apply Set.ext
      intro z
      exact Iff.rfl
    have hNZ : ∀ x ∈ D, ∀ i, NonzeroRV (x i) :=
      fun x hx i => ⟨X.domain_definable.proper x hx.1 i, hXf x hx.1 i⟩
    have hEb : Section2.RVCodeDoublyBounded D := by
      obtain ⟨β, hβ⟩ := hX
      exact ⟨β, fun x hx i => hβ x hx.1 i (hNZ x hx i)⟩
    exact Section2.lemma_2_41_gamma_raw hc h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
      hκ hs S (commonRealNames_small hκ B hr hγ) (GammaUnaryBijections.nontrivial_commonBase B hΓ)
      D hD hNZ _ hf hEb
  choose γ hγb using hbound
  refine ⟨∏ j, max (γ j) 1, ?_⟩
  intro v hv i hi
  let u := F.equiv.symm ⟨v, hv⟩
  have hu : (F.equiv u).val = v := congrArg Subtype.val (F.equiv.apply_symm_apply ⟨v, hv⟩)
  have hmem : u.val ∈ coordinateDomain F i := ⟨u.property, by
    change NonzeroRV ((F.equiv u).val i)
    rw [hu]
    exact hi⟩
  have hval : coordinateValue F i u.val = codeValue (v i) := by rw [coordinateValue_of, hu]
  obtain ⟨h1, h2⟩ := hγb i u.val hmem
  rw [hval] at h1 h2
  have hle : γ i ≤ ∏ j, max (γ j) 1 := (le_max_left _ _).trans
    (Finset.single_le_prod (fun j _ => le_max_right (γ j) 1) (Finset.mem_univ i))
  exact ⟨(inv_le_inv_iff.mpr hle).trans h1, h2.trans hle⟩

end DiamondIntegral.Section4.RVBoundedDecomposition
