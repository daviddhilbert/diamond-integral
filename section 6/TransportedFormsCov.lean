import «section 6».DiamondGroupoid
import «section 6».ClopenCriterion

/-! (Moved from `section 7/IntermediateFormsProofCov.lean`, branch `claude/intermediate-forms-proof`, commit 7b2b7ed2, for the repaired Definition 6.34: intermediate objects of a factorization carry transported forms.)

Covariance of locally constant `Γ`-forms.

A definable `Γ`-form on a proper invariant set which is locally constant in each
label fibre is covariant with radii named over each label, in the shape of the
`formCovariant` field of `VFObject`. The proof applies the clopen criterion
(Lemma 6.5, `clopen_has_named_invariant_radius`) to the clopen, bounded set of
pairs of points of a label fibre on which the form agrees. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section6.TransportedForms
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n s : ℕ}

/-- Selection of VF coordinates along `e`, keeping the RV labels, as a definable map. -/
def vfSelectMap {k : ℕ} (e : Fin n → Fin k) (A : DefSet (rawMixedSpace (M := M) k s) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n s) S) := by
  let P := rawMixedSpace (M := M) k s
  let Q := rawMixedSpace (M := M) n s
  let F (z : P.Index → M) : Q.Index → M :=
    Sum.elim (fun i => z (.inl (e i))) (fun j => z (.inr j))
  have hCode (c : P.domain) : mixedValues ((P.decode c).1 ∘ e, (P.decode c).2) = F c.val := by
    funext i
    rcases i with i | i
    · exact congrFun (mixedValues_decode c) (.inl (e i))
    · exact congrFun (mixedValues_decode c) (.inr i)
  have hDom (c : P.domain) : F c.val ∈ Q.domain := by
    rw [← hCode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A (fun x => (x.1 ∘ e, x.2)) F
    (fun i => by
      cases i with
      | inl i => exact Set.DefinableFun.proj LRV
      | inr i => exact Set.DefinableFun.proj LRV) hDom ?_
  intro c
  exact mixedValues_injective ((mixedValues_decode _).trans (hCode c).symm)

omit [M ⊨ Axioms.ACVF] in
theorem vfSelectMap_value {k : ℕ} (e : Fin n → Fin k) (A : DefSet (rawMixedSpace (M := M) k s) S)
    (u : A) : (vfSelectMap e A u).val = (u.val.1 ∘ e, u.val.2) := rfl

/-- The pairs of points of `B` with the same label on which `ω` agrees form a
definable set over the original base. -/
theorem agreementPairs_definable (B : DefSet (rawMixedSpace (M := M) n s) S)
    (ω : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    (rawMixedSpace (M := M) (n + n) s).Definable S
      {p : Mixed M (n + n) s | ∃ (h1 : (p.1 ∘ Fin.castAdd n, p.2) ∈ B.carrier)
        (h2 : (p.1 ∘ Fin.natAdd n, p.2) ∈ B.carrier),
        gammaMapValue ω ⟨_, h1⟩ = gammaMapValue ω ⟨_, h2⟩} := by
  let P := rawMixedSpace (M := M) (n + n) s
  let U := DefSet.univ P S
  have hL := (vfSelectMap (Fin.castAdd n) U).definable_preimage B.definable
  have hR := (vfSelectMap (Fin.natAdd n) U).definable_preimage B.definable
  have hL' : P.Definable S {p : Mixed M (n + n) s | (p.1 ∘ Fin.castAdd n, p.2) ∈ B.carrier} := by
    convert hL using 1
    ext p
    exact ⟨fun h => ⟨⟨p, Set.mem_univ _⟩, rfl, h⟩, fun ⟨a, ha, h⟩ => ha ▸ h⟩
  have hR' : P.Definable S {p : Mixed M (n + n) s | (p.1 ∘ Fin.natAdd n, p.2) ∈ B.carrier} := by
    convert hR using 1
    ext p
    exact ⟨fun h => ⟨⟨p, Set.mem_univ _⟩, rfl, h⟩, fun ⟨a, ha, h⟩ => ha ▸ h⟩
  let C : DefSet P S := ⟨_, hL'.inter P hR'⟩
  let Lc : Map C B := (vfSelectMap (Fin.castAdd n) C).corestrict (fun a => a.property.1)
  let Rc : Map C B := (vfSelectMap (Fin.natAdd n) C).corestrict (fun a => a.property.2)
  let Q := rawGammaPresentation (M := M)
  let h := (ω.comp Lc).pair (ω.comp Rc)
  have hDiag : (Q.prod Q).Definable S {z | z.1 = z.2} :=
    (Q.definable_prod_iff Q S Eq).mpr (Q.diagonal_definable.mono (Set.empty_subset S))
  have hD := h.definable_preimage hDiag
  convert hD using 1
  ext p
  constructor
  · rintro ⟨h1, h2, heq⟩
    exact ⟨⟨p, h1, h2⟩, rfl, heq⟩
  · rintro ⟨a, rfl, he⟩
    exact ⟨a.property.1, a.property.2, he⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- A set which is locally invariant under congruence with a constant radius is clopen. -/
theorem isClopen_of_locallyInvariant
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) {k : ℕ}
    (E : Set (Fin k → VF M))
    (h : ∀ z, ∃ c : Gamma M, ∀ w, Congruent (fun _ => c) z w → (w ∈ E ↔ z ∈ E)) :
    IsClopen E := by
  have hopen : ∀ F : Set (Fin k → VF M),
      (∀ z ∈ F, ∃ c : Gamma M, ∀ w, Congruent (fun _ => c) z w → w ∈ F) → IsOpen F :=
    fun F hF => isOpen_iff_mem_nhds.mpr fun z hz => by
      obtain ⟨c, hc⟩ := hF z hz
      exact Filter.mem_of_superset (congruent_ball_mem_nhds (G := G) hv _ z) (fun w hw => hc w hw)
  refine ⟨isOpen_compl_iff.mp (hopen _ fun z hz => ?_), hopen _ fun z hz => ?_⟩
  · obtain ⟨c, hc⟩ := h z
    exact ⟨c, fun w hw hwE => hz ((hc w hw).mp hwE)⟩
  · obtain ⟨c, hc⟩ := h z
    exact ⟨c, fun w hw => (hc w hw).mpr hz⟩

omit [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] in
theorem gammaMapValue_congr_vf {B : DefSet (rawMixedSpace (M := M) n s) S}
    (ω : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)) {t : Fin s → RVInfinity M}
    {a a' : Fin n → VF M} (e : a = a') (h : (a, t) ∈ B.carrier) (h' : (a', t) ∈ B.carrier) :
    gammaMapValue ω ⟨(a, t), h⟩ = gammaMapValue ω ⟨(a', t), h'⟩ := by
  subst e
  rfl

/-- **Covariance of locally constant forms.** A definable `Γ`-form on a proper
invariant set which is locally constant in each label fibre is covariant with
radii named over each label. -/
theorem covariant_of_locallyConstant (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (B : DefSet (rawMixedSpace (M := M) n s) S) (hB : ProperInvariant S B.carrier)
    (ω : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hloc : ∀ (t : Fin s → RVInfinity M) (x : Fin n → VF M) (hx : (x, t) ∈ B.carrier),
      ∃ ρ : Gamma M, ∀ (y : Fin n → VF M) (hy : (y, t) ∈ B.carrier),
        Congruent (fun _ => ρ) x y → gammaMapValue ω ⟨(x, t), hx⟩ = gammaMapValue ω ⟨(y, t), hy⟩) :
    ∀ t : Fin s → RVInfinity M, ∃ α : Fin n → Gamma M, NamedRadii S t α ∧
      ∀ x y (hx : (x, t) ∈ B.carrier) (hy : (y, t) ∈ B.carrier), Congruent α x y →
        gammaMapValue ω ⟨(x, t), hx⟩ = gammaMapValue ω ⟨(y, t), hy⟩ := by
  intro t
  obtain ⟨α, -, hαX⟩ := hB.radii t
  obtain ⟨d, hd⟩ := (Set.finite_range α).bddAbove
  have hαd : ∀ i, α i ≤ d := fun i => hd (Set.mem_range_self i)
  let E : Set (Fin (n + n) → VF M) :=
    {z | ∃ (h1 : (z ∘ Fin.castAdd n, t) ∈ B.carrier) (h2 : (z ∘ Fin.natAdd n, t) ∈ B.carrier),
      gammaMapValue ω ⟨_, h1⟩ = gammaMapValue ω ⟨_, h2⟩}
  have hEdef : (S ∪ Set.range (rvValues t)).Definable LRV (vfValues '' E) :=
    properInvariant_fibre_definable _ (agreementPairs_definable B ω) t
  have restrict : ∀ (e : Fin n → Fin (n + n)) (c : Gamma M) (z w : Fin (n + n) → VF M),
      Congruent (fun _ => c) z w → Congruent (fun _ => c) (z ∘ e) (w ∘ e) :=
    fun e _ _ _ h i => h (e i)
  have hlocE : ∀ z, ∃ c : Gamma M, ∀ w, Congruent (fun _ => c) z w → (w ∈ E ↔ z ∈ E) := by
    intro z
    have key : ∀ e : Fin n → Fin (n + n), ∃ c : Gamma M, d ≤ c ∧ ∀ w,
        Congruent (fun _ => c) z w → ∀ (h1 : (z ∘ e, t) ∈ B.carrier) (h2 : (w ∘ e, t) ∈ B.carrier),
          gammaMapValue ω ⟨_, h1⟩ = gammaMapValue ω ⟨_, h2⟩ := by
      intro e
      by_cases hz : (z ∘ e, t) ∈ B.carrier
      · obtain ⟨ρ, hρ⟩ := hloc t (z ∘ e) hz
        exact ⟨max d ρ, le_max_left _ _, fun w hw _ h2 =>
          hρ _ h2 ((restrict e _ z w hw).of_larger_radius (fun _ => le_max_right d ρ))⟩
      · exact ⟨d, le_rfl, fun _ _ h1 _ => absurd h1 hz⟩
    obtain ⟨c1, hd1, hc1⟩ := key (Fin.castAdd n)
    obtain ⟨c2, hd2, hc2⟩ := key (Fin.natAdd n)
    refine ⟨max c1 c2, fun w hw => ?_⟩
    have hw1 : Congruent (fun _ => c1) z w := hw.of_larger_radius (fun _ => le_max_left _ _)
    have hw2 : Congruent (fun _ => c2) z w := hw.of_larger_radius (fun _ => le_max_right _ _)
    have hm : ∀ (e : Fin n → Fin (n + n)) (c : Gamma M), d ≤ c → Congruent (fun _ => c) z w →
        ((w ∘ e, t) ∈ B.carrier ↔ (z ∘ e, t) ∈ B.carrier) := fun e c hdc h =>
      (hαX (z ∘ e) (w ∘ e)
        ((restrict e c z w h).of_larger_radius (fun i => (hαd i).trans hdc))).symm
    constructor
    · rintro ⟨h1, h2, heq⟩
      have h1' := (hm _ c1 hd1 hw1).mp h1
      have h2' := (hm _ c2 hd2 hw2).mp h2
      exact ⟨h1', h2', (hc1 w hw1 h1' h1).trans (heq.trans (hc2 w hw2 h2' h2).symm)⟩
    · rintro ⟨h1, h2, heq⟩
      have h1' := (hm _ c1 hd1 hw1).mpr h1
      have h2' := (hm _ c2 hd2 hw2).mpr h2
      exact ⟨h1', h2', (hc1 w hw1 h1 h1').symm.trans (heq.trans (hc2 w hw2 h2 h2'))⟩
  have hEclopen : IsClopen E := isClopen_of_locallyInvariant (G := G) hv E hlocE
  have hEbd : ∃ γ : Gamma M, ∀ x ∈ E, ∀ i, γ.val ≤ vfValue (x i) := by
    obtain ⟨γ, hγ⟩ := hB.vfBounded
    refine ⟨γ, fun z hz i => ?_⟩
    obtain ⟨h1, h2, -⟩ := hz
    induction i using Fin.addCases with
    | left j => exact hγ _ h1 j
    | right j => exact hγ _ h2 j
  obtain ⟨δ, hδdef, hδ⟩ :=
    clopen_has_named_invariant_radius (G := G) h00 hc hκ hs hv E hEdef hEclopen hEbd
  have memE : ∀ (a b : Fin n → VF M) (ha : (a, t) ∈ B.carrier) (hb : (b, t) ∈ B.carrier),
      (Fin.append a b ∈ E ↔ gammaMapValue ω ⟨(a, t), ha⟩ = gammaMapValue ω ⟨(b, t), hb⟩) := by
    intro a b ha hb
    have e1 : Fin.append a b ∘ Fin.castAdd n = a := funext (Fin.append_left a b)
    have e2 : Fin.append a b ∘ Fin.natAdd n = b := funext (Fin.append_right a b)
    constructor
    · rintro ⟨h1, h2, heq⟩
      exact (gammaMapValue_congr_vf ω e1.symm ha h1).trans
        (heq.trans (gammaMapValue_congr_vf ω e2 h2 hb))
    · intro heq
      have h1 : (Fin.append a b ∘ Fin.castAdd n, t) ∈ B.carrier := by rw [e1]; exact ha
      have h2 : (Fin.append a b ∘ Fin.natAdd n, t) ∈ B.carrier := by rw [e2]; exact hb
      exact ⟨h1, h2, (gammaMapValue_congr_vf ω e1 h1 ha).trans
        (heq.trans (gammaMapValue_congr_vf ω e2.symm hb h2))⟩
  refine ⟨fun _ => δ, fun _ => hδdef, fun x y hx hy hxy => ?_⟩
  have hxE : Fin.append x x ∈ E := (memE x x hx hx).mpr rfl
  have hcong : Congruent (fun _ => δ) (Fin.append x x) (Fin.append x y) := by
    intro i
    induction i using Fin.addCases with
    | left j =>
      simp only [Fin.append_left]
      exact DiamondIntegral.Section6.Congruent.refl (fun _ => δ) x j
    | right j =>
      simp only [Fin.append_right]
      exact hxy j
  exact (memE x y hx hy).mp ((hδ _ _ hcong).mp hxE)

end DiamondIntegral.Section6.TransportedForms
