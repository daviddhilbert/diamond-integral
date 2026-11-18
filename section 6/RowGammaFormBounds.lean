import «section 6».RowForms
import «section 6».GammaFormBounds
import «section 6».UniformMixedRadius
import «section 6».ClopenCriterion

/-! (Row-form version for Remark 6.20, replacing `GammaFormBounds`.)
A row-valued function with open levels on a proper invariant set has one
named radius on which it is constant. As for Gamma functions, the equality
relation of values is a proper invariant set in the doubled VF space; its
definability comes from the definable membership graph (equality of rows is
first-order), so no coding of rows is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r q : ℕ} {S : Set M}

/-- Definable relations are closed under negation. -/
theorem relationDefinable_not {P Q : Space LRV M} {r : P.Carrier → Q.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) : P.RelationDefinable Q S (fun x y => ¬ r x y) := by
  have hP := (P.definable_domain S).preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)
  have hQ := (Q.definable_domain S).preimage_comp (Sum.inr : Q.Index → P.Index ⊕ Q.Index)
  have h := (hP.inter hQ).inter (Set.Definable.compl hr)
  change S.Definable LRV _
  convert h using 1
  ext z
  constructor
  · rintro ⟨hx, hy, hn⟩
    refine ⟨⟨hx, hy⟩, ?_⟩
    rintro ⟨hx', hy', hr'⟩
    exact hn hr'
  · rintro ⟨⟨hx, hy⟩, hn⟩
    exact ⟨hx, hy, fun hr' => hn ⟨hx, hy, hr'⟩⟩

/-- A block of VF coordinates as an actual map. -/
def vfBlockMap (sel : Fin n → Fin (n+n)) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n+n) r) S) (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let P := rawMixedSpace (M := M) (n+n) r
  let Q := rawMixedSpace (M := M) n r
  let F (p : Mixed M (n+n) r) : Mixed M n r := (p.1 ∘ sel, p.2)
  let codes (z : Fin (n+n) ⊕ Fin r → M) : Fin n ⊕ Fin r → M :=
    Sum.elim (fun i => z (.inl (sel i))) (z ∘ Sum.inr)
  have hd : S.DefinableMap LRV codes := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hdom (c : P.domain) : codes c.val ∈ Q.domain := by
    obtain ⟨a, ha⟩ := c.property.1
    refine ⟨⟨a ∘ sel, ?_⟩, c.property.2⟩
    funext i
    exact congrFun ha (sel i)
  refine Map.ofCodes _ F codes hd hdom ?_
  intro c
  apply mixedValues_injective
  have h := mixedValues_decode ⟨codes c.val, hdom c⟩
  refine h.trans ?_
  funext i
  cases i with
  | inl i => exact (congrFun (mixedValues_decode c) (.inl (sel i))).symm
  | inr i => exact (congrFun (mixedValues_decode c) (.inr i)).symm

theorem vfBlockMap_apply (sel : Fin n → Fin (n+n))
    (p : DefSet.univ (rawMixedSpace (M := M) (n+n) r) S) :
    (vfBlockMap (S := S) sel p).val = (p.val.1 ∘ sel, p.val.2) := rfl

theorem vfBlockMap_graph_iff (sel : Fin n → Fin (n+n)) (p : Mixed M (n+n) r) (x : Mixed M n r) :
    (vfBlockMap (S := S) sel).graph p x ↔ x = (p.1 ∘ sel, p.2) := by
  constructor
  · rintro ⟨a, rfl, ha⟩
    exact ha.symm
  · intro hx
    exact ⟨⟨p, Set.mem_univ _⟩, rfl, hx.symm⟩

/-- The equality relation of row values, in the doubled VF space. -/
def rowLevelRelation (A : Set (Mixed M n r)) (f : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) :
    Set (Mixed M (n+n) r) :=
  {p | firstVFBlock p ∈ A ∧ secondVFBlock p ∈ A ∧ f (firstVFBlock p) = f (secondVFBlock p)}

theorem rowLevelRelation_vfBounded {A : Set (Mixed M n r)} (hA : VFBounded A)
    (f : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) : VFBounded (rowLevelRelation A f) := by
  obtain ⟨η, hη⟩ := hA
  refine ⟨η, ?_⟩
  intro p hp i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact hη (firstVFBlock p) hp.1 i
  · exact hη (secondVFBlock p) hp.2.1 i

theorem rowLevelRelation_rvBounded {A : Set (Mixed M n r)} (hA : RVSupportDoublyBounded A)
    (f : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) :
    RVSupportDoublyBounded (rowLevelRelation A f) := by
  obtain ⟨η, hη⟩ := hA
  exact ⟨η, fun p hp i => hη (firstVFBlock p) hp.1 i⟩

theorem rowLevelRelation_clopen_fibres {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    (A : Set (Mixed M n r)) (f : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier)
    (hA : ∀ u, IsClopen (vfFibre A u))
    (hlevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A ∧ f (a,u) = γ})
    (u : Fin r → RVInfinity M) : IsClopen (vfFibre (rowLevelRelation A f) u) := by
  have hcont : Continuous (fun x : Fin (n+n) → VF M => (x ∘ Fin.castAdd n, x ∘ Fin.natAdd n)) :=
    (continuous_pi (fun _ => continuous_apply _)).prodMk (continuous_pi (fun _ => continuous_apply _))
  exact (isClopen_equal_levels (vfFibre A u) (fun a => f (a,u)) (hA u) (hlevels u)).preimage hcont

theorem rowLevelRelation_definable (A : Set (Mixed M n r))
    (hAdef : (rawMixedSpace (M := M) n r).Definable S A)
    (f : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) (hf : MixedRowGraphDefinable S A f) :
    (rawMixedSpace (M := M) (n+n) r).Definable S (rowLevelRelation A f) := by
  let P := rawMixedSpace (M := M) (n+n) r
  let Q := rawMixedSpace (M := M) n r
  let R := rawRVSpace (M := M) q
  let fst := vfBlockMap (S := S) (n := n) (r := r) (Fin.castAdd n)
  let snd := vfBlockMap (S := S) (n := n) (r := r) (Fin.natAdd n)
  have hA1 : P.Definable S {p | ∃ x, fst.graph p x ∧ x ∈ A} :=
    (fst.graph_definable.inter P Q (hAdef.right_relation P Q)).exists_right P Q
  have hA2 : P.Definable S {p | ∃ x, snd.graph p x ∧ x ∈ A} :=
    (snd.graph_definable.inter P Q (hAdef.right_relation P Q)).exists_right P Q
  have hD1 : P.RelationDefinable R S (fun p v => ∃ x, fst.graph p x ∧ (x ∈ A ∧ v ∈ f x)) :=
    fst.graph_definable.comp P Q R hf
  have hD2 : P.RelationDefinable R S (fun p v => ∃ x, snd.graph p x ∧ (x ∈ A ∧ v ∈ f x)) :=
    snd.graph_definable.comp P Q R hf
  have hBad : P.RelationDefinable R S (fun p v =>
      ((∃ x, fst.graph p x ∧ (x ∈ A ∧ v ∈ f x)) ∧ ¬ (∃ x, snd.graph p x ∧ (x ∈ A ∧ v ∈ f x))) ∨
      (¬ (∃ x, fst.graph p x ∧ (x ∈ A ∧ v ∈ f x)) ∧ (∃ x, snd.graph p x ∧ (x ∈ A ∧ v ∈ f x)))) :=
    (hD1.inter P R (relationDefinable_not hD2)).union P R ((relationDefinable_not hD1).inter P R hD2)
  have h := (hA1.inter P hA2).inter P ((hBad.exists_right P R).compl P)
  convert h using 1
  ext p
  have hfst : ∀ x, fst.graph p x ↔ x = firstVFBlock p := fun x => vfBlockMap_graph_iff _ p x
  have hsnd : ∀ x, snd.graph p x ↔ x = secondVFBlock p := fun x => vfBlockMap_graph_iff _ p x
  constructor
  · intro hp
    obtain ⟨h1, h2, he⟩ := hp
    refine ⟨⟨⟨firstVFBlock p, (hfst _).mpr rfl, h1⟩, ⟨secondVFBlock p, (hsnd _).mpr rfl, h2⟩⟩, ?_⟩
    rintro ⟨v, hv⟩
    rcases hv with ⟨⟨x, hx, _, hvx⟩, hn⟩ | ⟨hn, ⟨x, hx, _, hvx⟩⟩
    · rw [(hfst x).mp hx] at hvx
      exact hn ⟨secondVFBlock p, (hsnd _).mpr rfl, h2, he ▸ hvx⟩
    · rw [(hsnd x).mp hx] at hvx
      exact hn ⟨firstVFBlock p, (hfst _).mpr rfl, h1, he.symm ▸ hvx⟩
  · rintro ⟨⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩, hno⟩
    rw [(hfst x1).mp hx1] at h1
    rw [(hsnd x2).mp hx2] at h2
    refine ⟨h1, h2, ?_⟩
    ext v
    constructor
    · intro hv
      by_contra hn
      exact hno ⟨v, Or.inl ⟨⟨firstVFBlock p, (hfst _).mpr rfl, h1, hv⟩,
        fun ⟨x, hx, _, hvx⟩ => hn (((hsnd x).mp hx) ▸ hvx)⟩⟩
    · intro hv
      by_contra hn
      exact hno ⟨v, Or.inr ⟨fun ⟨x, hx, _, hvx⟩ => hn (((hfst x).mp hx) ▸ hvx),
        ⟨secondVFBlock p, (hsnd _).mpr rfl, h2, hv⟩⟩⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem gammaFunction_uniform_named_radius_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (f : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier)
    (hf : MixedRowGraphDefinable S A f)
    (hlevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A ∧ f (a,u) = γ}) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ (1 : Gamma M) ≤ δ ∧
      ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
        Congruent (fun _ => δ) a b → f (a,u) = f (b,u) := by
  let R := rowLevelRelation A f
  have hR : ProperInvariant S R :=
    (lemma_6_5 h00 hc hκ hs hv R (rowLevelRelation_definable A hA.definable f hf)
      (rowLevelRelation_vfBounded hA.vfBounded f) (rowLevelRelation_rvBounded hA.rvBounded f)).mpr
        (rowLevelRelation_clopen_fibres (G := G) A f (hA.clopen_fibres hv) hlevels)
  obtain ⟨δ,hδ,hδ0,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hR
  refine ⟨δ,hδ,hδ0,?_⟩
  intro u a ha b hb hab
  have hp : (Fin.append a a,u) ∈ R := by
    change firstVFBlock (Fin.append a a,u) ∈ A ∧ secondVFBlock (Fin.append a a,u) ∈ A ∧ _
    rw [firstVFBlock_append,secondVFBlock_append]
    exact ⟨ha,ha,rfl⟩
  have hclose : Congruent (fun _ => δ) (Fin.append a a) (Fin.append a b) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left,sub_self]
      exact gamma_lt_value_zero δ
    · simpa only [Fin.append_right] using hab i
  have hq := (hInv u _ _ hclose).mp hp
  change firstVFBlock (Fin.append a b,u) ∈ A ∧ secondVFBlock (Fin.append a b,u) ∈ A ∧ _ at hq
  rw [firstVFBlock_append,secondVFBlock_append] at hq
  exact hq.2.2

end DiamondIntegral.Section6
