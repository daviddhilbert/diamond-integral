import Section3.RVOperations
import Section4.RVLabelCompression
import «section 6».ApertureRestrictionData
import «section 6».CentripetalCoefficientRefinement
import «section 6».VFProjection
import «section 6».DefinableSurjectiveDescent

/-! Row forms (Remark 6.20). A powerset-valued function `f : H → 𝒫(RV^q)`
is carried as a *row form*: a function from a definable set to row values
(sets of RV tuples) whose membership graph is definable. Row forms imitate
definable maps into the Gamma presentation: they compose with actual maps
on the right, and descend through surjections that respect them. A Gamma
form `ω` is the special case of the rows `ω(p)^♯ = {c : vrv c = ω p}`.

The interface mirrors `GammaFormMaps`: `rowFormExtension` plays the role of
`gammaFormExtension` (with the empty row outside the domain). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s q : ℕ}

/-- A row value: a set of RV tuples (an element of the full set of rows, so that
it behaves like an element of `DefSet.univ`). -/
abbrev RowValue (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (q : ℕ) :=
  ↥(Set.univ : Set (Set (rawRVSpace (M := M) q).Carrier))

/-- A row form on a definable mixed set: row values with a definable membership graph,
whose entries lie in one doubly bounded box (as for the RV support of a proper
invariant relation). -/
structure RowFormOn (A : DefSet (rawMixedSpace (M := M) n r) S) (q : ℕ) where
  toFun : A → RowValue M q
  rows_definable : (rawMixedSpace (M := M) n r).RelationDefinable (rawRVSpace (M := M) q) S
    (fun x u => ∃ a : A, a.val = x ∧ u ∈ (toFun a).val)
  bounded : ∃ γ : Gamma M, ∀ a, ∀ v ∈ (toFun a).val, ∀ i,
    (γ⁻¹).val ≤ Values.vrv (v i) ∧ Values.vrv (v i) ≤ γ.val

instance {A : DefSet (rawMixedSpace (M := M) n r) S} :
    CoeFun (RowFormOn A q) (fun _ => A → RowValue M q) := ⟨RowFormOn.toFun⟩

namespace RowFormOn

variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

/-- The domain marker: the zero tuple, never an entry of a bounded row when `q ≠ 0`. -/
def rowMarker (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (q : ℕ) : (rawRVSpace (M := M) q).Carrier :=
  fun _ => (0 : CanonicalRV.RVSort M)

/-- The marked membership graph: row entries together with the domain marker. -/
def graph (ρ : RowFormOn A q) (x : (rawMixedSpace (M := M) n r).Carrier)
    (u : (rawRVSpace (M := M) q).Carrier) : Prop :=
  ∃ a : A, a.val = x ∧ (u ∈ (ρ a).val ∨ u = rowMarker M q)

theorem rowMarker_definable : (rawRVSpace (M := M) q).Definable S {rowMarker M q} := by
  have h := Set.definable_iInter_of_finite (fun i : Fin q => SpecialTransformations.Section4.rvZero_coordinate_definable S i)
  have hD := ((rawRVSpace (M := M) q).definable_domain S).inter h
  change S.Definable LRV _
  convert hD using 1
  ext z
  constructor
  · rintro ⟨hz, hm⟩
    refine ⟨hz, ?_⟩
    simp only [Set.mem_iInter]
    intro i
    change z i = iRVZero
    have hdec : (rawRVSpace (M := M) q).decode ⟨z, hz⟩ = rowMarker M q := hm
    have h2 : rvValues ((rawRVSpace (M := M) q).decode ⟨z, hz⟩) i = z i :=
      congrFun (rvValues_decode ⟨z, hz⟩) i
    rw [hdec] at h2
    exact h2.symm.trans RVOperations.zero_val
  · rintro ⟨hz, hzero⟩
    refine ⟨hz, ?_⟩
    apply Set.mem_singleton_iff.mpr
    apply rvValues_injective
    rw [rvValues_decode]
    funext i
    have h := Set.mem_iInter.mp hzero i
    change z i = iRVZero at h
    exact h.trans RVOperations.zero_val.symm

theorem graph_definable (ρ : RowFormOn A q) :
    (rawMixedSpace (M := M) n r).RelationDefinable (rawRVSpace (M := M) q) S ρ.graph := by
  have hm := (A.definable.left_relation (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q)).inter
    (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q)
    ((rowMarker_definable (M := M) (S := S) (q := q)).right_relation (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q))
  apply (ρ.rows_definable.union (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q) hm).congr
    (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q)
  intro x u
  constructor
  · rintro (⟨a, rfl, hu⟩ | ⟨hx, hu⟩)
    · exact ⟨a, rfl, Or.inl hu⟩
    · exact ⟨⟨x, hx⟩, rfl, Or.inr hu⟩
  · rintro ⟨a, rfl, hu | hu⟩
    · exact Or.inl ⟨a, rfl, hu⟩
    · exact Or.inr ⟨a.property, hu⟩

theorem rowMarker_not_mem [NeZero q] (ρ : RowFormOn A q) (a : A) : rowMarker M q ∉ (ρ a).val := by
  intro h
  obtain ⟨γ, hγ⟩ := ρ.bounded
  have h0 := (hγ a _ h 0).2
  change Values.vrv (0 : CanonicalRV.RVSort M) ≤ γ.val at h0
  rw [RVOperations.vrv_zero] at h0
  have hinf : Values.infinity (M := M) = 0 := by
    rw [← RVOperations.vrv_zero]
    exact congrArg Values.vrv (Subtype.ext RVOperations.zero_val.symm)
  have h3 : Values.infinity (M := M) ≤ γ.val := by
    calc Values.infinity (M := M) = 0 := hinf
      _ ≤ γ.val := h0
  exact γ.property (le_antisymm (Values.le_infinity _) h3)

theorem graph_apply_iff (ρ : RowFormOn A q) (a : A) (u : (rawRVSpace (M := M) q).Carrier) :
    ρ.graph a.val u ↔ (u ∈ (ρ a).val ∨ u = rowMarker M q) := by
  constructor
  · rintro ⟨a', ha', hu⟩
    have he : a' = a := Subtype.ext ha'
    subst he
    exact hu
  · intro hu
    exact ⟨a, rfl, hu⟩

/-- Pull back along an actual map (imitates `Map.comp`). -/
def comp (ρ : RowFormOn A q) (g : Map B A) : RowFormOn B q where
  toFun b := ρ (g b)
  rows_definable := by
    have h := g.graph_definable.comp (rawMixedSpace (M := M) m s) (rawMixedSpace (M := M) n r)
      (rawRVSpace (M := M) q) ρ.rows_definable
    apply h.congr (rawMixedSpace (M := M) m s) (rawRVSpace (M := M) q)
    intro x u
    constructor
    · rintro ⟨y, ⟨b, hbx, hby⟩, a, hay, hu⟩
      refine ⟨b, hbx, ?_⟩
      have hab : g b = a := Subtype.ext (hby.trans hay.symm)
      change u ∈ (ρ (g b)).val
      rw [hab]
      exact hu
    · rintro ⟨b, hbx, hu⟩
      exact ⟨(g b).val, ⟨b, hbx, rfl⟩, g b, rfl, hu⟩
  bounded := by
    obtain ⟨γ, hγ⟩ := ρ.bounded
    exact ⟨γ, fun b v hv => hγ (g b) v hv⟩

@[ext] theorem ext {ρ η : RowFormOn A q} (h : ∀ a, ρ a = η a) : ρ = η := by
  cases ρ
  cases η
  congr
  funext a
  exact h a

@[simp] theorem comp_apply (ρ : RowFormOn A q) (g : Map B A) (b : B) : (ρ.comp g) b = ρ (g b) := rfl

theorem comp_comp {t k : ℕ} {C : DefSet (rawMixedSpace (M := M) t k) S}
    (ρ : RowFormOn A q) (g : Map B A) (h : Map C B) (c : C) :
    ((ρ.comp g).comp h) c = (ρ.comp (g.comp h)) c := rfl

/-- Descent through a surjection whose fibres have constant rows
(imitates `definableSurjectiveDescent`). -/
def descent (π : Map A B) (hπ : Function.Surjective π) (ρ : RowFormOn A q)
    (hρ : ∀ a a' : A, π a = π a' → ρ a = ρ a') : RowFormOn B q where
  toFun b := ρ (Classical.choose (hπ b))
  rows_definable := by
    have h := (π.graph_definable.swap (rawMixedSpace (M := M) n r) (rawMixedSpace (M := M) m s)).comp
      (rawMixedSpace (M := M) m s) (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q) ρ.rows_definable
    apply h.congr (rawMixedSpace (M := M) m s) (rawRVSpace (M := M) q)
    intro y u
    constructor
    · rintro ⟨x, ⟨a, hax, hay⟩, a', hax', hu⟩
      have haa : a = a' := Subtype.ext (hax.trans hax'.symm)
      subst haa
      have hb : y ∈ B.carrier := hay ▸ (π a).property
      refine ⟨⟨y, hb⟩, rfl, ?_⟩
      have hpa : π a = ⟨y, hb⟩ := Subtype.ext hay
      have hc := Classical.choose_spec (hπ ⟨y, hb⟩)
      have he := hρ _ a (hc.trans hpa.symm)
      change u ∈ (ρ (Classical.choose (hπ ⟨y, hb⟩))).val
      rw [he]
      exact hu
    · rintro ⟨b, rfl, hu⟩
      let a : A := Classical.choose (hπ b)
      exact ⟨a.val, ⟨a, rfl, congrArg Subtype.val (Classical.choose_spec (hπ b))⟩, a, rfl, hu⟩
  bounded := by
    obtain ⟨γ, hγ⟩ := ρ.bounded
    exact ⟨γ, fun b v hv => hγ _ v hv⟩

theorem descent_apply (π : Map A B) (hπ : Function.Surjective π) (ρ : RowFormOn A q)
    (hρ : ∀ a a' : A, π a = π a' → ρ a = ρ a') (a : A) : ρ.descent π hπ hρ (π a) = ρ a :=
  hρ _ a (Classical.choose_spec (hπ (π a)))

end RowFormOn

/-- Definability of the membership graph of a row-valued function on a set
(imitates definability of `mixedGammaGraph`). -/
def MixedRowGraphDefinable (S : Set M) (A : Set (Mixed M n r))
    (ω : Mixed M n r → Set (rawRVSpace (M := M) q).Carrier) : Prop :=
  (rawMixedSpace (M := M) n r).RelationDefinable (rawRVSpace (M := M) q) S
    (fun x u => x ∈ A ∧ u ∈ ω x)

/-- Values on all of the mixed space, with the empty row outside the domain. -/
def rowFormExtension {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : RowFormOn A q) (p : Mixed M n r) : Set (rawRVSpace (M := M) q).Carrier :=
  if hp : p ∈ A.carrier then (f ⟨p, hp⟩).val else ∅

theorem rowFormExtension_at {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : RowFormOn A q) (p : A) : rowFormExtension f p.val = (f p).val := by
  simp only [rowFormExtension, dite_eq_left_iff, p.property, not_true_eq_false, IsEmpty.forall_iff,
    dite_true]

theorem rowFormExtension_graph_definable {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : RowFormOn A q) : MixedRowGraphDefinable S A.carrier (rowFormExtension f) := by
  apply f.rows_definable.congr (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q)
  intro x u
  constructor
  · rintro ⟨a, rfl, hu⟩
    exact ⟨a.property, by rw [rowFormExtension_at]; exact hu⟩
  · rintro ⟨hx, hu⟩
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    rw [← rowFormExtension_at f ⟨x, hx⟩]
    exact hu

theorem rowFormExtension_comp_at {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : RowFormOn A q) (g : Map B A) (p : B) :
    rowFormExtension (f.comp g) p.val = rowFormExtension f (g p).val := by
  rw [rowFormExtension_at, rowFormExtension_at]
  rfl

theorem rowFormExtension_inverse_transport {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A B) (hf : Function.Bijective f) (ω : RowFormOn A q) (p : A) :
    rowFormExtension (ω.comp (f.inverse hf)) (f p).val = (ω p).val := by
  rw [rowFormExtension_at]
  change (ω (f.inverse hf (f p))).val = (ω p).val
  rw [Map.inverse_apply]

/-- A row form from a definable relation with `q` extra RV coordinates. -/
def rowFormOfRelation (A : DefSet (rawMixedSpace (M := M) n r) S)
    (R : (rawMixedSpace (M := M) n r).Carrier → (rawRVSpace (M := M) q).Carrier → Prop)
    (hR : (rawMixedSpace (M := M) n r).RelationDefinable (rawRVSpace (M := M) q) S R)
    (hB : ∃ γ : Gamma M, ∀ a : A, ∀ v, R a.val v → ∀ i,
      (γ⁻¹).val ≤ Values.vrv (v i) ∧ Values.vrv (v i) ≤ γ.val) :
    RowFormOn A q where
  toFun a := ⟨{u | R a.val u}, Set.mem_univ _⟩
  rows_definable := by
    have hA := A.definable.left_relation (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q)
    apply (hA.inter (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q) hR).congr
      (rawMixedSpace (M := M) n r) (rawRVSpace (M := M) q)
    intro x u
    constructor
    · rintro ⟨hx, hu⟩
      exact ⟨⟨x, hx⟩, rfl, hu⟩
    · rintro ⟨a, rfl, hu⟩
      exact ⟨a.property, hu⟩
  bounded := hB

theorem rowFormOfRelation_apply (A : DefSet (rawMixedSpace (M := M) n r) S)
    (R : (rawMixedSpace (M := M) n r).Carrier → (rawRVSpace (M := M) q).Carrier → Prop)
    (hR : (rawMixedSpace (M := M) n r).RelationDefinable (rawRVSpace (M := M) q) S R)
    (hB : ∃ γ : Gamma M, ∀ a : A, ∀ v, R a.val v → ∀ i,
      (γ⁻¹).val ≤ Values.vrv (v i) ∧ Values.vrv (v i) ≤ γ.val) (a : A) :
    (rowFormOfRelation A R hR hB a).val = {u | R a.val u} := rfl

end DiamondIntegral.Section6
