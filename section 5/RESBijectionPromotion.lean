import «section 5».RESBijectionRealization
import IntegrationSection6.GammaRowBijectionPromotion

/-! Every actual underlying RES bijection at a parameter admits a full
original-base graph schema, with actual finite value bounds on both rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 DiamondIntegral.Section4.FiniteTupleBlocks

 theorem comp_join {α β : Type*} (f : α → β) (n : ℕ) :
    ∀ (m : ℕ) (x : Fin m → α) (y : Fin n → α),
      f ∘ join n m x y = join n m (f ∘ x) (f ∘ y) := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro x y
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (Fin.tail x) y) j

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}

theorem joined_equiv_graph_append_definable
    {D : Set (Fin a → M)} {E : Set (Fin b → M)} (e : D ≃ E)
    (hD : ∀ x ∈ D, ∀ i, iRV (x i)) (hE : ∀ y ∈ E, ∀ i, iRV (y i))
    (hg : DefinableOverBase B (fun _ : Fin (b+a) => .rv)
      {w | ∃ u : D, w = join b a u.val (e u).val}) :
    DefinableOverBase B (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv))
      {w | ∃ u : D, w = Fin.append u.val (e u).val} := by
  let π : Fin (b+a) → Fin (a+b) := join b a (Fin.castAdd b) (Fin.natAdd a)
  have hπ (x : Fin a → M) (y : Fin b → M) :
      Fin.append x y ∘ π = join b a x y := by
    rw [comp_join]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right]
  have h := hg.preimage_real (Fin.append (fun _ : Fin a => .rv) (fun _ : Fin b => .rv)) π
  convert h using 1
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨u, hπ _ _⟩, ?_⟩
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left, sortEval, iRV] using hD u.val u.property i
    · simpa only [Fin.append_right, sortEval, iRV] using hE (e u).val (e u).property i
  · rintro ⟨⟨u, hu⟩, _⟩
    refine ⟨u, ?_⟩
    have hx (i : Fin a) : w (Fin.castAdd b i) = u.val i := by
      have hh := congrFun hu (headIndex b a i)
      simpa only [Function.comp_apply, π, join_head] using hh
    have hy (i : Fin b) : w (Fin.natAdd a i) = (e u).val i := by
      have hh := congrFun hu (tailIndex b a i)
      simpa only [Function.comp_apply, π, join_tail] using hh
    funext j
    exact Fin.addCases (fun i => (hx i).trans (Fin.append_left _ _ i).symm)
      (fun i => (hy i).trans (Fin.append_right _ _ i).symm) j

theorem res_bijection_schema_at_parameter (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p k l : ℕ} (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (A : RVMeasuredCharts.RESChart ⟨B.real ∪ Set.range z, B.gamma⟩ k)
    (C : RVMeasuredCharts.RESChart ⟨B.real ∪ Set.range z, B.gamma⟩ l)
    (f : RVUnderlyingIsomorphisms.Iso A.toChart C.toChart) :
    ∃ (F : RESSetSchema B p A.arity sp) (G : RESSetSchema B p C.arity sp)
      (H : RESBijectionSchema F G), H.Valid hc z ∧
      F.rowDomain z = A.domain ∧ G.rowDomain z = C.domain ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ H.graph.val ↔
        ∃ u : A.domain, u.val = x ∧ (f.equiv u).val = y := by
  obtain ⟨F, hF, heF⟩ := res_set_schema_at_parameter hc B sp z hz A
  obtain ⟨G, hG, heG⟩ := res_set_schema_at_parameter hc B sp z hz C
  let es := Set.equivOfEq heF
  let et := Set.equivOfEq heG
  let e := es.trans (f.equiv.trans et.symm)
  let W : Set (Fin (A.arity+C.arity) → M) := {w | ∃ u : A.domain, w = Fin.append u.val (f.equiv u).val}
  have hW : DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩
      (Fin.append (fun _ : Fin A.arity => .rv) (fun _ : Fin C.arity => .rv)) W :=
    joined_equiv_graph_append_definable f.equiv
      (fun x hx i => A.domain_definable.proper x hx i)
      (fun y hy i => C.domain_definable.proper y hy i) f.graph_definable
  have he (x : Fin A.arity → M) (y : Fin C.arity → M) :
      Fin.append x y ∈ W ↔ ∃ u : F.rowDomain z, u.val = x ∧ (e u).val = y := by
    constructor
    · rintro ⟨u, hu⟩
      have hx := congrArg (fun w => w ∘ Fin.castAdd C.arity) hu
      have hy := congrArg (fun w => w ∘ Fin.natAdd A.arity) hu
      refine ⟨es.symm u, ?_, ?_⟩
      · change u.val = x
        simpa only [Function.comp_def, Fin.append_left] using hx.symm
      · change (et.symm (f.equiv (es (es.symm u)))).val = y
        rw [es.apply_symm_apply]
        change (f.equiv u).val = y
        simpa only [Function.comp_def, Fin.append_right] using hy.symm
    · rintro ⟨u, hu, hv⟩
      refine ⟨es u, ?_⟩
      change Fin.append x y = Fin.append u.val (f.equiv (es u)).val
      rw [← hu, ← hv]
      rfl
  obtain ⟨Q, hQ, hrow⟩ := gamma_sorted_tuple_relation_promotion B sp
    (fun _ : Fin A.arity => .rv) (fun _ : Fin C.arity => .rv) z hz W hW
  let H : RESBijectionSchema F G := ⟨⟨Q, hQ⟩⟩
  have hbij := bijectiveMapRowValid_of_equiv (sy := fun _ : Fin C.arity => .rv) (D := F.domain.val) (E := G.domain.val)
    z hz e (fun x y => (hrow x y).trans (he x y))
  refine ⟨F, G, H, ⟨hF, hG, hbij⟩, heF, heG, ?_⟩
  intro x y
  change Fin.append (Fin.append z x) y ∈ Q ↔ _
  rw [hrow x y]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_, ?_⟩
    · simpa only [Function.comp_def, Fin.append_left] using
        (congrArg (fun w => w ∘ Fin.castAdd C.arity) hu).symm
    · simpa only [Function.comp_def, Fin.append_right] using
        (congrArg (fun w => w ∘ Fin.natAdd A.arity) hu).symm
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, by rw [← hu, ← hv]⟩

end DiamondIntegral.Section5
