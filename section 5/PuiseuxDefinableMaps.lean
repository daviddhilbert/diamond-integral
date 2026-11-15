import «section 5».FiniteFrameComparison
import «section 3».DefinableBijections

/-! Original-base definable maps commute with the proved full Puiseux
actions. This applies to their complete graphs, including VF quantifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section3
local instance mapActionStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

def sortedRVAction (η : CompatibleRoots ℂ) (r : CanonicalRV.RVSort Carrier) :
    CanonicalRV.RVSort Carrier := rvTag (rvAction η (taggedRVEquiv r))

theorem sortedRVAction_raw (η : CompatibleRoots ℂ) (r : CanonicalRV.RVSort Carrier) :
    (sortedRVAction η r).val = carrierAction η r.val := by
  have h := congrArg (carrierAction η) (rvSort_tag r)
  exact h

theorem raw_original_definable_invariant (η : CompatibleRoots ℂ) {β : Type}
    (D : Set (β → Carrier)) (hD : {c | baseCarrier c}.Definable LRV D) (z : β → Carrier) :
    (carrierAction η ∘ z) ∈ D ↔ z ∈ D := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hD
  rw [hφ]
  change φ.Realize (Sum.elim Subtype.val (carrierAction η ∘ z)) ↔
    φ.Realize (Sum.elim Subtype.val z)
  have h := StrongHomClass.realize_formula (canonicalLanguageAction η) φ
    (v := Sum.elim Subtype.val z)
  have he : (canonicalLanguageAction η) ∘
      (Sum.elim (Subtype.val : {c // baseCarrier c} → Carrier) z) =
      Sum.elim (Subtype.val : {c // baseCarrier c} → Carrier) (carrierAction η ∘ z) := by
    funext j
    cases j with
    | inl c => exact carrierAction_fixes_base η c.val c.property
    | inr i => rfl
  exact (Iff.of_eq (congrArg (fun v => φ.Realize v) he)).symm.trans h

theorem original_RV_map_equivariant {n m : ℕ}
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (f : Map A B) (η : CompatibleRoots ℂ) (u : A) :
    ∃ v : A, v.val = (fun i => sortedRVAction η (u.val i)) ∧
      (f v).val = (fun i => sortedRVAction η ((f u).val i)) := by
  let P := rawRVSpace (M := Carrier) n
  let Q := rawRVSpace (M := Carrier) m
  let G := P.relation Q f.graph
  have hg : {c | baseCarrier c}.Definable LRV G := f.graph_definable
  have hrow (a : Fin n → CanonicalRV.RVSort Carrier) (b : Fin m → CanonicalRV.RVSort Carrier) :
      Sum.elim (rvValues a) (rvValues b) ∈ G ↔ f.graph a b := by
    have h := Space.relation_decode P Q f.graph
      ⟨rvValues a, ⟨a, rfl⟩⟩ ⟨rvValues b, ⟨b, rfl⟩⟩
    rw [decode_rvValues, decode_rvValues] at h
    exact h
  have hz : Sum.elim (rvValues u.val) (rvValues (f u).val) ∈ G :=
    (hrow _ _).mpr ⟨u, rfl, rfl⟩
  have h := (raw_original_definable_invariant η G hg _).mpr hz
  have he : carrierAction η ∘ Sum.elim (rvValues u.val) (rvValues (f u).val) =
      Sum.elim (rvValues (fun i => sortedRVAction η (u.val i)))
        (rvValues (fun i => sortedRVAction η ((f u).val i))) := by
    funext j
    cases j <;> exact (sortedRVAction_raw η _).symm
  rw [he] at h
  exact (hrow _ _).mp h

def frameSetEquiv {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : HasFrameSupport N a A) : A ≃ framedRVSet N a A where
  toFun r := ⟨fun i => lineCoefficient (taggedRVEquiv (r.val i)), by
    change (fun i => rvTag (finiteFrame N a (fun j => lineCoefficient (taggedRVEquiv (r.val j))) i)) ∈ A.carrier
    rw [frame_reconstruction N a A hA r]
    exact r.property⟩
  invFun x := ⟨fun i => rvTag (finiteFrame N a x.val i), x.property⟩
  left_inv r := Subtype.ext (frame_reconstruction N a A hA r)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact lineCoefficient_point ((a i : ℚ) / (N : ℕ)) (x.val i)

theorem sortedRVAction_frame {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (η : CompatibleRoots ℂ) (x : Fin n → ℂ) :
    (fun i => sortedRVAction η (rvTag (finiteFrame N a x i))) =
      fun i => rvTag (finiteFrame N a (weightedAction a (η.val N) x) i) := by
  funext i
  exact congrArg rvTag (congrFun (finiteFrame_action N a η x) i)

theorem frameSetEquiv_action {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (hA : HasFrameSupport N a A) (η : CompatibleRoots ℂ) (u v : A)
    (hv : v.val = fun i => sortedRVAction η (u.val i)) :
    (frameSetEquiv N a A hA v).val = weightedAction a (η.val N) (frameSetEquiv N a A hA u).val := by
  apply finiteFrame_injective N a
  have he : (fun i => rvTag (finiteFrame N a (frameSetEquiv N a A hA v).val i)) =
      fun i => rvTag (finiteFrame N a (weightedAction a (η.val N) (frameSetEquiv N a A hA u).val) i) := by
    calc
      _ = v.val := frame_reconstruction N a A hA v
      _ = (fun i => sortedRVAction η (u.val i)) := hv
      _ = (fun i => sortedRVAction η (rvTag (finiteFrame N a (frameSetEquiv N a A hA u).val i))) :=
        congrArg (fun t => fun i => sortedRVAction η (t i)) (frame_reconstruction N a A hA u).symm
      _ = _ := sortedRVAction_frame N a η _
  exact funext (fun i => congrArg taggedRVEquiv (congrFun he i))

end DiamondIntegral.Section5.PuiseuxOriginal
