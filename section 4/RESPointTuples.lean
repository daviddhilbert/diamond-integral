import «section 4».RVUnderlyingIsomorphisms
import «section 4».RESOrdinaryRing
import «section 4».RVRadiusGenerators

/-! Concrete definable point objects in every grade, including grade
zero, and their underlying bijections and ordinary product classes. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESPointTuples
open RVMeasuredCharts RVRadiusGenerators FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def tuple (n : ℕ) : Fin n → M := fun _ => raw (oneCode (M := M))

theorem tuple_definable (B : Base (M := M)) (n : ℕ) :
    DefinableOverBase B (fun _ : Fin n => .rv) ({tuple n} : Set (Fin n → M)) :=
  tuple_singleton_definable_base B (fun _ => .rv) (tuple n) (fun _ => oneCode_definable B)

def chart (B : Base (M := M)) (n : ℕ) : Chart B n where
  arity := n
  domain := {tuple n}
  domain_definable := tuple_definable B n
  coordinate := id
  coordinate_definable := RVSharpCharts.identity_graph_definable B _ (tuple_definable B n)
  coordinate_proper := by
    rintro u (rfl : u = tuple n) i
    exact ⟨raw_rv oneCode, raw_ne_zero oneCode⟩
  finite_fibres := fun _ => (Set.finite_singleton (tuple n)).subset (fun _ h => h.1)
  volume := fun _ => 1
  volume_definable := constant_volume_definable B _ (tuple_definable B n) 1 (GammaGroupNames.one_definable_base B)

def res (B : Base (M := M)) (n : ℕ) : RESChart B n :=
  ⟨chart B n, (chart B n).finite_domain_values (Set.finite_singleton _)⟩

theorem join_tuple (n m : ℕ) : join n m (tuple (M := M) m) (tuple n) = tuple (n + m) :=
  FiniteTupleGraphProduct.block_ext n m (funext (join_head n m _ _)) (funext (join_tail n m _ _))

def underlyingIso (B : Base (M := M)) (m n : ℕ) : RVUnderlyingIsomorphisms.Iso (chart B m) (chart B n) where
  equiv := {
    toFun := fun _ => ⟨tuple n, rfl⟩
    invFun := fun _ => ⟨tuple m, rfl⟩
    left_inv := fun u => Subtype.ext u.property.symm
    right_inv := fun u => Subtype.ext u.property.symm }
  graph_definable := by
    have he : {w | ∃ u : (chart B m).domain, w = join n m u.val (tuple n)} = ({tuple (n + m)} : Set (Fin (n + m) → M)) := by
      ext w
      constructor
      · rintro ⟨u, rfl⟩
        have hu : u.val = tuple m := u.property
        rw [hu]
        exact join_tuple n m
      · intro hw
        exact ⟨⟨tuple m, rfl⟩, (show w = tuple (n + m) from hw).trans (join_tuple n m).symm⟩
    change DefinableOverBase B (fun _ : Fin (n + m) => .rv)
      {w | ∃ u : (chart B m).domain, w = join n m u.val (tuple n)}
    rw [he]
    exact tuple_definable B (n + m)

theorem product_domain (B : Base (M := M)) (m n : ℕ) :
    (RVMeasuredProduct.product (chart B m) (chart B n)).domain = (chart B (n + m)).domain := by
  ext z
  change (z ∘ headIndex n m = tuple m ∧ z ∘ tailIndex n m = tuple n) ↔ z = tuple (n + m)
  constructor
  · rintro ⟨hh, ht⟩
    exact FiniteTupleGraphProduct.block_ext n m hh ht
  · rintro rfl
    exact ⟨rfl, rfl⟩

def productIso (B : Base (M := M)) (m n : ℕ) : RVForgetScissors.UnderlyingIso
    (RVMeasuredProduct.product (chart B m) (chart B n)) (chart B (n + m)) := by
  let a := RVMeasuredProduct.product (chart B m) (chart B n)
  have he := product_domain B m n
  exact RVUnderlyingIsomorphisms.toFixed (RVUnderlyingIsomorphisms.ofMap a (chart B (n + m)) id
    (RVSharpCharts.identity_graph_definable B a.domain a.domain_definable)
    ⟨(fun u hu => he ▸ hu), (fun _ _ _ _ h => h), (fun u hu => ⟨u, he.symm ▸ hu, rfl⟩)⟩)

theorem ordinary_product (B : Base (M := M)) (m n : ℕ) :
    RESOrdinaryRing.objectClass (res B (n + m)) = RESOrdinaryRing.objectClass (res B m) * RESOrdinaryRing.objectClass (res B n) :=
  (RESOrdinaryRing.objectClass_iso (productIso B m n)).symm.trans
    (RESOrdinaryRing.objectClass_product (res B m) (res B n))

def unitIso (B : Base (M := M)) : RVForgetScissors.UnderlyingIso (chart B 0) (RESChartRing.unit B).toChart := by
  have he : (chart B 0).domain = (RESChartRing.unit B).domain := by
    ext u
    change u = tuple 0 ↔ True
    exact ⟨fun _ => trivial, fun _ => @Subsingleton.elim (Fin 0 → M) inferInstance _ _⟩
  exact RVUnderlyingIsomorphisms.toFixed (RVUnderlyingIsomorphisms.ofMap (chart B 0) (RESChartRing.unit B).toChart id
    (RVSharpCharts.identity_graph_definable B _ (tuple_definable B 0))
    ⟨(fun u hu => he ▸ hu), (fun _ _ _ _ h => h), (fun u hu => ⟨u, he.symm ▸ hu, rfl⟩)⟩)

theorem ordinary_zero (B : Base (M := M)) : RESOrdinaryRing.objectClass (res B 0) = 1 :=
  (RESOrdinaryRing.objectClass_iso (unitIso B)).trans (RESOrdinaryRing.objectClass_unit B)

theorem ordinary_power (B : Base (M := M)) (n : ℕ) :
    RESOrdinaryRing.objectClass (res B n) = RESOrdinaryRing.objectClass (res B 1) ^ n := by
  induction n with
  | zero => exact (ordinary_zero B).trans (pow_zero _).symm
  | succ n ih =>
    rw [show RESOrdinaryRing.objectClass (res B (n + 1)) =
      RESOrdinaryRing.objectClass (res B 1) * RESOrdinaryRing.objectClass (res B n) from ordinary_product B 1 n,
      ih, pow_succ']

end DiamondIntegral.Section4.RESPointTuples
