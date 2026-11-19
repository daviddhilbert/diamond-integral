import «section 4».RVTaggedPartitionIsomorphisms
import «section 4».RVCoordinateMaps
import «section 4».RVBoundedRing
import «section 4».RVTaggedCoproductClasses

/-! Isomorphism classes of doubly bounded measured RV objects (the paper's
`μRV^db[k]`, Definition 4.9, in the Section 4 chart presentation).

An object is a bounded Section 4 chart over a parameter base `B`; a morphism is
an actual measured isomorphism (a definable bijection preserving the total
weight, condition (cond:mg2)). This module provides:

* measured isomorphisms from maps with definable graphs (`isoOfMap`), the
  identity between pieces with the same domain and data (`sameIso`), the
  restriction of an isomorphism to a definable piece of its source
  (`restrictIso`), and gluing along definable two-piece partitions (`glue`);
* the tagged disjoint union: functoriality, commutativity, associativity and
  the empty object as unit, as actual isomorphisms;
* the commutative monoid `Cls B k` of isomorphism classes. Equality of
  classes is, by construction, existence of an isomorphism; no cancellation is
  used.

As in Section 4, the coproduct uses the RV element `∞` as a tag, which the
bounded condition `DomainBounded` does not constrain. Section 4 shows that this
presentation and the paper's `∞`-free one give isomorphic rings
(`RVStrictBoundedComparison`). -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section4
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions RVTaggedCoproduct FiniteTupleBlocks
open RVRealProducts

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-! ### Measured isomorphisms from maps, restriction and gluing -/

/-- A measured isomorphism from a map with a definable graph that is a
bijection of the domains and preserves the total weight. -/
def isoOfMap (a b : Chart B k) (F : (Fin a.arity → M) → (Fin b.arity → M))
    (hF : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (graphOn a.domain F))
    (hbij : Set.BijOn F a.domain b.domain)
    (hw : ∀ u ∈ a.domain, a.correctedWeight u = b.correctedWeight (F u)) : Iso a b :=
  let H := RVUnderlyingIsomorphisms.ofMap a b F hF hbij
  ⟨H.equiv, H.graph_definable, fun u => hw u.val u.property⟩

theorem isoOfMap_apply (a b : Chart B k) (F : (Fin a.arity → M) → (Fin b.arity → M))
    (hF : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (graphOn a.domain F))
    (hbij : Set.BijOn F a.domain b.domain)
    (hw : ∀ u ∈ a.domain, a.correctedWeight u = b.correctedWeight (F u)) (u : a.domain) :
    ((isoOfMap a b F hF hbij hw).equiv u).val = F u.val := rfl

/-- The identity between two pieces of the same arity with the same domain and
the same coordinates and volume on it. -/
def sameIso {n : ℕ} (a b : Data B n k) (hdom : a.domain = b.domain)
    (hcoord : ∀ u ∈ a.domain, a.coordinate u = b.coordinate u)
    (hvol : ∀ u ∈ a.domain, a.volume u = b.volume u) : Iso a.toChart b.toChart :=
  isoOfMap a.toChart b.toChart id
    (RVSharpCharts.identity_graph_definable B a.domain a.domain_definable)
    (by
      change Set.BijOn id a.domain b.domain
      rw [← hdom]
      exact Set.bijOn_id _)
    (fun u hu => by
      change a.volume u * ∏ i, codeValue (a.coordinate u i) =
        b.volume u * ∏ i, codeValue (b.coordinate u i)
      rw [hvol u hu, hcoord u hu])

/-- The extension of the underlying map of a measured isomorphism. -/
def isoMap {a b : Chart B k} (F : Iso a b) : (Fin a.arity → M) → (Fin b.arity → M) :=
  (RVMeasuredIsomorphisms.underlying F).extension

theorem isoMap_on {a b : Chart B k} (F : Iso a b) (u : a.domain) : isoMap F u.val = (F.equiv u).val :=
  (RVMeasuredIsomorphisms.underlying F).extension_on u

theorem isoMap_graph {a b : Chart B k} (F : Iso a b) :
    DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (graphOn a.domain (isoMap F)) :=
  (RVMeasuredIsomorphisms.underlying F).extension_graph

theorem isoMap_bijOn {a b : Chart B k} (F : Iso a b) : Set.BijOn (isoMap F) a.domain b.domain :=
  RVUnderlyingIsomorphisms.Iso.extension_bijOn (RVMeasuredIsomorphisms.underlying F)

theorem isoMap_weight {a b : Chart B k} (F : Iso a b) (u : Fin a.arity → M) (hu : u ∈ a.domain) :
    a.correctedWeight u = b.correctedWeight (isoMap F u) := by
  rw [isoMap_on F ⟨u, hu⟩]
  exact F.weight_eq ⟨u, hu⟩

omit [LRV.Structure M] hM in
theorem graphOn_inter {m n : ℕ} (I J : Set (Fin m → M)) (F : (Fin m → M) → (Fin n → M)) :
    graphOn (I ∩ J) F = graphOn I F ∩ {w | w ∘ headIndex n m ∈ J} := by
  ext w
  exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩

theorem graph_inter_definable {m n : ℕ} (I J : Set (Fin m → M)) (F : (Fin m → M) → (Fin n → M))
    (hG : DefinableOverBase B (fun _ : Fin (n + m) => .rv) (graphOn I F))
    (hJ : DefinableOverBase B (fun _ : Fin m => .rv) J) :
    DefinableOverBase B (fun _ : Fin (n + m) => .rv) (graphOn (I ∩ J) F) := by
  have h := hG.inter (hJ.preimage_real (fun _ : Fin (n + m) => .rv) (headIndex n m))
  convert h using 1
  ext w
  constructor
  · intro hw
    exact ⟨⟨hw.1.1, hw.2⟩, hw.1.2, hG.proper w ⟨hw.1.1, hw.2⟩⟩
  · intro hw
    exact ⟨⟨hw.1.1, hw.2.1⟩, hw.1.2⟩

theorem graph_image_definable {m n : ℕ} (I : Set (Fin m → M)) (F : (Fin m → M) → (Fin n → M))
    (hG : DefinableOverBase B (fun _ : Fin (n + m) => .rv) (graphOn I F)) :
    DefinableOverBase B (fun _ : Fin n => .rv) (F '' I) := by
  have h := hG.image_real (tailIndex n m)
  have he : F '' I = (fun w => w ∘ tailIndex n m) '' graphOn I F := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hh : join n m x (F x) ∘ headIndex n m = x := funext (join_head n m x (F x))
      have ht : join n m x (F x) ∘ tailIndex n m = F x := funext (join_tail n m x (F x))
      exact ⟨join n m x (F x), ⟨by rw [hh]; exact hx, by rw [hh, ht]⟩, ht⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w ∘ headIndex n m, hw.1, hw.2⟩
  rw [he]
  exact h

/-- The image of a definable piece under a measured isomorphism. -/
def image {a b : Chart B k} (F : Iso a b) (I : Set (Fin a.arity → M)) : Set (Fin b.arity → M) :=
  isoMap F '' (a.domain ∩ I)

theorem image_definable {a b : Chart B k} (F : Iso a b) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) :
    DefinableOverBase B (fun _ : Fin b.arity => .rv) (image F I) :=
  graph_image_definable _ _ (graph_inter_definable _ _ _ (isoMap_graph F) hI)

theorem image_subset {a b : Chart B k} (F : Iso a b) (I : Set (Fin a.arity → M)) :
    image F I ⊆ b.domain := by
  rintro y ⟨x, hx, rfl⟩
  exact (isoMap_bijOn F).1 hx.1

/-- The restriction of a measured isomorphism to a definable piece of its
source, onto the image piece. -/
def restrictIso {a b : Chart B k} (F : Iso a b) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) :
    Iso (inside (ofChart a) I hI).toChart (inside (ofChart b) (image F I) (image_definable F I hI)).toChart :=
  isoOfMap _ _ (isoMap (a := a) (b := b) F) (graph_inter_definable _ _ _ (isoMap_graph F) hI)
    (by
      refine ⟨fun u hu => ⟨(isoMap_bijOn F).1 hu.1, u, hu, rfl⟩, ?_, ?_⟩
      · exact (isoMap_bijOn F).2.1.mono (fun u hu => hu.1)
      · rintro y ⟨_, x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩)
    (fun u hu => isoMap_weight F u hu.1)

/-- Gluing measured isomorphisms along definable two-piece partitions. -/
def glue {n m : ℕ} (X : Data B n k) (Y : Data B m k)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I)
    (J : Set (Fin m → M)) (hJ : DefinableOverBase B (fun _ : Fin m => .rv) J)
    (F : Iso (inside X I hI).toChart (inside Y J hJ).toChart)
    (G : Iso (outside X I hI).toChart (outside Y J hJ).toChart) : Iso X.toChart Y.toChart :=
  RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm (partitionIso X I hI))
    (RVMeasuredIsomorphisms.trans
      (RVDisjointUnionIsomorphisms.unionIso _ _ _ _ (pieces_disjoint X I hI) (pieces_disjoint Y J hJ) G F)
      (partitionIso Y J hJ))

/-! ### Pieces of a disjoint union -/

section Pieces
variable {n : ℕ} (c d : Data B n k) (hcd : Disjoint c.domain d.domain)

theorem union_inter_left : (c.domain ∪ d.domain) ∩ c.domain = c.domain :=
  Set.union_inter_cancel_left

theorem union_diff_left (hcd : Disjoint c.domain d.domain) : (c.domain ∪ d.domain) \ c.domain = d.domain := by
  rw [Set.union_sdiff_left]
  exact Disjoint.sdiff_eq_left hcd.symm

theorem union_inter_right : (c.domain ∪ d.domain) ∩ d.domain = d.domain :=
  Set.union_inter_cancel_right

theorem union_diff_right (hcd : Disjoint c.domain d.domain) : (c.domain ∪ d.domain) \ d.domain = c.domain := by
  rw [Set.union_sdiff_right]
  exact Disjoint.sdiff_eq_left hcd

/-- The left piece of a disjoint union is the left summand. -/
def insideLeft :
    Iso (inside (disjointUnion c d hcd) c.domain c.domain_definable).toChart c.toChart :=
  sameIso _ _ (union_inter_left c d)
    (fun u hu => by
      change piecewise c.domain c.coordinate d.coordinate u = c.coordinate u
      simp only [piecewise, ite_eq_left hu.2])
    (fun u hu => by
      change piecewise c.domain c.volume d.volume u = c.volume u
      simp only [piecewise, ite_eq_left hu.2])

/-- The complement of the left piece is the right summand. -/
def outsideLeft :
    Iso (outside (disjointUnion c d hcd) c.domain c.domain_definable).toChart d.toChart :=
  sameIso _ _ (union_diff_left c d hcd)
    (fun u hu => by
      change piecewise c.domain c.coordinate d.coordinate u = d.coordinate u
      simp only [piecewise, ite_eq_right hu.2])
    (fun u hu => by
      change piecewise c.domain c.volume d.volume u = d.volume u
      simp only [piecewise, ite_eq_right hu.2])

/-- The right piece of a disjoint union is the right summand. -/
def insideRight :
    Iso (inside (disjointUnion c d hcd) d.domain d.domain_definable).toChart d.toChart :=
  sameIso _ _ (union_inter_right c d)
    (fun u hu => by
      have hc : u ∉ c.domain := fun h => Set.disjoint_left.mp hcd h hu.2
      change piecewise c.domain c.coordinate d.coordinate u = d.coordinate u
      simp only [piecewise, ite_eq_right hc])
    (fun u hu => by
      have hc : u ∉ c.domain := fun h => Set.disjoint_left.mp hcd h hu.2
      change piecewise c.domain c.volume d.volume u = d.volume u
      simp only [piecewise, ite_eq_right hc])

/-- The complement of the right piece is the left summand. -/
def outsideRight :
    Iso (outside (disjointUnion c d hcd) d.domain d.domain_definable).toChart c.toChart :=
  sameIso _ _ (union_diff_right c d hcd)
    (fun u hu => by
      have hc : u ∈ c.domain := (union_diff_right c d hcd ▸ hu : u ∈ c.domain)
      change piecewise c.domain c.coordinate d.coordinate u = c.coordinate u
      simp only [piecewise, ite_eq_left hc])
    (fun u hu => by
      have hc : u ∈ c.domain := (union_diff_right c d hcd ▸ hu : u ∈ c.domain)
      change piecewise c.domain c.volume d.volume u = c.volume u
      simp only [piecewise, ite_eq_left hc])

end Pieces

/-! ### The tagged coproduct -/

/-- The left summand of a tagged coproduct, as data on the coproduct arity. -/
abbrev L (a b : Chart B k) := leftData a b
/-- The right summand of a tagged coproduct. -/
abbrev R (a b : Chart B k) := rightData a b

theorem coproduct_eq (a b : Chart B k) :
    coproduct a b = (disjointUnion (L a b) (R a b) (tagged_disjoint a b)).toChart := rfl

/-- The coproduct is functorial in actual measured isomorphisms. -/
def coprodCongr {a b c d : Chart B k} (F : Iso a c) (G : Iso b d) :
    Iso (coproduct a b) (coproduct c d) :=
  RVDisjointUnionIsomorphisms.unionIso (L a b) (R a b) (L c d) (R c d)
    (tagged_disjoint a b) (tagged_disjoint c d)
    (RVMeasuredIsomorphisms.trans (RVTaggedComponentIsomorphisms.leftIso a b)
      (RVMeasuredIsomorphisms.trans F (RVMeasuredIsomorphisms.symm (RVTaggedComponentIsomorphisms.leftIso c d))))
    (RVMeasuredIsomorphisms.trans (RVTaggedComponentIsomorphisms.rightIso a b)
      (RVMeasuredIsomorphisms.trans G (RVMeasuredIsomorphisms.symm (RVTaggedComponentIsomorphisms.rightIso c d))))

/-- The left piece of the coproduct `a ⊎ b` is `a`. -/
def coprodInsideLeft (a b : Chart B k) :
    Iso (inside (disjointUnion (L a b) (R a b) (tagged_disjoint a b)) (L a b).domain
      (L a b).domain_definable).toChart a :=
  RVMeasuredIsomorphisms.trans (insideLeft _ _ _) (RVTaggedComponentIsomorphisms.leftIso a b)

/-- The complement of the left piece of `a ⊎ b` is `b`. -/
def coprodOutsideLeft (a b : Chart B k) :
    Iso (outside (disjointUnion (L a b) (R a b) (tagged_disjoint a b)) (L a b).domain
      (L a b).domain_definable).toChart b :=
  RVMeasuredIsomorphisms.trans (outsideLeft _ _ _) (RVTaggedComponentIsomorphisms.rightIso a b)

/-- The right piece of `a ⊎ b` is `b`. -/
def coprodInsideRight (a b : Chart B k) :
    Iso (inside (disjointUnion (L a b) (R a b) (tagged_disjoint a b)) (R a b).domain
      (R a b).domain_definable).toChart b :=
  RVMeasuredIsomorphisms.trans (insideRight _ _ _) (RVTaggedComponentIsomorphisms.rightIso a b)

/-- The complement of the right piece of `a ⊎ b` is `a`. -/
def coprodOutsideRight (a b : Chart B k) :
    Iso (outside (disjointUnion (L a b) (R a b) (tagged_disjoint a b)) (R a b).domain
      (R a b).domain_definable).toChart a :=
  RVMeasuredIsomorphisms.trans (outsideRight _ _ _) (RVTaggedComponentIsomorphisms.leftIso a b)

/-- Commutativity of the coproduct. -/
def coprodComm (a b : Chart B k) : Iso (coproduct a b) (coproduct b a) :=
  glue (disjointUnion (L a b) (R a b) (tagged_disjoint a b))
    (disjointUnion (L b a) (R b a) (tagged_disjoint b a))
    (L a b).domain (L a b).domain_definable (R b a).domain (R b a).domain_definable
    (RVMeasuredIsomorphisms.trans (coprodInsideLeft a b) (RVMeasuredIsomorphisms.symm (coprodInsideRight b a)))
    (RVMeasuredIsomorphisms.trans (coprodOutsideLeft a b) (RVMeasuredIsomorphisms.symm (coprodOutsideRight b a)))

/-! ### Associativity and the empty object -/

omit [LRV.Structure M] hM in
/-- Bijective images of complementary pieces are complementary. -/
theorem image_compl_piece {n m : ℕ} {f : (Fin n → M) → (Fin m → M)} {A P Q : Set (Fin n → M)}
    {C : Set (Fin m → M)} (hf : Set.BijOn f A C) (hA : A = P ∪ Q) (hPQ : Disjoint P Q) :
    C \ f '' (A ∩ Q) = f '' (A ∩ P) := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨hy, hnot⟩
    obtain ⟨x, hx, rfl⟩ := hf.2.2 hy
    have hx' : x ∈ P ∪ Q := hA ▸ hx
    rcases hx' with hp | hq
    · exact ⟨x, ⟨hx, hp⟩, rfl⟩
    · exact absurd ⟨x, ⟨hx, hq⟩, rfl⟩ hnot
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    refine ⟨hf.1 hx, ?_⟩
    rintro ⟨x', ⟨hx', hq⟩, he⟩
    have hxx := hf.2.1 hx' hx he
    subst hxx
    exact Set.disjoint_left.mp hPQ hp hq

section Assoc
variable (a b c : Chart B k)

/-- The right summand of `a ⊎ (b ⊎ c)` is `b ⊎ c`. -/
abbrev bcIso : Iso (coproduct b c) (R a (coproduct b c)).toChart :=
  RVMeasuredIsomorphisms.symm (RVTaggedComponentIsomorphisms.rightIso a (coproduct b c))

/-- The piece of `a ⊎ (b ⊎ c)` corresponding to `c`. -/
def cPart : Set (Fin (R a (coproduct b c)).toChart.arity → M) := image (bcIso a b c) (R b c).domain

/-- The piece of `a ⊎ (b ⊎ c)` corresponding to `b`. -/
def bPart : Set (Fin (R a (coproduct b c)).toChart.arity → M) := image (bcIso a b c) (L b c).domain

theorem cPart_definable : DefinableOverBase B (fun _ => .rv) (cPart a b c) :=
  image_definable _ _ (R b c).domain_definable

theorem bPart_definable : DefinableOverBase B (fun _ => .rv) (bPart a b c) :=
  image_definable _ _ (L b c).domain_definable

theorem cPart_sub : cPart a b c ⊆ (R a (coproduct b c)).domain := image_subset _ _

theorem bPart_sub : bPart a b c ⊆ (R a (coproduct b c)).domain := image_subset _ _

theorem right_diff_cPart : (R a (coproduct b c)).domain \ cPart a b c = bPart a b c :=
  image_compl_piece (isoMap_bijOn (bcIso a b c)) rfl (tagged_disjoint b c)

theorem not_left_of_right {u : Fin (R a (coproduct b c)).toChart.arity → M}
    (hu : u ∈ (R a (coproduct b c)).domain) : u ∉ (L a (coproduct b c)).domain :=
  fun h => Set.disjoint_left.mp (tagged_disjoint a (coproduct b c)) h hu

/-- The piece of `a ⊎ (b ⊎ c)` over `c` is `c`. -/
def assocInsideY :
    Iso (inside (disjointUnion (L a (coproduct b c)) (R a (coproduct b c)) (tagged_disjoint a (coproduct b c)))
      (cPart a b c) (cPart_definable a b c)).toChart c :=
  RVMeasuredIsomorphisms.trans
    (sameIso _ (inside (R a (coproduct b c)) (cPart a b c) (cPart_definable a b c))
      (by
        apply Set.ext
        intro u
        constructor
        · rintro ⟨_, hu⟩
          exact ⟨cPart_sub a b c hu, hu⟩
        · rintro ⟨hr, hu⟩
          exact ⟨Or.inr hr, hu⟩)
      (fun u hu => by
        have h := not_left_of_right a b c (cPart_sub a b c hu.2)
        change piecewise _ _ _ u = _
        simp only [piecewise]
        split_ifs with h'
        · exact absurd h' h
        · rfl)
      (fun u hu => by
        have h := not_left_of_right a b c (cPart_sub a b c hu.2)
        change piecewise _ _ _ u = _
        simp only [piecewise]
        split_ifs with h'
        · exact absurd h' h
        · rfl))
    (RVMeasuredIsomorphisms.trans
      (RVMeasuredIsomorphisms.symm (restrictIso (bcIso a b c) (R b c).domain (R b c).domain_definable))
      (coprodInsideRight b c))

/-- The complement of the piece over `c` in `a ⊎ (b ⊎ c)` is `a ⊎ b`. -/
def assocOutsideY :
    Iso (outside (disjointUnion (L a (coproduct b c)) (R a (coproduct b c)) (tagged_disjoint a (coproduct b c)))
      (cPart a b c) (cPart_definable a b c)).toChart (coproduct a b) :=
  glue _ (disjointUnion (L a b) (R a b) (tagged_disjoint a b))
    (L a (coproduct b c)).domain (L a (coproduct b c)).domain_definable (L a b).domain (L a b).domain_definable
    (RVMeasuredIsomorphisms.trans
      (sameIso _ (L a (coproduct b c))
        (by
          apply Set.ext
          intro u
          constructor
          · rintro ⟨_, hu⟩
            exact hu
          · intro hu
            refine ⟨⟨Or.inl hu, fun hc => not_left_of_right a b c (cPart_sub a b c hc) hu⟩, hu⟩)
        (fun u hu => by
          change piecewise _ _ _ u = _
          simp only [piecewise, ite_eq_left hu.2])
        (fun u hu => by
          change piecewise _ _ _ u = _
          simp only [piecewise, ite_eq_left hu.2]))
      (RVMeasuredIsomorphisms.trans (RVTaggedComponentIsomorphisms.leftIso a (coproduct b c))
        (RVMeasuredIsomorphisms.symm (coprodInsideLeft a b))))
    (RVMeasuredIsomorphisms.trans
      (sameIso _ (inside (R a (coproduct b c)) (bPart a b c) (bPart_definable a b c))
        (by
          apply Set.ext
          intro u
          constructor
          · rintro ⟨⟨hu, hc⟩, hl⟩
            have hr : u ∈ (R a (coproduct b c)).domain := hu.resolve_left hl
            have hb : u ∈ bPart a b c := by
              rw [← right_diff_cPart]
              exact ⟨hr, hc⟩
            exact ⟨hr, hb⟩
          · rintro ⟨hr, hb⟩
            rw [← right_diff_cPart] at hb
            exact ⟨⟨Or.inr hr, hb.2⟩, not_left_of_right a b c hr⟩)
        (fun u hu => by
          change piecewise _ _ _ u = _
          simp only [piecewise]
          split_ifs with h'
          · exact absurd h' hu.2
          · rfl)
        (fun u hu => by
          change piecewise _ _ _ u = _
          simp only [piecewise]
          split_ifs with h'
          · exact absurd h' hu.2
          · rfl))
      (RVMeasuredIsomorphisms.trans
        (RVMeasuredIsomorphisms.symm (restrictIso (bcIso a b c) (L b c).domain (L b c).domain_definable))
        (RVMeasuredIsomorphisms.trans (coprodInsideLeft b c)
          (RVMeasuredIsomorphisms.symm (coprodOutsideLeft a b)))))

/-- Associativity of the coproduct. -/
def coprodAssoc : Iso (coproduct (coproduct a b) c) (coproduct a (coproduct b c)) :=
  glue (disjointUnion (L (coproduct a b) c) (R (coproduct a b) c) (tagged_disjoint (coproduct a b) c))
    (disjointUnion (L a (coproduct b c)) (R a (coproduct b c)) (tagged_disjoint a (coproduct b c)))
    (R (coproduct a b) c).domain (R (coproduct a b) c).domain_definable (cPart a b c) (cPart_definable a b c)
    (RVMeasuredIsomorphisms.trans (coprodInsideRight (coproduct a b) c)
      (RVMeasuredIsomorphisms.symm (assocInsideY a b c)))
    (RVMeasuredIsomorphisms.trans (coprodOutsideRight (coproduct a b) c)
      (RVMeasuredIsomorphisms.symm (assocOutsideY a b c)))

end Assoc

/-- An outside piece over a set missing the domain is the whole object. -/
def outsideMissing {n : ℕ} (X : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hmiss : X.domain ∩ I = ∅) :
    Iso (outside X I hI).toChart X.toChart :=
  sameIso _ _
    (by
      apply Set.ext
      intro u
      constructor
      · exact fun hu => hu.1
      · intro hu
        refine ⟨hu, fun hi => ?_⟩
        have : u ∈ X.domain ∩ I := ⟨hu, hi⟩
        rw [hmiss] at this
        exact this)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- An empty object is a unit for the coproduct. -/
def coprodEmpty (e a : Chart B k) (he : e.domain = ∅) : Iso (coproduct e a) a := by
  have hL : (L e a).domain = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact (Set.eq_empty_iff_forall_notMem.mp he) _
      ((RVTaggedComponentIsomorphisms.leftIso e a).equiv ⟨u, hu⟩).property
  exact RVMeasuredIsomorphisms.trans
    (RVMeasuredIsomorphisms.symm (outsideMissing (disjointUnion (L e a) (R e a) (tagged_disjoint e a))
      (L e a).domain (L e a).domain_definable (by rw [hL, Set.inter_empty])))
    (coprodOutsideLeft e a)

/-! ### Bounded objects, pieces and the monoid of isomorphism classes -/

/-- Objects of `μRV^db[k]`: bounded Section 4 charts. -/
abbrev Obj (B : Base (M := M)) (k : ℕ) := RVBoundedCharts.BoundedChart B k

/-- The empty object. -/
def emptyObj (B : Base (M := M)) (k : ℕ) : Obj B k :=
  ⟨(RVChartDisjointUnion.empty B 0 k).toChart, ⟨1, fun _ hu => hu.elim⟩⟩

/-- The tagged disjoint union of bounded objects. -/
abbrev coprod (a b : Obj B k) : Obj B k := RVTaggedCoproductProperties.boundedCoproduct a b

/-- A definable piece of a bounded object. -/
def piece (a : Obj B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) : Obj B k :=
  ⟨(inside (ofChart a.toChart) I hI).toChart,
    restrict_domain_bounded _ _ _ _ a.domain_bounded⟩

/-- The complementary piece. -/
def cpiece (a : Obj B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) : Obj B k :=
  ⟨(outside (ofChart a.toChart) I hI).toChart,
    restrict_domain_bounded _ _ _ _ a.domain_bounded⟩

variable (B k) in
/-- Isomorphism of bounded objects. -/
def isoSetoid : Setoid (Obj B k) where
  r a b := Nonempty (Iso a.toChart b.toChart)
  iseqv := ⟨fun a => ⟨RVMeasuredIsomorphisms.refl a.toChart⟩,
    fun ⟨F⟩ => ⟨RVMeasuredIsomorphisms.symm F⟩,
    fun ⟨F⟩ ⟨G⟩ => ⟨RVMeasuredIsomorphisms.trans F G⟩⟩

variable (B k) in
/-- Isomorphism classes of `μRV^db[k]`. -/
def Cls := Quotient (isoSetoid B k)

/-- The class of an object. -/
def cls (a : Obj B k) : Cls B k := Quotient.mk (isoSetoid B k) a

theorem cls_eq_iff {a b : Obj B k} : cls a = cls b ↔ Nonempty (Iso a.toChart b.toChart) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem cls_eq_of_iso {a b : Obj B k} (F : Iso a.toChart b.toChart) : cls a = cls b :=
  cls_eq_iff.mpr ⟨F⟩

instance : Zero (Cls B k) := ⟨cls (emptyObj B k)⟩

instance : Add (Cls B k) :=
  ⟨Quotient.map₂ coprod (fun _ _ hF _ _ hG => by
    obtain ⟨F⟩ := hF
    obtain ⟨G⟩ := hG
    exact ⟨coprodCongr F G⟩)⟩

theorem cls_coprod (a b : Obj B k) : cls (coprod a b) = cls a + cls b := rfl

theorem cls_zero : cls (emptyObj B k) = 0 := rfl

theorem cls_empty (a : Obj B k) (ha : a.domain = ∅) : cls a = 0 := by
  rw [← cls_zero]
  apply cls_eq_of_iso
  refine RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm (coprodEmpty (emptyObj B k).toChart a.toChart rfl)) ?_
  refine RVMeasuredIsomorphisms.trans (coprodComm _ _) ?_
  exact coprodEmpty a.toChart (emptyObj B k).toChart ha

instance : AddCommMonoid (Cls B k) where
  add_assoc x y z := Quotient.inductionOn₃ x y z fun a b c =>
    cls_eq_of_iso (coprodAssoc a.toChart b.toChart c.toChart)
  zero_add x := Quotient.inductionOn x fun a =>
    cls_eq_of_iso (coprodEmpty (emptyObj B k).toChart a.toChart rfl)
  add_zero x := Quotient.inductionOn x fun a =>
    cls_eq_of_iso (RVMeasuredIsomorphisms.trans (coprodComm a.toChart (emptyObj B k).toChart)
      (coprodEmpty (emptyObj B k).toChart a.toChart rfl))
  add_comm x y := Quotient.inductionOn₂ x y fun a b => cls_eq_of_iso (coprodComm a.toChart b.toChart)
  nsmul := nsmulRec

theorem cls_surjective : Function.Surjective (cls : Obj B k → Cls B k) :=
  fun x => Quotient.inductionOn x fun a => ⟨a, rfl⟩

/-- A definable partition splits the class. -/
theorem cls_partition (a : Obj B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) :
    cls a = cls (piece a I hI) + cls (cpiece a I hI) := by
  rw [add_comm, ← cls_coprod]
  exact (cls_eq_of_iso (RVTaggedPartitionIsomorphisms.partitionTaggedIso (ofChart a.toChart) I hI)).symm

/-- Isomorphic objects have isomorphic corresponding pieces. -/
theorem cls_piece_image {a b : Obj B k} (F : Iso a.toChart b.toChart) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) :
    cls (piece a I hI) = cls (piece b (image F I) (image_definable F I hI)) :=
  cls_eq_of_iso (restrictIso F I hI)

/-- The class in the Section 4 ring `K μRV^db[*]`. -/
def toRing : Cls B k →+ RVBoundedRing.Ring B where
  toFun := Quotient.lift (fun a => RVBoundedRing.objectClass a)
    (fun _ _ h => by
      obtain ⟨F⟩ := h
      exact RVBoundedRing.objectClass_iso F)
  map_zero' := RVBoundedRing.objectClass_empty (emptyObj B k) rfl
  map_add' x y := Quotient.inductionOn₂ x y fun a b =>
    RVTaggedCoproductClasses.bounded_coproduct_class a b

theorem toRing_cls (a : Obj B k) : toRing (cls a) = RVBoundedRing.objectClass a := rfl

/-! ### Refinement of decompositions -/

/-- Restrictions of the same object with equal domains are isomorphic. -/
def nestedIso {n : ℕ} (X : Data B n k) (P Q : Data B n k) (hP : P.coordinate = X.coordinate)
    (hQ : Q.coordinate = X.coordinate) (hPv : P.volume = X.volume) (hQv : Q.volume = X.volume)
    (hdom : P.domain = Q.domain) : Iso P.toChart Q.toChart :=
  sameIso P Q hdom (fun u _ => by rw [hP, hQ]) (fun u _ => by rw [hPv, hQv])

/-- The complement of the image of a piece is the image of the complement. -/
theorem image_compl_domain {a b : Chart B k} (F : Iso a b) (J : Set (Fin a.arity → M)) :
    b.domain \ image F J = image F (a.domain \ J) := by
  have h := image_compl_piece (isoMap_bijOn F) (A := a.domain) (P := a.domain \ J)
    (Q := a.domain ∩ J) (by rw [Set.sdiff_union_inter]) (Set.disjoint_sdiff_inter)
  unfold image
  rw [← Set.inter_assoc, Set.inter_self] at h
  exact h

/-- Two definable two-piece partitions of isomorphic objects have a common
refinement into four classes. -/
theorem refine_iso (X Y : Obj B k) (Φ : Iso X.toChart Y.toChart)
    (I : Set (Fin X.arity → M)) (hI : DefinableOverBase B (fun _ : Fin X.arity => .rv) I)
    (J : Set (Fin Y.arity → M)) (hJ : DefinableOverBase B (fun _ : Fin Y.arity => .rv) J) :
    ∃ e f g h : Cls B k, cls (piece X I hI) = e + f ∧ cls (cpiece X I hI) = g + h ∧
      cls (piece Y J hJ) = e + g ∧ cls (cpiece Y J hJ) = f + h := by
  let Ψ := RVMeasuredIsomorphisms.symm Φ
  let K := image Ψ J
  have hK : DefinableOverBase B (fun _ : Fin X.arity => .rv) K := image_definable Ψ J hJ
  refine ⟨cls (piece (piece X I hI) K hK), cls (cpiece (piece X I hI) K hK),
    cls (piece (cpiece X I hI) K hK), cls (cpiece (cpiece X I hI) K hK),
    cls_partition _ _ _, cls_partition _ _ _, ?_, ?_⟩
  · have h1 : cls (piece Y J hJ) = cls (piece X K hK) := by
      have h := cls_piece_image Ψ J hJ
      exact h
    rw [h1, cls_partition (piece X K hK) I hI]
    congr 1
    · apply cls_eq_of_iso
      refine sameIso (inside (ofChart (piece X K hK).toChart) I hI)
        (inside (ofChart (piece X I hI).toChart) K hK) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      change (X.domain ∩ K) ∩ I = (X.domain ∩ I) ∩ K
      rw [Set.inter_assoc, Set.inter_comm K I, ← Set.inter_assoc]
    · apply cls_eq_of_iso
      refine sameIso (outside (ofChart (piece X K hK).toChart) I hI)
        (inside (ofChart (cpiece X I hI).toChart) K hK) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      change (X.domain ∩ K) \ I = (X.domain \ I) ∩ K
      ext u
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      tauto
  · have hc : cls (cpiece Y J hJ) = cls (cpiece X K hK) := by
      have h := cls_piece_image Ψ (Y.domain \ J) (difference_definable B _ _ Y.domain_definable hJ)
      refine Eq.trans ?_ (h.trans ?_)
      · apply cls_eq_of_iso
        refine sameIso (outside (ofChart Y.toChart) J hJ)
          (inside (ofChart Y.toChart) (Y.domain \ J) (difference_definable B _ _ Y.domain_definable hJ)) ?_
          (fun _ _ => rfl) (fun _ _ => rfl)
        change Y.domain \ J = Y.domain ∩ (Y.domain \ J)
        rw [Set.inter_eq_self_of_subset_right Set.sdiff_subset]
      · apply cls_eq_of_iso
        refine sameIso (inside (ofChart X.toChart) (image Ψ (Y.domain \ J)) (image_definable Ψ _
          (difference_definable B _ _ Y.domain_definable hJ)))
          (outside (ofChart X.toChart) K hK) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
        change X.domain ∩ image Ψ (Y.domain \ J) = X.domain \ K
        rw [← image_compl_domain Ψ J]
        exact Set.inter_eq_self_of_subset_right Set.sdiff_subset
    rw [hc, cls_partition (cpiece X K hK) I hI]
    congr 1
    · apply cls_eq_of_iso
      refine sameIso (inside (ofChart (cpiece X K hK).toChart) I hI)
        (outside (ofChart (piece X I hI).toChart) K hK) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      change (X.domain \ K) ∩ I = (X.domain ∩ I) \ K
      rw [Set.inter_sdiff_right_comm]
    · apply cls_eq_of_iso
      refine sameIso (outside (ofChart (cpiece X K hK).toChart) I hI)
        (outside (ofChart (cpiece X I hI).toChart) K hK) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      change (X.domain \ K) \ I = (X.domain \ I) \ K
      rw [Set.sdiff_sdiff_comm]

/-- Refinement in the class monoid: `p + q = r + s` has a common refinement. -/
theorem refine2 (p q r s : Cls B k) (h : p + q = r + s) :
    ∃ e f g h' : Cls B k, p = e + f ∧ q = g + h' ∧ r = e + g ∧ s = f + h' := by
  obtain ⟨P, rfl⟩ := cls_surjective p
  obtain ⟨Q, rfl⟩ := cls_surjective q
  obtain ⟨R', rfl⟩ := cls_surjective r
  obtain ⟨S, rfl⟩ := cls_surjective s
  rw [← cls_coprod, ← cls_coprod, cls_eq_iff] at h
  obtain ⟨Φ⟩ := h
  obtain ⟨e, f, g, h', h1, h2, h3, h4⟩ := refine_iso (coprod P Q) (coprod R' S) Φ
    (L P.toChart Q.toChart).domain (L P.toChart Q.toChart).domain_definable
    (L R'.toChart S.toChart).domain (L R'.toChart S.toChart).domain_definable
  refine ⟨e, f, g, h', ?_, ?_, ?_, ?_⟩
  · rw [← h1]
    exact (cls_eq_of_iso (coprodInsideLeft P.toChart Q.toChart)).symm
  · rw [← h2]
    exact (cls_eq_of_iso (coprodOutsideLeft P.toChart Q.toChart)).symm
  · rw [← h3]
    exact (cls_eq_of_iso (coprodInsideLeft R'.toChart S.toChart)).symm
  · rw [← h4]
    exact (cls_eq_of_iso (coprodOutsideLeft R'.toChart S.toChart)).symm

/-- The class monoid has no nontrivial sums equal to zero. -/
theorem eq_zero_of_add_eq_zero (x y : Cls B k) (h : x + y = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  obtain ⟨b, rfl⟩ := cls_surjective y
  rw [← cls_coprod, ← cls_zero, cls_eq_iff] at h
  obtain ⟨Φ⟩ := h
  apply cls_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  let v := (RVMeasuredIsomorphisms.symm (RVTaggedComponentIsomorphisms.leftIso a.toChart b.toChart)).equiv ⟨u, hu⟩
  have hv : v.val ∈ (coprod a b).domain := Or.inl v.property
  exact (Φ.equiv ⟨v.val, hv⟩).property

/-- Isomorphic objects have isomorphic complementary pieces. -/
theorem cls_cpiece_image {a b : Obj B k} (F : Iso a.toChart b.toChart) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) :
    cls (cpiece a I hI) = cls (cpiece b (image F I) (image_definable F I hI)) := by
  have hD := difference_definable B _ _ a.domain_definable hI
  have h := cls_piece_image F (a.domain \ I) hD
  refine Eq.trans ?_ (h.trans ?_)
  · apply cls_eq_of_iso
    refine sameIso (outside (ofChart a.toChart) I hI)
      (inside (ofChart a.toChart) (a.domain \ I) hD) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    change a.domain \ I = a.domain ∩ (a.domain \ I)
    rw [Set.inter_eq_self_of_subset_right Set.sdiff_subset]
  · apply cls_eq_of_iso
    refine sameIso (inside (ofChart b.toChart) (image F (a.domain \ I)) (image_definable F _ hD))
      (outside (ofChart b.toChart) (image F I) (image_definable F I hI)) ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    change b.domain ∩ image F (a.domain \ I) = b.domain \ image F I
    rw [← image_compl_domain F I]
    exact Set.inter_eq_self_of_subset_right Set.sdiff_subset

/-- A class is zero exactly when its objects are empty. -/
theorem cls_eq_zero_iff (a : Obj B k) : cls a = 0 ↔ a.domain = ∅ := by
  constructor
  · intro h
    rw [← cls_zero, cls_eq_iff] at h
    obtain ⟨Φ⟩ := h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact (Φ.equiv ⟨u, hu⟩).property
  · exact cls_empty a

/-- Decomposing an object along a class decomposition. -/
theorem exists_split (a : Obj B k) (p q : Cls B k) (h : cls a = p + q) :
    ∃ (I : Set (Fin a.arity → M)) (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I),
      cls (piece a I hI) = p ∧ cls (cpiece a I hI) = q := by
  obtain ⟨P, rfl⟩ := cls_surjective p
  obtain ⟨Q, rfl⟩ := cls_surjective q
  rw [← cls_coprod, cls_eq_iff] at h
  obtain ⟨Φ⟩ := h
  let Ψ := RVMeasuredIsomorphisms.symm Φ
  refine ⟨image Ψ (L P.toChart Q.toChart).domain,
    image_definable Ψ _ (L P.toChart Q.toChart).domain_definable, ?_, ?_⟩
  · rw [← cls_piece_image Ψ _ (L P.toChart Q.toChart).domain_definable]
    exact cls_eq_of_iso (coprodInsideLeft P.toChart Q.toChart)
  · rw [← cls_cpiece_image Ψ _ (L P.toChart Q.toChart).domain_definable]
    exact cls_eq_of_iso (coprodOutsideLeft P.toChart Q.toChart)

end DiamondIntegral.Section7.BoundedClasses

/-! ### Matrix refinement in refinement monoids -/

namespace DiamondIntegral.Section7.Refinement

variable {α : Type*} [AddCommMonoid α]

variable (α) in
/-- Two-by-two refinement. -/
def Refine2 : Prop :=
  ∀ p q r s : α, p + q = r + s → ∃ e f g h : α, p = e + f ∧ q = g + h ∧ r = e + g ∧ s = f + h

variable (α) in
/-- No nontrivial sum is zero. -/
def ZeroSumFree : Prop := ∀ x y : α, x + y = 0 → x = 0

theorem eq_zero_of_sum_eq_zero (hz : ZeroSumFree α) {m : ℕ} (b : Fin m → α)
    (h : ∑ j, b j = 0) (j : Fin m) : b j = 0 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h
  exact hz _ _ h

theorem refine_one_many (h2 : Refine2 α) (hz : ZeroSumFree α) :
    ∀ (m : ℕ) (a A : α) (b : Fin m → α), a + A = ∑ j, b j →
      ∃ d d' : Fin m → α, (∀ j, b j = d j + d' j) ∧ ∑ j, d j = a ∧ ∑ j, d' j = A
  | 0, a, A, b, h => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
    have ha : a = 0 := hz _ _ h
    have hA : A = 0 := hz _ _ (by rw [add_comm]; exact h)
    exact ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, by simp [ha], by simp [hA]⟩
  | m + 1, a, A, b, h => by
    rw [Fin.sum_univ_succ] at h
    obtain ⟨e, f, g, h', ha, hA, hb0, hrest⟩ := h2 _ _ _ _ h
    obtain ⟨d0, d0', hd, hs, hs'⟩ := refine_one_many h2 hz m f h' (fun j => b j.succ) hrest.symm
    refine ⟨Fin.cons e d0, Fin.cons g d0', ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hb0
      · simpa using hd j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hs, ha]
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hs', hA]

/-- Matrix refinement: two finite decompositions of the same element have a
common refinement. -/
theorem refine_matrix (h2 : Refine2 α) (hz : ZeroSumFree α) :
    ∀ (n m : ℕ) (a : Fin n → α) (b : Fin m → α), ∑ i, a i = ∑ j, b j →
      ∃ c : Fin n → Fin m → α, (∀ i, ∑ j, c i j = a i) ∧ (∀ j, ∑ i, c i j = b j)
  | 0, m, a, b, h => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
    refine ⟨Fin.elim0, fun i => i.elim0, fun j => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (eq_zero_of_sum_eq_zero hz b h.symm j).symm
  | n + 1, m, a, b, h => by
    rw [Fin.sum_univ_succ] at h
    obtain ⟨d, d', hd, hs, hs'⟩ := refine_one_many h2 hz m (a 0) _ b h
    obtain ⟨c', hrow, hcol⟩ := refine_matrix h2 hz n m (fun i => a i.succ) d' hs'.symm
    refine ⟨Fin.cons d c', fun i => ?_, fun j => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hs
      · simpa using hrow i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hcol j, hd j]

end DiamondIntegral.Section7.Refinement
