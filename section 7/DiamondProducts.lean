import «section 6».DiamondProduct
import «section 6».DiamondGroupoidMaps
import Integration7.MixedDomainProductJacobians

/-! Products of morphisms in `μVF^◇` (Definition 6.34 objects, products as in
`DiamondProduct`). This is what the graded ring `K μVF^◇[*]` of Theorem 7.26
needs: the class of a product depends only on the classes of the factors.

The product of two maps is the mixed product map of `Integration in ACVF`
(`mixedDomainProductMap`): on `(x, y; t, u)` it acts as
`(f(x, t).1, g(y, u).1; f(x, t).2, g(y, u).2)`, with `Fin.append` separately on
the VF and on the RV coordinates.

* The product of two proper covariant homeomorphisms is one: its graph fibres
  are products of the graph fibres of the factors, so the radii are appended.
  Over a proper invariant set the identity is a proper covariant
  homeomorphism, proved directly without further hypotheses.
* If `f` is relatively unary in `(i, j)`, then `f × id` is relatively unary in
  `(castAdd i, castAdd j)` and `id × f` in `(natAdd i, natAdd j)`. In degree
  zero the product with an identity fixes every VF coordinate. Hence
  factorizations multiply with identities.
* At a VF-generic point of `A × B` both parts are VF-generic. The product map
  is differentiable there, and its Jacobian is the product of the factor
  Jacobians by the block Jacobian of `mixedDomainProductMap`. The product forms
  give `ω_A ω_B / (ω_A' ω_B') = (ω_A / ω_A') (ω_B / ω_B')`.

The main results are `Morphism.product_exists` (with the product map named),
`isomorphic_product_left`, `isomorphic_product_right` and
`isomorphic_product`. They use the Section 6 hypotheses `h00 hc hκ hs hsmall hv`
only, and no `GammaPiecewiseRationalAffineInput` or nontrivial-Γ input. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2 DiamondIntegral.Section6

namespace DiamondIntegral.Section7.DiamondProducts
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondProduct
  DiamondIntegral.Section6.DiamondGroupoid
open IntegrationInACVF.Section7 (mixedDomainProductMap mixed_domain_product_map_bijective
  mixed_domain_product_map_pair has_mixed_vf_jacobian_domain_product)

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {n m a a' a'' b b' b'' : ℕ}

/-! ### Coordinates -/

section Coordinates

theorem append_comp_castAdd {X : Type} (x : Fin n → X) (y : Fin m → X) :
    Fin.append x y ∘ Fin.castAdd m = x :=
  funext fun i => Fin.append_left x y i

theorem append_comp_natAdd {X : Type} (x : Fin n → X) (y : Fin m → X) :
    Fin.append x y ∘ Fin.natAdd n = y :=
  funext fun i => Fin.append_right x y i

theorem congruent_append {α : Fin n → Gamma M} {β : Fin m → Gamma M} {x y : Fin (n + m) → VF M}
    (h₁ : Congruent α (x ∘ Fin.castAdd m) (y ∘ Fin.castAdd m))
    (h₂ : Congruent β (x ∘ Fin.natAdd n) (y ∘ Fin.natAdd n)) :
    Congruent (Fin.append α β) x y := by
  intro i
  induction i using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    exact h₁ j
  | right j =>
    rw [Fin.append_right]
    exact h₂ j

theorem vfBounded_of_parts {P : Set (Mixed M (n + m) (a + b))} {P₁ : Set (Mixed M n a)}
    {P₂ : Set (Mixed M m b)} (h₁ : VFBounded P₁) (h₂ : VFBounded P₂)
    (hP : ∀ p ∈ P, (p.1 ∘ Fin.castAdd m, p.2 ∘ Fin.castAdd b) ∈ P₁ ∧
      (p.1 ∘ Fin.natAdd n, p.2 ∘ Fin.natAdd a) ∈ P₂) : VFBounded P := by
  obtain ⟨γ₁, hγ₁⟩ := h₁
  obtain ⟨γ₂, hγ₂⟩ := h₂
  refine ⟨min γ₁ γ₂, fun p hp i => ?_⟩
  have h := hP p hp
  induction i using Fin.addCases with
  | left j => exact le_trans (show (min γ₁ γ₂).val ≤ γ₁.val from min_le_left γ₁ γ₂) (hγ₁ _ h.1 j)
  | right j => exact le_trans (show (min γ₁ γ₂).val ≤ γ₂.val from min_le_right γ₁ γ₂) (hγ₂ _ h.2 j)

theorem rvBounded_of_parts {P : Set (Mixed M (n + m) (a + b))} {P₁ : Set (Mixed M n a)}
    {P₂ : Set (Mixed M m b)} (h₁ : RVSupportDoublyBounded P₁) (h₂ : RVSupportDoublyBounded P₂)
    (hP : ∀ p ∈ P, (p.1 ∘ Fin.castAdd m, p.2 ∘ Fin.castAdd b) ∈ P₁ ∧
      (p.1 ∘ Fin.natAdd n, p.2 ∘ Fin.natAdd a) ∈ P₂) : RVSupportDoublyBounded P := by
  obtain ⟨δ₁, hδ₁⟩ := h₁
  obtain ⟨δ₂, hδ₂⟩ := h₂
  refine ⟨max δ₁ δ₂, fun p hp i => ?_⟩
  have h := hP p hp
  induction i using Fin.addCases with
  | left j =>
    have hj := hδ₁ _ h.1 j
    exact ⟨le_trans (show ((max δ₁ δ₂)⁻¹).val ≤ (δ₁⁻¹).val from
        inv_le_inv_iff.mpr (le_max_left δ₁ δ₂)) hj.1,
      le_trans hj.2 (show δ₁.val ≤ (max δ₁ δ₂).val from le_max_left δ₁ δ₂)⟩
  | right j =>
    have hj := hδ₂ _ h.2 j
    exact ⟨le_trans (show ((max δ₁ δ₂)⁻¹).val ≤ (δ₂⁻¹).val from
        inv_le_inv_iff.mpr (le_max_right δ₁ δ₂)) hj.1,
      le_trans hj.2 (show δ₂.val ≤ (max δ₁ δ₂).val from le_max_right δ₁ δ₂)⟩

end Coordinates

/-! ### The product map -/

section ProductMap

variable {U : DefSet (rawMixedSpace (M := M) n a) S} {U' : DefSet (rawMixedSpace (M := M) n a') S}
variable {U'' : DefSet (rawMixedSpace (M := M) n a'') S}
variable {V : DefSet (rawMixedSpace (M := M) m b) S} {V' : DefSet (rawMixedSpace (M := M) m b') S}
variable {V'' : DefSet (rawMixedSpace (M := M) m b'') S}

/-- The first factor of a point of a mixed product. -/
def leftPart (p : mixedProductDomain U V) : U :=
  ⟨(p.val.1 ∘ Fin.castAdd m, p.val.2 ∘ Fin.castAdd b),
    ((mem_mixedProductDomain U V p.val).mp p.property).1⟩

/-- The second factor of a point of a mixed product. -/
def rightPart (p : mixedProductDomain U V) : V :=
  ⟨(p.val.1 ∘ Fin.natAdd n, p.val.2 ∘ Fin.natAdd a),
    ((mem_mixedProductDomain U V p.val).mp p.property).2⟩

omit [M ⊨ Axioms.ACVF] in
theorem unpack_eq_parts (p : mixedProductDomain U V) :
    mixedUnpack U V p = ⟨((leftPart p).val, (rightPart p).val),
      (leftPart p).property, (rightPart p).property⟩ :=
  Subtype.ext (unpack_val U V p)

omit [M ⊨ Axioms.ACVF] in
theorem pack_parts (p : mixedProductDomain U V) :
    (mixedPack U V).toImage ⟨((leftPart p).val, (rightPart p).val),
      (leftPart p).property, (rightPart p).property⟩ = p := by
  rw [← unpack_eq_parts]
  exact mixedPack_unpack U V p

/-- The product map acts coordinatewise, with `Fin.append` on VF and on RV
coordinates. -/
theorem productMap_val (f : Map U U') (g : Map V V') (p : mixedProductDomain U V) :
    (mixedDomainProductMap f g p).val =
      (Fin.append (f (leftPart p)).val.1 (g (rightPart p)).val.1,
        Fin.append (f (leftPart p)).val.2 (g (rightPart p)).val.2) := by
  conv_lhs => rw [← pack_parts p]
  rw [mixed_domain_product_map_pair]
  rfl

theorem leftPart_productMap (f : Map U U') (g : Map V V') (p : mixedProductDomain U V) :
    leftPart (mixedDomainProductMap f g p) = f (leftPart p) := by
  apply Subtype.ext
  change ((mixedDomainProductMap f g p).val.1 ∘ Fin.castAdd m,
    (mixedDomainProductMap f g p).val.2 ∘ Fin.castAdd b') = (f (leftPart p)).val
  rw [productMap_val, append_comp_castAdd, append_comp_castAdd]
  rfl

theorem rightPart_productMap (f : Map U U') (g : Map V V') (p : mixedProductDomain U V) :
    rightPart (mixedDomainProductMap f g p) = g (rightPart p) := by
  apply Subtype.ext
  change ((mixedDomainProductMap f g p).val.1 ∘ Fin.natAdd n,
    (mixedDomainProductMap f g p).val.2 ∘ Fin.natAdd a') = (g (rightPart p)).val
  rw [productMap_val, append_comp_natAdd, append_comp_natAdd]
  rfl

theorem productMap_id (U : DefSet (rawMixedSpace (M := M) n a) S)
    (V : DefSet (rawMixedSpace (M := M) m b) S) :
    mixedDomainProductMap (Map.id U) (Map.id V) = Map.id (mixedProductDomain U V) := by
  apply Map.ext
  intro p
  apply Subtype.ext
  rw [productMap_val]
  exact Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

theorem productMap_comp (f : Map U U') (f' : Map U' U'') (g : Map V V') (g' : Map V' V'') :
    mixedDomainProductMap (f'.comp f) (g'.comp g) =
      (mixedDomainProductMap f' g').comp (mixedDomainProductMap f g) := by
  apply Map.ext
  intro p
  apply Subtype.ext
  rw [Map.comp_apply, productMap_val, productMap_val, leftPart_productMap, rightPart_productMap]
  rfl

theorem productMap_comp_left (f : Map U U') (f' : Map U' U'') (V : DefSet (rawMixedSpace (M := M) m b) S) :
    mixedDomainProductMap (f'.comp f) (Map.id V) =
      (mixedDomainProductMap f' (Map.id V)).comp (mixedDomainProductMap f (Map.id V)) := by
  have h := productMap_comp f f' (Map.id V) (Map.id V)
  rwa [show (Map.id V).comp (Map.id V) = Map.id V from Map.ext (fun _ => rfl)] at h

theorem productMap_comp_right (U : DefSet (rawMixedSpace (M := M) n a) S) (g : Map V V') (g' : Map V' V'') :
    mixedDomainProductMap (Map.id U) (g'.comp g) =
      (mixedDomainProductMap (Map.id U) g').comp (mixedDomainProductMap (Map.id U) g) := by
  have h := productMap_comp (Map.id U) (Map.id U) g g'
  rwa [show (Map.id U).comp (Map.id U) = Map.id U from Map.ext (fun _ => rfl)] at h

/-- The general product factors as `(f × id) ∘ (id × g)`. -/
theorem productMap_eq_comp (f : Map U U') (g : Map V V') :
    mixedDomainProductMap f g =
      (mixedDomainProductMap f (Map.id V')).comp (mixedDomainProductMap (Map.id U) g) := by
  have h := productMap_comp (Map.id U) f g (Map.id V')
  rwa [show f.comp (Map.id U) = f from Map.ext (fun _ => rfl),
    show (Map.id V').comp g = g from Map.ext (fun _ => rfl)] at h

theorem productMap_inverse {f : Map U U'} {g : Map V V'} (hf : Function.Bijective f)
    (hg : Function.Bijective g) (h : Function.Bijective (mixedDomainProductMap f g)) :
    (mixedDomainProductMap f g).inverse h = mixedDomainProductMap (f.inverse hf) (g.inverse hg) := by
  apply Map.ext
  intro q
  have h₁ : mixedDomainProductMap f g (mixedDomainProductMap (f.inverse hf) (g.inverse hg) q) = q := by
    apply Subtype.ext
    rw [productMap_val, leftPart_productMap, rightPart_productMap, Map.apply_inverse,
      Map.apply_inverse]
    exact Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd
  have h₂ := Map.inverse_apply (mixedDomainProductMap f g) h
    (mixedDomainProductMap (f.inverse hf) (g.inverse hg) q)
  rw [h₁] at h₂
  exact h₂

end ProductMap

/-! ### Graph fibres of products -/

section GraphFibres

variable {U : DefSet (rawMixedSpace (M := M) n a) S} {U' : DefSet (rawMixedSpace (M := M) n a') S}
variable {V : DefSet (rawMixedSpace (M := M) m b) S} {V' : DefSet (rawMixedSpace (M := M) m b') S}

theorem graphFibre_product (f : Map U U') (g : Map V V')
    (u : Fin (a + b) → RVInfinity M) (v : Fin (a' + b') → RVInfinity M)
    (x y : Fin (n + m) → VF M) :
    graphFibre (mixedDomainProductMap f g) u v x y ↔
      graphFibre f (u ∘ Fin.castAdd b) (v ∘ Fin.castAdd b') (x ∘ Fin.castAdd m) (y ∘ Fin.castAdd m) ∧
      graphFibre g (u ∘ Fin.natAdd a) (v ∘ Fin.natAdd a') (x ∘ Fin.natAdd n) (y ∘ Fin.natAdd n) := by
  constructor
  · rintro ⟨p, hp, hfp⟩
    rw [productMap_val] at hfp
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfp
    have hx : p.val.1 = x := congrArg Prod.fst hp
    have hu : p.val.2 = u := congrArg Prod.snd hp
    refine ⟨⟨leftPart p, ?_, ?_⟩, ⟨rightPart p, ?_, ?_⟩⟩
    · exact Prod.ext (congrArg (· ∘ Fin.castAdd m) hx) (congrArg (· ∘ Fin.castAdd b) hu)
    · exact Prod.ext (append_comp_castAdd _ _).symm (append_comp_castAdd _ _).symm
    · exact Prod.ext (congrArg (· ∘ Fin.natAdd n) hx) (congrArg (· ∘ Fin.natAdd a) hu)
    · exact Prod.ext (append_comp_natAdd _ _).symm (append_comp_natAdd _ _).symm
  · rintro ⟨⟨q, hq, hfq⟩, ⟨q', hq', hfq'⟩⟩
    have hmem : (x, u) ∈ (mixedProductDomain U V).carrier :=
      (mem_mixedProductDomain U V (x, u)).mpr ⟨hq ▸ q.property, hq' ▸ q'.property⟩
    refine ⟨⟨(x, u), hmem⟩, rfl, ?_⟩
    rw [productMap_val]
    have hl : leftPart (⟨(x, u), hmem⟩ : mixedProductDomain U V) = q := Subtype.ext hq.symm
    have hr : rightPart (⟨(x, u), hmem⟩ : mixedProductDomain U V) = q' := Subtype.ext hq'.symm
    rw [hl, hr, hfq, hfq']
    exact Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

theorem source_product (f : Map U U') (g : Map V V')
    (u : Fin (a + b) → RVInfinity M) (v : Fin (a' + b') → RVInfinity M) (x : Fin (n + m) → VF M) :
    x ∈ graphFibreSource (mixedDomainProductMap f g) u v ↔
      x ∘ Fin.castAdd m ∈ graphFibreSource f (u ∘ Fin.castAdd b) (v ∘ Fin.castAdd b') ∧
      x ∘ Fin.natAdd n ∈ graphFibreSource g (u ∘ Fin.natAdd a) (v ∘ Fin.natAdd a') := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨h₁, h₂⟩ := (graphFibre_product f g u v x y).mp hy
    exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩
  · rintro ⟨⟨y₁, h₁⟩, ⟨y₂, h₂⟩⟩
    refine ⟨Fin.append y₁ y₂, (graphFibre_product f g u v x _).mpr ⟨?_, ?_⟩⟩
    · rwa [append_comp_castAdd]
    · rwa [append_comp_natAdd]

theorem range_product (f : Map U U') (g : Map V V')
    (u : Fin (a + b) → RVInfinity M) (v : Fin (a' + b') → RVInfinity M) (y : Fin (n + m) → VF M) :
    y ∈ graphFibreRange (mixedDomainProductMap f g) u v ↔
      y ∘ Fin.castAdd m ∈ graphFibreRange f (u ∘ Fin.castAdd b) (v ∘ Fin.castAdd b') ∧
      y ∘ Fin.natAdd n ∈ graphFibreRange g (u ∘ Fin.natAdd a) (v ∘ Fin.natAdd a') := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h₁, h₂⟩ := (graphFibre_product f g u v x y).mp hx
    exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩
  · rintro ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩⟩
    refine ⟨Fin.append x₁ x₂, (graphFibre_product f g u v _ y).mpr ⟨?_, ?_⟩⟩
    · rwa [append_comp_castAdd]
    · rwa [append_comp_natAdd]

theorem map_product (f : Map U U') (g : Map V V')
    (u : Fin (a + b) → RVInfinity M) (v : Fin (a' + b') → RVInfinity M) {x : Fin (n + m) → VF M}
    (hx : x ∈ graphFibreSource (mixedDomainProductMap f g) u v) :
    graphFibreMap (mixedDomainProductMap f g) u v x =
      Fin.append (graphFibreMap f (u ∘ Fin.castAdd b) (v ∘ Fin.castAdd b') (x ∘ Fin.castAdd m))
        (graphFibreMap g (u ∘ Fin.natAdd a) (v ∘ Fin.natAdd a') (x ∘ Fin.natAdd n)) := by
  obtain ⟨h₁, h₂⟩ := (source_product f g u v x).mp hx
  apply graphFibre_functional _ u v (graphFibreMap_graph _ u v hx)
  apply (graphFibre_product f g u v x _).mpr
  rw [append_comp_castAdd, append_comp_natAdd]
  exact ⟨graphFibreMap_graph f _ _ h₁, graphFibreMap_graph g _ _ h₂⟩

theorem range_parts (f : Map U U') (g : Map V V') {q : Mixed M (n + m) (a' + b')}
    (hq : q ∈ mixedMapRange (mixedDomainProductMap f g)) :
    (q.1 ∘ Fin.castAdd m, q.2 ∘ Fin.castAdd b') ∈ mixedMapRange f ∧
      (q.1 ∘ Fin.natAdd n, q.2 ∘ Fin.natAdd a') ∈ mixedMapRange g := by
  obtain ⟨p, hp⟩ := hq
  have he : q = (mixedDomainProductMap f g p).val := hp.symm
  rw [he, productMap_val]
  exact ⟨⟨leftPart p, Prod.ext (append_comp_castAdd _ _).symm (append_comp_castAdd _ _).symm⟩,
    ⟨rightPart p, Prod.ext (append_comp_natAdd _ _).symm (append_comp_natAdd _ _).symm⟩⟩

theorem namedGammaTuple_append {u : Fin (a + b) → RVInfinity M} {v : Fin (a' + b') → RVInfinity M}
    {α : Fin n → Gamma M} {β : Fin m → Gamma M}
    (hα : NamedGammaTuple (graphFibreBase S (u ∘ Fin.castAdd b) (v ∘ Fin.castAdd b')) α)
    (hβ : NamedGammaTuple (graphFibreBase S (u ∘ Fin.natAdd a) (v ∘ Fin.natAdd a')) β) :
    NamedGammaTuple (graphFibreBase S u v) (Fin.append α β) := by
  intro i
  induction i using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    exact (hα j).mono (Set.union_subset_union
      (Set.union_subset_union_right S (fun z ⟨l, hl⟩ => ⟨Fin.castAdd b l, hl⟩))
      (fun z ⟨l, hl⟩ => ⟨Fin.castAdd b' l, hl⟩))
  | right j =>
    rw [Fin.append_right]
    exact (hβ j).mono (Set.union_subset_union
      (Set.union_subset_union_right S (fun z ⟨l, hl⟩ => ⟨Fin.natAdd a l, hl⟩))
      (fun z ⟨l, hl⟩ => ⟨Fin.natAdd a' l, hl⟩))

/-- The product of two proper covariant maps is proper covariant: the graph
fibres of the product are the products of the graph fibres of the factors. -/
theorem properCovariant_product {f : Map U U'} {g : Map V V'}
    (hf : ProperCovariant f) (hg : ProperCovariant g) :
    ProperCovariant (mixedDomainProductMap f g) := by
  refine ⟨vfBounded_of_parts hf.sourceVFBounded hg.sourceVFBounded
      (fun p hp => (mem_mixedProductDomain U V p).mp hp),
    vfBounded_of_parts hf.imageVFBounded hg.imageVFBounded (fun q hq => range_parts f g hq),
    rvBounded_of_parts hf.sourceRVBounded hg.sourceRVBounded
      (fun p hp => (mem_mixedProductDomain U V p).mp hp),
    rvBounded_of_parts hf.imageRVBounded hg.imageRVBounded (fun q hq => range_parts f g hq),
    fun u v => ?_⟩
  obtain ⟨α, β, hαn, hβn, hα, hβ, hcov⟩ := hf.radii (u ∘ Fin.castAdd b) (v ∘ Fin.castAdd b')
  obtain ⟨α', β', hαn', hβn', hα', hβ', hcov'⟩ := hg.radii (u ∘ Fin.natAdd a) (v ∘ Fin.natAdd a')
  refine ⟨Fin.append α α', Fin.append β β', namedGammaTuple_append hαn hαn',
    namedGammaTuple_append hβn hβn', ?_, ?_, ?_⟩
  · intro x y hxy
    rw [source_product, source_product]
    exact and_congr (hα _ _ (congruent_left hxy)) (hα' _ _ (congruent_right hxy))
  · intro x y hxy
    rw [range_product, range_product]
    exact and_congr (hβ _ _ (congruent_left hxy)) (hβ' _ _ (congruent_right hxy))
  · intro x hx y hy hxy
    have hx' := (source_product f g u v x).mp hx
    have hy' := (source_product f g u v y).mp hy
    rw [map_product f g u v hx, map_product f g u v hy]
    apply congruent_append
    · rw [append_comp_castAdd, append_comp_castAdd]
      exact hcov _ hx'.1 _ hy'.1 (congruent_left hxy)
    · rw [append_comp_natAdd, append_comp_natAdd]
      exact hcov' _ hx'.2 _ hy'.2 (congruent_right hxy)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousOnGraphFibres_product {f : Map U U'} {g : Map V V'}
    (hf : ContinuousOnGraphFibres (G := G) f) (hg : ContinuousOnGraphFibres (G := G) g) :
    ContinuousOnGraphFibres (G := G) (mixedDomainProductMap f g) := by
  intro u v
  have hL : Continuous (fun x : Fin (n + m) → VF M => x ∘ Fin.castAdd m) :=
    continuous_pi fun i => continuous_apply _
  have hR : Continuous (fun x : Fin (n + m) → VF M => x ∘ Fin.natAdd n) :=
    continuous_pi fun i => continuous_apply _
  have h₁ : ContinuousOn
      (fun x : Fin (n + m) → VF M =>
        graphFibreMap f (u ∘ Fin.castAdd b) (v ∘ Fin.castAdd b') (x ∘ Fin.castAdd m))
      (graphFibreSource (mixedDomainProductMap f g) u v) :=
    (hf _ _).comp hL.continuousOn (fun x hx => ((source_product f g u v x).mp hx).1)
  have h₂ : ContinuousOn
      (fun x : Fin (n + m) → VF M =>
        graphFibreMap g (u ∘ Fin.natAdd a) (v ∘ Fin.natAdd a') (x ∘ Fin.natAdd n))
      (graphFibreSource (mixedDomainProductMap f g) u v) :=
    (hg _ _).comp hR.continuousOn (fun x hx => ((source_product f g u v x).mp hx).2)
  refine ContinuousOn.congr ?_ (fun x hx => map_product f g u v hx)
  rw [continuousOn_pi]
  intro i
  induction i using Fin.addCases with
  | left j =>
    simp only [Fin.append_left]
    exact (continuous_apply j).comp_continuousOn h₁
  | right j =>
    simp only [Fin.append_right]
    exact (continuous_apply j).comp_continuousOn h₂

/-- The product of two proper covariant homeomorphisms is one. -/
theorem properCovariantHomeomorphism_product {f : Map U U'} {g : Map V V'}
    (hf : ProperCovariantHomeomorphism (G := G) f) (hg : ProperCovariantHomeomorphism (G := G) g) :
    ProperCovariantHomeomorphism (G := G) (mixedDomainProductMap f g) := by
  have hb := mixed_domain_product_map_bijective f g hf.bijective hg.bijective
  refine ⟨hb, properCovariant_product hf.covariant hg.covariant,
    continuousOnGraphFibres_product hf.continuous hg.continuous, ?_, ?_⟩
  · rw [productMap_inverse hf.bijective hg.bijective hb]
    exact properCovariant_product hf.inverseCovariant hg.inverseCovariant
  · rw [productMap_inverse hf.bijective hg.bijective hb]
    exact continuousOnGraphFibres_product hf.inverseContinuous hg.inverseContinuous

end GraphFibres

/-! ### The identity of a proper invariant set -/

section Identity

variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem identity_graphFibreMap {u v : Fin r → RVInfinity M} {x : Fin n → VF M}
    (hx : x ∈ graphFibreSource (Map.id A) u v) : graphFibreMap (Map.id A) u v x = x := by
  obtain ⟨p, hp, hfp⟩ := graphFibreMap_graph (Map.id A) u v hx
  exact (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)

theorem properCovariant_id (hA : ProperInvariant S A.carrier) : ProperCovariant (Map.id A) := by
  have hsub : mixedMapRange (Map.id A) ⊆ A.carrier := by
    rintro _ ⟨p, rfl⟩
    exact p.property
  refine ⟨hA.vfBounded, hA.vfBounded.mono hsub, hA.rvBounded, hA.rvBounded.mono hsub,
    fun u v => ?_⟩
  obtain ⟨α, hαn, hα⟩ := hA.radii u
  have hnamed : NamedGammaTuple (graphFibreBase S u v) α :=
    fun i => (hαn i).mono Set.subset_union_left
  have hsrc : AlphaInvariant α (graphFibreSource (Map.id A) u v) := by
    intro x y hxy
    rw [identity_source_iff, identity_source_iff]
    exact and_congr_left' (hα x y hxy)
  refine ⟨α, α, hnamed, hnamed, hsrc, identity_range_eq_source A u v ▸ hsrc, ?_⟩
  intro x hx y hy hxy
  rw [identity_graphFibreMap hx, identity_graphFibreMap hy]
  exact hxy

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousOnGraphFibres_id (A : DefSet (rawMixedSpace (M := M) n r) S) :
    ContinuousOnGraphFibres (G := G) (Map.id A) := by
  intro u v
  apply continuous_id.continuousOn.congr
  intro x hx
  obtain ⟨p, hp, hfp⟩ := graphFibreMap_graph (Map.id A) u v hx
  exact (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)

/-- Over a proper invariant set the identity is a proper covariant
homeomorphism (no hypotheses beyond proper invariance). -/
theorem properCovariantHomeomorphism_id (hA : ProperInvariant S A.carrier) :
    ProperCovariantHomeomorphism (G := G) (Map.id A) := by
  have hb : Function.Bijective (Map.id A) := ⟨fun _ _ h => h, fun z => ⟨z, rfl⟩⟩
  refine ⟨hb, properCovariant_id hA, continuousOnGraphFibres_id A, ?_, ?_⟩
  · rw [inverse_id A hb]
    exact properCovariant_id hA
  · rw [inverse_id A hb]
    exact continuousOnGraphFibres_id A

end Identity

/-! ### Relative unarity of products with an identity -/

section Unary

theorem cycleRange_val {N : ℕ} (i k : Fin N) :
    (Fin.cycleRange i k).val =
      if k.val < i.val then k.val + 1 else if k.val = i.val then 0 else k.val := by
  split_ifs with h₁ h₂
  · exact Fin.coe_cycleRange_of_lt h₁
  · have he : k = i := Fin.ext h₂
    subst he
    rw [Fin.coe_cycleRange_of_le le_rfl, ite_eq_left rfl]
  · have hlt : i < k := lt_of_le_of_ne (not_lt.mp h₁) (fun he => h₂ (congrArg Fin.val he).symm)
    exact congrArg Fin.val (Fin.cycleRange_of_gt hlt)

theorem cycleRange_castAdd (i k : Fin n) :
    Fin.cycleRange (Fin.castAdd m i) (Fin.castAdd m k) = Fin.castAdd m (Fin.cycleRange i k) := by
  apply Fin.ext
  rw [cycleRange_val, Fin.val_castAdd, Fin.val_castAdd, Fin.val_castAdd, cycleRange_val]

theorem cycleRange_castAdd_symm (i l : Fin n) :
    (Fin.cycleRange (Fin.castAdd m i)).symm (Fin.castAdd m l) =
      Fin.castAdd m ((Fin.cycleRange i).symm l) := by
  rw [Equiv.symm_apply_eq, cycleRange_castAdd, Equiv.apply_symm_apply]

theorem cycleRange_castAdd_natAdd (i : Fin n) (k : Fin m) :
    Fin.cycleRange (Fin.castAdd m i) (Fin.natAdd n k) = Fin.natAdd n k := by
  apply Fin.ext
  have hi := i.isLt
  rw [cycleRange_val, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> omega

theorem cycleRange_castAdd_natAdd_symm (i : Fin n) (k : Fin m) :
    (Fin.cycleRange (Fin.castAdd m i)).symm (Fin.natAdd n k) = Fin.natAdd n k := by
  rw [Equiv.symm_apply_eq, cycleRange_castAdd_natAdd]

theorem cycleRange_natAdd_castAdd (i j : Fin m) (k : Fin n) :
    Fin.cycleRange (Fin.natAdd n j) (Fin.castAdd m k) =
      Fin.cycleRange (Fin.natAdd n i) (Fin.castAdd m k) := by
  apply Fin.ext
  have hk := k.isLt
  rw [cycleRange_val, cycleRange_val, Fin.val_castAdd, Fin.val_natAdd, Fin.val_natAdd]
  split_ifs <;> omega

theorem cycleRange_natAdd {i k : Fin m} (hk : k ≠ i) :
    Fin.cycleRange (Fin.natAdd n i) (Fin.natAdd n k) = Fin.natAdd n (Fin.cycleRange i k) := by
  apply Fin.ext
  have hk' : k.val ≠ i.val := fun h => hk (Fin.ext h)
  rw [cycleRange_val, Fin.val_natAdd, Fin.val_natAdd, Fin.val_natAdd, cycleRange_val]
  split_ifs <;> omega

omit [M ⊨ Axioms.ACVF] in
/-- A map fixing every VF coordinate is relatively unary (or of degree zero). -/
theorem unary_of_vf_eq {N r s : ℕ} {A : DefSet (rawMixedSpace (M := M) N r) S}
    {B : DefSet (rawMixedSpace (M := M) N s) S} {F : Map A B} (h : ∀ p, (F p).val.1 = p.val.1) :
    N = 0 ∨ ∃ i j : Fin N, VFRelativelyUnary F i j := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact Or.inl hN
  · refine Or.inr ⟨⟨0, hN⟩, ⟨0, hN⟩, fun p k _ => ?_⟩
    rw [h p, Equiv.symm_apply_apply]

variable {r s : ℕ}

/-- If `f` is relatively unary in `(i, j)`, then `f × id` is relatively unary in
`(castAdd i, castAdd j)`. -/
theorem relativelyUnary_productLeft {C : DefSet (rawMixedSpace (M := M) n r) S}
    {D : DefSet (rawMixedSpace (M := M) n s) S} (B : DefSet (rawMixedSpace (M := M) m b) S)
    {f : Map C D} {i j : Fin n} (h : VFRelativelyUnary f i j) :
    VFRelativelyUnary (mixedDomainProductMap f (Map.id B)) (Fin.castAdd m i) (Fin.castAdd m j) := by
  intro p k hk
  rw [productMap_val]
  induction k using Fin.addCases with
  | left k =>
    have hk' : k ≠ j := fun he => hk (congrArg (Fin.castAdd m) he)
    rw [cycleRange_castAdd, cycleRange_castAdd_symm]
    simp only [Fin.append_left]
    rw [h (leftPart p) k hk']
    rfl
  | right k =>
    rw [cycleRange_castAdd_natAdd, cycleRange_castAdd_natAdd_symm]
    simp only [Fin.append_right, Map.id_apply]
    rfl

/-- If `g` is relatively unary in `(i, j)`, then `id × g` is relatively unary in
`(natAdd i, natAdd j)`. -/
theorem relativelyUnary_productRight (A : DefSet (rawMixedSpace (M := M) n a) S)
    {C : DefSet (rawMixedSpace (M := M) m r) S} {D : DefSet (rawMixedSpace (M := M) m s) S}
    {g : Map C D} {i j : Fin m} (h : VFRelativelyUnary g i j) :
    VFRelativelyUnary (mixedDomainProductMap (Map.id A) g) (Fin.natAdd n i) (Fin.natAdd n j) := by
  intro p k hk
  rw [productMap_val]
  induction k using Fin.addCases with
  | left k =>
    rw [cycleRange_natAdd_castAdd i j k, Equiv.symm_apply_apply]
    simp only [Fin.append_left, Map.id_apply]
    rfl
  | right k =>
    have hk' : k ≠ j := fun he => hk (congrArg (Fin.natAdd n) he)
    have hl : (Fin.cycleRange i).symm (Fin.cycleRange j k) ≠ i := fun he =>
      cycleRange_ne_zero hk' ((cycleRange_symm_eq_iff i _).mp he)
    have key : (Fin.cycleRange (Fin.natAdd n i)).symm (Fin.natAdd n (Fin.cycleRange j k)) =
        Fin.natAdd n ((Fin.cycleRange i).symm (Fin.cycleRange j k)) := by
      rw [Equiv.symm_apply_eq, cycleRange_natAdd hl, Equiv.apply_symm_apply]
    rw [cycleRange_natAdd hk', key]
    simp only [Fin.append_right]
    rw [h (rightPart p) k hk']
    rfl

theorem productLeft_vf_eq_of_zero {C : DefSet (rawMixedSpace (M := M) n r) S}
    {D : DefSet (rawMixedSpace (M := M) n s) S} (B : DefSet (rawMixedSpace (M := M) m b) S)
    (hn : n = 0) (f : Map C D) (p : mixedProductDomain C B) :
    (mixedDomainProductMap f (Map.id B) p).val.1 = p.val.1 := by
  rw [productMap_val]
  funext k
  induction k using Fin.addCases with
  | left k => exact absurd k.isLt (by omega)
  | right k =>
    simp only [Fin.append_right, Map.id_apply]
    rfl

theorem productRight_vf_eq_of_zero (A : DefSet (rawMixedSpace (M := M) n a) S)
    {C : DefSet (rawMixedSpace (M := M) m r) S} {D : DefSet (rawMixedSpace (M := M) m s) S}
    (hm : m = 0) (g : Map C D) (p : mixedProductDomain A C) :
    (mixedDomainProductMap (Map.id A) g p).val.1 = p.val.1 := by
  rw [productMap_val]
  funext k
  induction k using Fin.addCases with
  | left k =>
    simp only [Fin.append_left, Map.id_apply]
    rfl
  | right k => exact absurd k.isLt (by omega)

end Unary

/-! ### Factorizations -/

section Factorizations

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- A factorization into relatively unary proper covariant homeomorphisms,
multiplied on the right by the identity of a proper invariant set. -/
theorem factor_productLeft {B : DefSet (rawMixedSpace (M := M) m b) S}
    (hB : ProperInvariant S B.carrier) {r s : ℕ} {C : DefSet (rawMixedSpace (M := M) n r) S}
    {D : DefSet (rawMixedSpace (M := M) n s) S} {f : Map C D}
    (hF : UnaryFactorization G C D f) :
    UnaryFactorization G (mixedProductDomain C B) (mixedProductDomain D B)
      (mixedDomainProductMap f (Map.id B)) := by
  induction hF with
  | id C =>
    rw [productMap_id]
    exact UnaryFactorization.id _
  | step homeo unary =>
    refine UnaryFactorization.step
      (properCovariantHomeomorphism_product homeo (properCovariantHomeomorphism_id hB)) ?_
    rcases unary with hn | ⟨i, j, h⟩
    · exact unary_of_vf_eq (fun p => productLeft_vf_eq_of_zero B hn _ p)
    · exact Or.inr ⟨_, _, relativelyUnary_productLeft B h⟩
  | comp _ _ ihf ihg =>
    rw [productMap_comp_left]
    exact UnaryFactorization.comp ihf ihg

/-- A factorization multiplied on the left by the identity of a proper
invariant set. -/
theorem factor_productRight {A : DefSet (rawMixedSpace (M := M) n a) S}
    (hA : ProperInvariant S A.carrier) {r s : ℕ} {C : DefSet (rawMixedSpace (M := M) m r) S}
    {D : DefSet (rawMixedSpace (M := M) m s) S} {g : Map C D}
    (hF : UnaryFactorization G C D g) :
    UnaryFactorization G (mixedProductDomain A C) (mixedProductDomain A D)
      (mixedDomainProductMap (Map.id A) g) := by
  induction hF with
  | id C =>
    rw [productMap_id]
    exact UnaryFactorization.id _
  | step homeo unary =>
    refine UnaryFactorization.step
      (properCovariantHomeomorphism_product (properCovariantHomeomorphism_id hA) homeo) ?_
    rcases unary with hm | ⟨i, j, h⟩
    · exact unary_of_vf_eq (fun p => productRight_vf_eq_of_zero A hm _ p)
    · exact Or.inr ⟨_, _, relativelyUnary_productRight A h⟩
  | comp _ _ ihf ihg =>
    rw [productMap_comp_right]
    exact UnaryFactorization.comp ihf ihg

/-- The product of two factorizations, as `(f × id) ∘ (id × g)`. -/
theorem factor_product {r s r' s' : ℕ} {C : DefSet (rawMixedSpace (M := M) n r) S}
    {D : DefSet (rawMixedSpace (M := M) n s) S} {C' : DefSet (rawMixedSpace (M := M) m r') S}
    {D' : DefSet (rawMixedSpace (M := M) m s') S} {f : Map C D} {g : Map C' D'}
    (hC : ProperInvariant S C.carrier) (hD' : ProperInvariant S D'.carrier)
    (hf : UnaryFactorization G C D f) (hg : UnaryFactorization G C' D' g) :
    UnaryFactorization G (mixedProductDomain C C') (mixedProductDomain D D')
      (mixedDomainProductMap f g) := by
  rw [productMap_eq_comp]
  exact UnaryFactorization.comp (factor_productRight hC hg) (factor_productLeft hD' hf)

end Factorizations

/-! ### Products of morphisms -/

section Morphisms

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))

theorem productForm_at (A : VFObject (M := M) S n) (B : VFObject (M := M) S m)
    (p : (VFObject.product hc A B).carrier) :
    gammaMapValue (VFObject.product hc A B).form p =
      gammaMapValue A.form (leftPart (U := A.carrier) (V := B.carrier) p) *
        gammaMapValue B.form (rightPart (U := A.carrier) (V := B.carrier) p) :=
  productForm_value hc A B p.val.1 p.val.2 p.property

/-- The measure identity for a product of morphisms at VF-generic points: the
Jacobian of the product is the product of the Jacobians, and the product forms
divide factorwise. -/
theorem product_generic (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A A' : VFObject (M := M) S n} {B B' : VFObject (M := M) S m}
    (F : Morphism G A A') (H : Morphism G B B') (p : (VFObject.product hc A B).carrier)
    (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
    ∃ L, HasMixedVFDerivativeAt (mixedDomainProductMap F.map H.map) p L ∧
      vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue (VFObject.product hc A B).form p /
          gammaMapValue (VFObject.product hc A' B').form (mixedDomainProductMap F.map H.map p)).val := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  let u : A.carrier := leftPart (U := A.carrier) (V := B.carrier) p
  let w : B.carrier := rightPart (U := A.carrier) (V := B.carrier) p
  have hu : AlgebraicIndependent (vfParameterField S) u.val.1 :=
    hp.comp _ (Fin.castAdd_injective _ _)
  have hw : AlgebraicIndependent (vfParameterField S) w.val.1 :=
    hp.comp _ (Fin.natAdd_injective _ _)
  obtain ⟨L, ⟨Fl, hFl, hL⟩, hdetL⟩ := Morphism.generic hc F u hu
  obtain ⟨K, ⟨Hl, hHl, hK⟩, hdetK⟩ := Morphism.generic hc H w hw
  obtain ⟨D, Dl, hDl, hD⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv
    (mixedDomainProductMap F.map H.map) p hp
  have hJ := has_mixed_vf_jacobian_domain_product F.map H.map u w _ _
    ⟨Fl, hFl, hL.hasJacobianAt⟩ ⟨Hl, hHl, hK.hasJacobianAt⟩
  rw [pack_parts p] at hJ
  have hdet : (LinearMap.toMatrix' D).det =
      (LinearMap.toMatrix' L).det * (LinearMap.toMatrix' K).det :=
    HasMixedVFJacobianAt.unique ⟨Dl, hDl, hD.hasJacobianAt⟩ hJ
  refine ⟨D, ⟨Dl, hDl, hD⟩, ?_⟩
  rw [hdet]
  change Values.vfValueHom (_ * _) = _
  rw [map_mul]
  change vfValue (LinearMap.toMatrix' L).det * vfValue (LinearMap.toMatrix' K).det = _
  rw [hdetL, hdetK, ← Values.gamma_val_mul]
  apply congrArg (fun z : Gamma M => z.val)
  rw [productForm_at hc A B p, productForm_at hc A' B' (mixedDomainProductMap F.map H.map p),
    leftPart_productMap, rightPart_productMap]
  exact (mul_div_mul_comm _ _ _ _).symm

/-- The product of two morphisms underlies a morphism of the products, with the
product map named. -/
theorem Morphism.product_exists (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A A' : VFObject (M := M) S n} {B B' : VFObject (M := M) S m}
    (F : Morphism G A A') (H : Morphism G B B') :
    ∃ K : Morphism G (VFObject.product hc A B) (VFObject.product hc A' B'),
      K.map = mixedDomainProductMap F.map H.map :=
  morphism_of_generic_map (A := VFObject.product hc A B) (B := VFObject.product hc A' B')
    h00 hc hs hsmall (mixedDomainProductMap F.map H.map)
    (mixed_domain_product_map_bijective _ _ F.bijective H.bijective)
    (factor_product A.proper B'.proper F.factor H.factor)
    (product_generic hc h00 hκ hs hsmall hv F H)

/-- (1) A morphism times an identity: the map is `F × id_B`. -/
theorem Morphism.productLeft_exists (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A A' : VFObject (M := M) S n} (F : Morphism G A A') (B : VFObject (M := M) S m) :
    ∃ K : Morphism G (VFObject.product hc A B) (VFObject.product hc A' B),
      K.map = mixedDomainProductMap F.map (Map.id B.carrier) :=
  morphism_of_generic_map (A := VFObject.product hc A B) (B := VFObject.product hc A' B)
    h00 hc hs hsmall (mixedDomainProductMap F.map (Map.id B.carrier))
    (mixed_domain_product_map_bijective _ _ F.bijective (Morphism.id (G := G) B).bijective)
    (factor_productLeft B.proper F.factor)
    (product_generic hc h00 hκ hs hsmall hv F (Morphism.id B))

/-- (2) An identity times a morphism: the map is `id_A × G'`. -/
theorem Morphism.productRight_exists (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : VFObject (M := M) S n) {B B' : VFObject (M := M) S m} (H : Morphism G B B') :
    ∃ K : Morphism G (VFObject.product hc A B) (VFObject.product hc A B'),
      K.map = mixedDomainProductMap (Map.id A.carrier) H.map :=
  morphism_of_generic_map (A := VFObject.product hc A B) (B := VFObject.product hc A B')
    h00 hc hs hsmall (mixedDomainProductMap (Map.id A.carrier) H.map)
    (mixed_domain_product_map_bijective _ _ (Morphism.id (G := G) A).bijective H.bijective)
    (factor_productRight A.proper H.factor)
    (product_generic hc h00 hκ hs hsmall hv (Morphism.id A) H)

/-- (1) `A ≅ A'` in `μVF^◇[n]` via `F` gives `A × B ≅ A' × B`. -/
theorem isomorphic_product_left (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A A' : VFObject (M := M) S n} (F : Morphism G A A') (B : VFObject (M := M) S m) :
    Isomorphic G (VFObject.product hc A B) (VFObject.product hc A' B) := by
  obtain ⟨K, -⟩ := Morphism.productLeft_exists hc h00 hκ hs hsmall hv F B
  exact ⟨K⟩

/-- (2) `B ≅ B'` in `μVF^◇[m]` via `G'` gives `A × B ≅ A × B'`. -/
theorem isomorphic_product_right (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : VFObject (M := M) S n) {B B' : VFObject (M := M) S m} (H : Morphism G B B') :
    Isomorphic G (VFObject.product hc A B) (VFObject.product hc A B') := by
  obtain ⟨K, -⟩ := Morphism.productRight_exists hc h00 hκ hs hsmall hv A H
  exact ⟨K⟩

/-- (3) The isomorphism class of a product depends only on the classes of the
factors: `A × B → A' × B → A' × B'`, composed by `Morphism.comp_nonempty`. -/
theorem isomorphic_product (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A A' : VFObject (M := M) S n} {B B' : VFObject (M := M) S m}
    (hA : Isomorphic G A A') (hB : Isomorphic G B B') :
    Isomorphic G (VFObject.product hc A B) (VFObject.product hc A' B') := by
  obtain ⟨F⟩ := hA
  obtain ⟨H⟩ := hB
  obtain ⟨K₁, -⟩ := Morphism.productLeft_exists hc h00 hκ hs hsmall hv F B
  obtain ⟨K₂, -⟩ := Morphism.productRight_exists hc h00 hκ hs hsmall hv A' H
  exact Morphism.comp_nonempty h00 hc hs hsmall K₁ K₂

end Morphisms

end DiamondIntegral.Section7.DiamondProducts
