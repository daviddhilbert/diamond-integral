import «section 6».DiamondCategory
import «section 6».GammaMapArithmetic
import Section4.MixedProducts

/-! Products in `μVF^◇[*]` (Definition 6.34 objects): `μVF^◇[n] × μVF^◇[m] → μVF^◇[n+m]`.

The carrier is the mixed product (`Fin.append` in the VF and in the RV
coordinates separately) and the form is the product of the two pulled-back
forms. Proper invariance, the uniform form covariance with `t`-definable radii
and finiteness of the RV fibres are inherited coordinatewise. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2 DiamondIntegral.Section6

namespace DiamondIntegral.Section6.DiamondProduct
open DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}

theorem namedRadii_append {t : Fin (r + s) → RVInfinity M} {α : Fin n → Gamma M}
    {β : Fin m → Gamma M} (hα : NamedRadii S (t ∘ Fin.castAdd s) α)
    (hβ : NamedRadii S (t ∘ Fin.natAdd r) β) : NamedRadii S t (Fin.append α β) := by
  intro i
  induction i using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    exact (hα j).mono (Set.union_subset_union_right S (fun z ⟨l, hl⟩ => ⟨Fin.castAdd s l, hl⟩))
  | right j =>
    rw [Fin.append_right]
    exact (hβ j).mono (Set.union_subset_union_right S (fun z ⟨l, hl⟩ => ⟨Fin.natAdd r l, hl⟩))

theorem congruent_left {α : Fin n → Gamma M} {β : Fin m → Gamma M} {x y : Fin (n + m) → VF M}
    (h : Congruent (Fin.append α β) x y) : Congruent α (x ∘ Fin.castAdd m) (y ∘ Fin.castAdd m) :=
  fun j => by
    have hj := h (Fin.castAdd m j)
    rwa [Fin.append_left] at hj

theorem congruent_right {α : Fin n → Gamma M} {β : Fin m → Gamma M} {x y : Fin (n + m) → VF M}
    (h : Congruent (Fin.append α β) x y) : Congruent β (x ∘ Fin.natAdd n) (y ∘ Fin.natAdd n) :=
  fun j => by
    have hj := h (Fin.natAdd n j)
    rwa [Fin.append_right] at hj

theorem product_proper (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S)
    (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier) :
    ProperInvariant S (mixedProductDomain A B).carrier := by
  obtain ⟨γa, hγa⟩ := hA.vfBounded
  obtain ⟨γb, hγb⟩ := hB.vfBounded
  obtain ⟨δa, hδa⟩ := hA.rvBounded
  obtain ⟨δb, hδb⟩ := hB.rvBounded
  refine ⟨(mixedProductDomain A B).definable, ⟨min γa γb, fun p hp i => ?_⟩,
    ⟨max δa δb, fun p hp i => ?_⟩, fun t => ?_⟩
  · have h := (mem_mixedProductDomain A B p).mp hp
    induction i using Fin.addCases with
    | left j => exact le_trans (show (min γa γb).val ≤ γa.val from min_le_left γa γb) (hγa _ h.1 j)
    | right j => exact le_trans (show (min γa γb).val ≤ γb.val from min_le_right γa γb) (hγb _ h.2 j)
  · have h := (mem_mixedProductDomain A B p).mp hp
    induction i using Fin.addCases with
    | left j =>
      have hj := hδa _ h.1 j
      exact ⟨le_trans (show ((max δa δb)⁻¹).val ≤ (δa⁻¹).val from inv_le_inv_iff.mpr (le_max_left δa δb)) hj.1,
        le_trans hj.2 (show δa.val ≤ (max δa δb).val from le_max_left δa δb)⟩
    | right j =>
      have hj := hδb _ h.2 j
      exact ⟨le_trans (show ((max δa δb)⁻¹).val ≤ (δb⁻¹).val from inv_le_inv_iff.mpr (le_max_right δa δb)) hj.1,
        le_trans hj.2 (show δb.val ≤ (max δa δb).val from le_max_right δa δb)⟩
  · obtain ⟨α, hαn, hα⟩ := hA.radii (t ∘ Fin.castAdd s)
    obtain ⟨β, hβn, hβ⟩ := hB.radii (t ∘ Fin.natAdd r)
    refine ⟨Fin.append α β, namedRadii_append hαn hβn, fun x y hxy => ?_⟩
    have hxy' : Congruent (Fin.append α β) x y := hxy
    change (x, t) ∈ (mixedProductDomain A B).carrier ↔ (y, t) ∈ (mixedProductDomain A B).carrier
    rw [mem_mixedProductDomain, mem_mixedProductDomain]
    exact and_congr (hα _ _ (congruent_left hxy')) (hβ _ _ (congruent_right hxy'))

omit [M ⊨ Axioms.ACVF] in
theorem unpack_val (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) (a : mixedProductDomain A B) :
    (mixedUnpack A B a).val = ((a.val.1 ∘ Fin.castAdd m, a.val.2 ∘ Fin.castAdd s),
      (a.val.1 ∘ Fin.natAdd n, a.val.2 ∘ Fin.natAdd r)) := by
  have h := congrArg Subtype.val (mixedPack_unpack A B a)
  change (vfAppend (mixedUnpack A B a).val.1.1 (mixedUnpack A B a).val.2.1,
    rvAppend (mixedUnpack A B a).val.1.2 (mixedUnpack A B a).val.2.2) = a.val at h
  rw [← h]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> funext j <;>
    simp [vfAppend, rvAppend, Fin.append_left, Fin.append_right]

variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- The product form: the product of the two pulled-back forms. -/
def productForm (A : VFObject (M := M) S n) (B : VFObject (M := M) S m) :
    Map (mixedProductDomain A.carrier B.carrier) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  gammaMapMul hc (A.form.comp ((Map.prodFst A.carrier B.carrier).comp (mixedUnpack A.carrier B.carrier)))
    (B.form.comp ((Map.prodSnd A.carrier B.carrier).comp (mixedUnpack A.carrier B.carrier)))

theorem productForm_value (A : VFObject (M := M) S n) (B : VFObject (M := M) S m)
    (x : Fin (n + m) → VF M) (t : Fin (A.labels + B.labels) → RVInfinity M)
    (hx : (x, t) ∈ (mixedProductDomain A.carrier B.carrier).carrier) :
    gammaMapValue (productForm hc A B) ⟨(x, t), hx⟩ =
      gammaMapValue A.form ⟨(x ∘ Fin.castAdd m, t ∘ Fin.castAdd B.labels),
          ((mem_mixedProductDomain A.carrier B.carrier (x, t)).mp hx).1⟩ *
        gammaMapValue B.form ⟨(x ∘ Fin.natAdd n, t ∘ Fin.natAdd A.labels),
          ((mem_mixedProductDomain A.carrier B.carrier (x, t)).mp hx).2⟩ := by
  have hu := unpack_val A.carrier B.carrier ⟨(x, t), hx⟩
  have eA : (Map.prodFst A.carrier B.carrier) (mixedUnpack A.carrier B.carrier ⟨(x, t), hx⟩) =
      ⟨(x ∘ Fin.castAdd m, t ∘ Fin.castAdd B.labels),
        ((mem_mixedProductDomain A.carrier B.carrier (x, t)).mp hx).1⟩ :=
    Subtype.ext (congrArg Prod.fst hu)
  have eB : (Map.prodSnd A.carrier B.carrier) (mixedUnpack A.carrier B.carrier ⟨(x, t), hx⟩) =
      ⟨(x ∘ Fin.natAdd n, t ∘ Fin.natAdd A.labels),
        ((mem_mixedProductDomain A.carrier B.carrier (x, t)).mp hx).2⟩ :=
    Subtype.ext (congrArg Prod.snd hu)
  change gammaMapValue A.form ((Map.prodFst A.carrier B.carrier)
      (mixedUnpack A.carrier B.carrier ⟨(x, t), hx⟩)) *
    gammaMapValue B.form ((Map.prodSnd A.carrier B.carrier)
      (mixedUnpack A.carrier B.carrier ⟨(x, t), hx⟩)) = _
  rw [eA, eB]

theorem product_covariant (A : VFObject (M := M) S n) (B : VFObject (M := M) S m)
    (t : Fin (A.labels + B.labels) → RVInfinity M) :
    ∃ α : Fin (n + m) → Gamma M, NamedRadii S t α ∧
      ∀ x y (hx : (x, t) ∈ (mixedProductDomain A.carrier B.carrier).carrier)
        (hy : (y, t) ∈ (mixedProductDomain A.carrier B.carrier).carrier), Congruent α x y →
        gammaMapValue (productForm hc A B) ⟨(x, t), hx⟩ =
          gammaMapValue (productForm hc A B) ⟨(y, t), hy⟩ := by
  obtain ⟨α, hαn, hα⟩ := A.formCovariant (t ∘ Fin.castAdd B.labels)
  obtain ⟨β, hβn, hβ⟩ := B.formCovariant (t ∘ Fin.natAdd A.labels)
  refine ⟨Fin.append α β, namedRadii_append hαn hβn, fun x y hx hy hxy => ?_⟩
  rw [productForm_value, productForm_value]
  rw [hα _ _ _ _ (congruent_left hxy), hβ _ _ _ _ (congruent_right hxy)]

theorem product_finite (A : VFObject (M := M) S n) (B : VFObject (M := M) S m)
    (x : Fin (n + m) → VF M) :
    {t | (x, t) ∈ (mixedProductDomain A.carrier B.carrier).carrier}.Finite := by
  apply (((A.finiteRV (x ∘ Fin.castAdd m)).prod (B.finiteRV (x ∘ Fin.natAdd n))).image
    (fun ts => Fin.append ts.1 ts.2)).subset
  intro t ht
  have hab := (mem_mixedProductDomain A.carrier B.carrier (x, t)).mp ht
  exact ⟨(t ∘ Fin.castAdd B.labels, t ∘ Fin.natAdd A.labels), hab, Fin.append_castAdd_natAdd⟩

/-- The product of two objects of `μVF^◇`. -/
def VFObject.product (A : VFObject (M := M) S n) (B : VFObject (M := M) S m) :
    VFObject (M := M) S (n + m) where
  labels := A.labels + B.labels
  carrier := mixedProductDomain A.carrier B.carrier
  form := productForm hc A B
  proper := product_proper A.carrier B.carrier A.proper B.proper
  formCovariant := product_covariant hc A B
  finiteRV := product_finite A B

end DiamondIntegral.Section6.DiamondProduct
