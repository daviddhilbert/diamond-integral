import «section 7».Lemma714Induct

/-! Lemma 7.14, part 39: the first stage with the base coordinates pulled back.

For prepared contraction data `D` on `A ⊆ VF^{m+2}`, the first stage `st` of
`D.C` moves the base coordinates `init(prep p)` of a point away from `init p`
by the label-determined translation of `prep`. The map

  `g p = (snoc (init p) (last (st.lift (prep p))), labels of st.lift (prep p))`

fixes the base coordinates (`g_fix`) and is a proper covariant homeomorphism
onto its image `Xt` (`g_homeo`), with unit derivative off the preimage of the
exceptional set of the stage (`g_unit`). It differs from `st.lift ∘ prep` by a
label translation `U` (`g_eq`). The form `formX` on `Xt` reads the form of the
pulled-back first-stage set at `(init, labels)` (`formX_g`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FiberwiseInput

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### The code map `((x, u), (z, w)) ↦ (snoc (init x) (last z), w)` -/

section SnocLabels
variable {S : Set M} {m r a : ℕ}

def slPoint (x : Mixed M (m + 1) r × Mixed M (m + 1) a) : Mixed M (m + 1) a :=
  (Fin.snoc (α := fun _ => VF M) (Fin.init x.1.1) (x.2.1 (Fin.last m)), x.2.2)

def slCodes (z : (Fin (m + 1) ⊕ Fin r) ⊕ (Fin (m + 1) ⊕ Fin a) → M) : Fin (m + 1) ⊕ Fin a → M :=
  Sum.elim (Fin.snoc (α := fun _ => M) (fun i => z (.inl (.inl i.castSucc))) (z (.inr (.inl (Fin.last m)))))
    (fun j => z (.inr (.inr j)))

omit hM in
theorem mixedValues_sl (x : Mixed M (m + 1) r × Mixed M (m + 1) a) :
    mixedValues (slPoint x) = slCodes (Sum.elim (mixedValues x.1) (mixedValues x.2)) := by
  funext i
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [slPoint, slCodes, mixedValues, vfValues]
    · simp only [slPoint, slCodes, mixedValues, Sum.elim_inl, Fin.snoc_castSucc]
      change ((Fin.snoc (α := fun _ => VF M) (Fin.init x.1.1) (x.2.1 (Fin.last m)) j.castSucc : VF M)).val =
        (x.1.1 j.castSucc).val
      rw [Fin.snoc_castSucc]
      rfl
  · rfl

/-- The code map `((x, u), (z, w)) ↦ (snoc (init x) (last z), w)`. -/
def snocLabels (C : DefSet ((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)) S) :
    Map C (DefSet.univ (rawMixedSpace (M := M) (m + 1) a) S) := by
  have hc : ∀ c : ((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)).domain,
      (slCodes c.val : Fin (m + 1) ⊕ Fin a → M) =
        mixedValues (slPoint (((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)).decode c)) := by
    intro c
    rw [mixedValues_sl]
    apply congrArg slCodes
    funext i
    rcases i with i | i
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inl, c.property.1⟩ : (rawMixedSpace (M := M) (m + 1) r).domain)) i).symm
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inr, c.property.2⟩ : (rawMixedSpace (M := M) (m + 1) a).domain)) i).symm
  refine Map.ofCodes C slPoint slCodes ?_ ?_ ?_
  · rintro (i | i)
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [slCodes, Sum.elim_inl, Fin.snoc_last]
        exact Set.DefinableFun.proj LRV
      · simp only [slCodes, Sum.elim_inl, Fin.snoc_castSucc]
        exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  · intro c
    rw [hc c]
    exact mixedValues_mem_domain _
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode _).trans (hc c)

@[simp] theorem snocLabels_apply
    (C : DefSet ((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)) S) (x : C) :
    (snocLabels C x).val = slPoint x.val := rfl

end SnocLabels

/-! ### Inverses of label translations -/

section TranslInverse
variable {S : Set M} {m q : ℕ} {X Y : DefSet (rawMixedSpace (M := M) m q) S} (f : Map X Y)
  (hf : Function.Bijective f) (hlab : ∀ p : X, (f p).val.2 = p.val.2)
  (htr : ∀ p p' : X, p.val.2 = p'.val.2 → trAt f p = trAt f p')

include hlab in
theorem transl_inv_labels (y : Y) : ((f.inverse hf) y).val.2 = y.val.2 := by
  have h := hlab ((f.inverse hf) y)
  rw [Map.apply_inverse] at h
  exact h.symm

include hlab htr in
theorem transl_inv_transl (y y' : Y) (h : y.val.2 = y'.val.2) :
    trAt (f.inverse hf) y = trAt (f.inverse hf) y' := by
  have hy : ∀ z : Y, trAt (f.inverse hf) z = -trAt f ((f.inverse hf) z) := by
    intro z
    funext i
    have h1 : (f ((f.inverse hf) z)).val.1 i = z.val.1 i := by rw [Map.apply_inverse]
    change ((f.inverse hf) z).val.1 i - z.val.1 i = -((f ((f.inverse hf) z)).val.1 i - ((f.inverse hf) z).val.1 i)
    rw [h1]
    abel
  rw [hy, hy]
  congr 1
  exact htr _ _ ((transl_inv_labels f hf hlab y).trans (h.trans (transl_inv_labels f hf hlab y').symm))

end TranslInverse

/-! ### The map `g` -/

section GMap
variable {T : LRV.Substructure M} {m r : ℕ} {A : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} (D : PrepContr (G := G) A ω)

namespace PrepContr

/-- The map `p ↦ (snoc (init p) (last (st.lift (prep p))), labels)`. -/
def gmap : Map A (DefSet.univ (rawMixedSpace (M := M) (m + 1 + 1) D.st.arity) (T : Set M)) :=
  (snocLabels _).comp ((Map.id A).pair (D.st.lift.comp D.prep))

/-- The image of `g`. -/
abbrev Xt : DefSet (rawMixedSpace (M := M) (m + 1 + 1) D.st.arity) (T : Set M) := D.gmap.image

/-- **The map `g : A → Xt`.** -/
abbrev g : Map A D.Xt := D.gmap.toImage

theorem g_val (p : A) :
    (D.g p).val = (Fin.snoc (α := fun _ => VF M) (Fin.init p.val.1) ((D.st.lift (D.prep p)).val.1 (Fin.last (m + 1))),
      (D.st.lift (D.prep p)).val.2) := rfl

theorem g_fix (p : A) : Fin.init (D.g p).val.1 = Fin.init p.val.1 := by
  rw [g_val]
  exact Fin.init_snoc _ _

theorem lift_init (p : A) :
    Fin.init (D.st.lift (D.prep p)).val.1 = Fin.init p.val.1 + Fin.init (trAt D.prep p) := by
  rw [← prep_init]
  funext i
  exact D.st.relative (D.prep p) i

theorem lift_eq (p : A) :
    (D.st.lift (D.prep p)).val = (Fin.snoc (α := fun _ => VF M) (Fin.init p.val.1 + Fin.init (trAt D.prep p))
      ((D.st.lift (D.prep p)).val.1 (Fin.last (m + 1))), (D.st.lift (D.prep p)).val.2) := by
  refine Prod.ext ?_ rfl
  rw [← lift_init, Fin.snoc_init_self]

theorem g_injective : Function.Injective D.g := by
  intro p p' he
  have hv := congrArg Subtype.val he
  rw [g_val, g_val] at hv
  obtain ⟨h1, h2⟩ := Prod.mk.inj hv
  have hi : Fin.init p.val.1 = Fin.init p'.val.1 := by
    have := congrArg Fin.init h1
    simpa only [Fin.init_snoc] using this
  have hl : (D.st.lift (D.prep p)).val.1 (Fin.last (m + 1)) = (D.st.lift (D.prep p')).val.1 (Fin.last (m + 1)) := by
    have := congrFun h1 (Fin.last (m + 1))
    simpa only [Fin.snoc_last] using this
  have heq : D.st.lift (D.prep p) = D.st.lift (D.prep p') := by
    apply Subtype.ext
    refine Prod.ext ?_ h2
    funext i
    refine Fin.lastCases hl (fun j => ?_) i
    have e1 := congrFun (D.lift_init p) j
    have e2 := congrFun (D.lift_init p') j
    change (Fin.init (D.st.lift (D.prep p)).val.1) j = (Fin.init (D.st.lift (D.prep p')).val.1) j
    rw [e1, e2, hi, trAt_eq_of_lift D h2]
  exact D.homeo.bijective.1 (D.st.home.bijective.1 heq)

theorem g_bijective : Function.Bijective D.g :=
  ⟨D.g_injective, by rintro ⟨_, p, rfl⟩; exact ⟨p, rfl⟩⟩

theorem liftPrep_bijective : Function.Bijective (D.st.lift.comp D.prep) :=
  D.st.home.bijective.comp D.homeo.bijective

/-- The label translation `U : st.target → Xt` with `U ∘ st.lift ∘ prep = g`. -/
def U : Map D.st.target D.Xt := D.g.comp ((D.st.lift.comp D.prep).inverse D.liftPrep_bijective)

theorem U_liftPrep (p : A) : D.U (D.st.lift (D.prep p)) = D.g p := by
  change D.g ((D.st.lift.comp D.prep).inverse D.liftPrep_bijective ((D.st.lift.comp D.prep) p)) = D.g p
  rw [Map.inverse_apply]

theorem g_eq : D.g = D.U.comp (D.st.lift.comp D.prep) := by
  apply Map.ext
  intro p
  exact (D.U_liftPrep p).symm

theorem U_bijective : Function.Bijective D.U := by
  constructor
  · intro z z' he
    obtain ⟨p, rfl⟩ := D.liftPrep_bijective.2 z
    obtain ⟨p', rfl⟩ := D.liftPrep_bijective.2 z'
    change D.U (D.st.lift (D.prep p)) = D.U (D.st.lift (D.prep p')) at he
    rw [U_liftPrep, U_liftPrep] at he
    rw [D.g_injective he]
  · intro x
    obtain ⟨p, rfl⟩ := D.g_bijective.2 x
    exact ⟨D.st.lift (D.prep p), D.U_liftPrep p⟩

theorem U_labels (z : D.st.target) : (D.U z).val.2 = z.val.2 := by
  obtain ⟨p, rfl⟩ := D.liftPrep_bijective.2 z
  change (D.U (D.st.lift (D.prep p))).val.2 = _
  rw [U_liftPrep, g_val]
  rfl

theorem U_trAt (p : A) :
    trAt D.U (D.st.lift (D.prep p)) = Fin.snoc (α := fun _ => VF M) (-Fin.init (trAt D.prep p)) 0 := by
  funext i
  change (D.U (D.st.lift (D.prep p))).val.1 i - (D.st.lift (D.prep p)).val.1 i = _
  rw [U_liftPrep, g_val]
  conv_lhs => rw [lift_eq]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, sub_self]
  · simp only [Fin.snoc_castSucc, Pi.add_apply, Pi.neg_apply]
    abel

theorem U_transl (z z' : D.st.target) (h : z.val.2 = z'.val.2) : trAt D.U z = trAt D.U z' := by
  obtain ⟨p, rfl⟩ := D.liftPrep_bijective.2 z
  obtain ⟨p', rfl⟩ := D.liftPrep_bijective.2 z'
  change trAt D.U (D.st.lift (D.prep p)) = trAt D.U (D.st.lift (D.prep p'))
  rw [U_trAt, U_trAt, trAt_eq_of_lift D h]

theorem Xt_vfBounded (hA : VFBounded A.carrier) : VFBounded D.Xt.carrier := by
  obtain ⟨γ, hγ⟩ := hA
  obtain ⟨δ, hδ⟩ := D.st.proper.vfBounded
  refine ⟨min γ δ, ?_⟩
  rintro _ ⟨p, rfl⟩ i
  change (min γ δ).val ≤ vfValue ((D.g p).val.1 i)
  rw [g_val]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact le_trans (show (min γ δ).val ≤ δ.val from min_le_right γ δ) (hδ _ (D.st.lift (D.prep p)).property _)
  · simp only [Fin.snoc_castSucc]
    exact le_trans (show (min γ δ).val ≤ γ.val from min_le_left γ δ) (hγ p.val p.property j.castSucc)

theorem Xt_proper (hA : VFBounded A.carrier) : ProperInvariant (T : Set M) D.Xt.carrier :=
  properInvariant_of_transl (D.U.inverse D.U_bijective)
    (DiamondGroupoid.inverse_bijective D.U D.U_bijective)
    (transl_inv_labels D.U D.U_bijective D.U_labels)
    (transl_inv_transl D.U D.U_bijective D.U_labels D.U_transl) D.st.proper (D.Xt_vfBounded hA)

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include h00 hc hκ hs hv hsmall hΓ in
theorem U_homeo (hA : VFBounded A.carrier) : ProperCovariantHomeomorphism (G := G) D.U :=
  transl_homeo D.U D.U_labels D.U_transl h00 hc hκ hs hv hsmall hΓ D.st.proper (D.Xt_proper hA) D.U_bijective

include h00 hc hκ hs hv hsmall hΓ in
/-- **`g` is a proper covariant homeomorphism.** -/
theorem g_homeo (hA : VFBounded A.carrier) : ProperCovariantHomeomorphism (G := G) D.g := by
  rw [g_eq]
  exact lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ (lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ D.homeo D.st.home)
    (D.U_homeo h00 hc hκ hs hv hsmall hΓ hA)

include hv in
/-- **`g` has unit derivative off the preimage of the exceptional set.** -/
theorem g_unit (hA : VFBounded A.carrier) (p : A) (hp : (D.prep p).val ∉ D.st.exceptional.carrier) :
    HasMixedUnitDerivativeAt D.g p := by
  have h := HasMixedUnitDerivativeAt.comp (f := D.st.lift.comp D.prep) (p := p)
    (transl_unit D.U D.U_labels D.U_transl hv D.st.proper (D.st.lift (D.prep p)))
    ((D.st.unitDerivative (D.prep p) hp).comp (D.unit p))
  rw [g_eq]
  exact h

end PrepContr

end GMap

end DiamondIntegral.Section7.Lemma714Reduce
