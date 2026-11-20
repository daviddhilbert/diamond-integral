import «section 7».Lemma714Prod

/-! Lemma 7.14, part 20: geometry of `g ⋉ A`.

For a proper covariant homeomorphism `g : P → Q` (`P ⊆ VF`) and a proper
invariant `A ⊆ VF × RV^r` over `P`, the map `g ⋉ A` has the graph fibres of `g`
cut by the fibres of `A` (`prodMap_graphFibre`). Its source fibres are open,
its fibre maps continuous, and its range fibres are clopen: they are preimages
of the clopen fibres of `A` under the continuous inverse fibre maps of `g`
(`prodMap_range_isClopen`). Hence:

* its image is proper invariant (`prodMap_image_properInvariant`), with radii
  named by the clopen criterion;
* it is a proper covariant homeomorphism onto its image (`prodMap_properHomeomorphism`,
  by Lemmas 6.7 and 6.8).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Prod
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {P : DefSet (rawMixedSpace (M := M) 1 0) S} {Q : DefSet (rawMixedSpace (M := M) 1 s) S}
  (g : Map P Q) {A : DefSet (rawMixedSpace (M := M) 1 r) S}
  (hAP : ∀ p ∈ A.carrier, basePoint p ∈ P.carrier)

omit hM in
theorem tags_split (v : Fin (s + r) → RVInfinity M) :
    v = Fin.append (fun j => v (Fin.castAdd r j)) (fun j => v (Fin.natAdd s j)) :=
  (Fin.append_castAdd_natAdd).symm

/-! ### Graph fibres -/

theorem prodMap_graphFibre (u : Fin r → RVInfinity M) (w : Fin s → RVInfinity M) (u' : Fin r → RVInfinity M)
    (a b : Fin 1 → VF M) :
    graphFibre (prodMap g hAP) u (Fin.append w u') a b ↔
      (a, u) ∈ A.carrier ∧ u' = u ∧ graphFibre g Fin.elim0 w a b := by
  constructor
  · rintro ⟨p, hp, hfp⟩
    rw [prodMap_apply] at hfp
    have h1 := congrArg Prod.fst hfp
    have h2 := congrArg Prod.snd hfp
    have hw : (g (baseMap hAP p)).val.2 = w := by
      funext j
      have := congrFun h2 (Fin.castAdd r j)
      simpa only [Fin.append_left] using this
    have hu : p.val.2 = u' := by
      funext j
      have := congrFun h2 (Fin.natAdd s j)
      simpa only [Fin.append_right] using this
    have hpa : p.val.1 = a := congrArg Prod.fst hp
    have hpu : p.val.2 = u := congrArg Prod.snd hp
    refine ⟨hp ▸ p.property, hu.symm.trans hpu, baseMap hAP p, ?_, Prod.ext h1 hw⟩
    rw [baseMap_apply]
    exact Prod.ext hpa (Subsingleton.elim _ _)
  · rintro ⟨hA, rfl, q, hq, hgq⟩
    refine ⟨⟨(a, u'), hA⟩, rfl, ?_⟩
    have hbq : baseMap hAP ⟨(a, u'), hA⟩ = q := by
      apply Subtype.ext
      rw [baseMap_apply, hq]
      exact Prod.ext rfl (Subsingleton.elim _ _)
    rw [prodMap_apply, hbq, hgq]

theorem prodMap_toImage_graphFibre (u : Fin r → RVInfinity M) (v : Fin (s + r) → RVInfinity M) (a b : Fin 1 → VF M) :
    graphFibre (prodMap g hAP).toImage u v a b ↔ graphFibre (prodMap g hAP) u v a b := Iff.rfl

theorem prodMap_source (u : Fin r → RVInfinity M) (w : Fin s → RVInfinity M) (u' : Fin r → RVInfinity M) :
    graphFibreSource (prodMap g hAP) u (Fin.append w u') =
      {a | (a, u) ∈ A.carrier ∧ u' = u ∧ a ∈ graphFibreSource g Fin.elim0 w} := by
  ext a
  simp only [graphFibreSource, Set.mem_setOf_eq, prodMap_graphFibre]
  exact ⟨fun ⟨b, h1, h2, h3⟩ => ⟨h1, h2, b, h3⟩, fun ⟨h1, h2, b, h3⟩ => ⟨b, h1, h2, h3⟩⟩

theorem prodMap_range (u : Fin r → RVInfinity M) (w : Fin s → RVInfinity M) (u' : Fin r → RVInfinity M) :
    graphFibreRange (prodMap g hAP) u (Fin.append w u') =
      {b | ∃ a, (a, u) ∈ A.carrier ∧ u' = u ∧ graphFibre g Fin.elim0 w a b} := by
  ext b
  simp only [graphFibreRange, Set.mem_setOf_eq, prodMap_graphFibre]
  exact Iff.rfl

theorem prodMap_fibreMap_eq (u : Fin r → RVInfinity M) (w : Fin s → RVInfinity M) (u' : Fin r → RVInfinity M)
    {a : Fin 1 → VF M} (ha : a ∈ graphFibreSource (prodMap g hAP) u (Fin.append w u')) :
    graphFibreMap (prodMap g hAP) u (Fin.append w u') a = graphFibreMap g Fin.elim0 w a := by
  have h1 := graphFibreMap_graph (prodMap g hAP) u (Fin.append w u') ha
  obtain ⟨-, -, h2⟩ := (prodMap_graphFibre g hAP u w u' a _).mp h1
  have hsrc : a ∈ graphFibreSource g Fin.elim0 w := ⟨_, h2⟩
  exact graphFibre_functional g Fin.elim0 w h2 (graphFibreMap_graph g Fin.elim0 w hsrc)

/-- Graph fibres of the inverse are the swapped graph fibres. -/
theorem inverse_graphFibre {n m r' s' : ℕ} {X : DefSet (rawMixedSpace (M := M) n r') S}
    {Y : DefSet (rawMixedSpace (M := M) m s') S} (f : Map X Y) (hf : Function.Bijective f)
    (u : Fin r' → RVInfinity M) (v : Fin s' → RVInfinity M) (a : Fin n → VF M) (b : Fin m → VF M) :
    graphFibre (f.inverse hf) v u b a ↔ graphFibre f u v a b := by
  constructor
  · rintro ⟨q, hq, hfq⟩
    refine ⟨f.inverse hf q, hfq, ?_⟩
    rw [Map.apply_inverse]
    exact hq
  · rintro ⟨p, hp, hfp⟩
    refine ⟨f p, hfp, ?_⟩
    rw [Map.inverse_apply]
    exact hp

/-! ### Topology of the fibres -/

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hv in
theorem source_isOpen_of_covariant {n m r' s' : ℕ} {X : DefSet (rawMixedSpace (M := M) n r') S}
    {Y : DefSet (rawMixedSpace (M := M) m s') S} {f : Map X Y} (hf : ProperCovariant f)
    (u : Fin r' → RVInfinity M) (v : Fin s' → RVInfinity M) : IsClopen (graphFibreSource f u v) := by
  obtain ⟨α, β, -, -, hα, -, -⟩ := hf.radii u v
  exact hα.isClopen hv

include hv in
theorem range_isClopen_of_covariant {n m r' s' : ℕ} {X : DefSet (rawMixedSpace (M := M) n r') S}
    {Y : DefSet (rawMixedSpace (M := M) m s') S} {f : Map X Y} (hf : ProperCovariant f)
    (u : Fin r' → RVInfinity M) (v : Fin s' → RVInfinity M) : IsClopen (graphFibreRange f u v) := by
  obtain ⟨α, β, -, -, -, hβ, -⟩ := hf.radii u v
  exact hβ.isClopen hv

include hv in
/-- **The range fibres of `g ⋉ A` are clopen.** -/
theorem prodMap_range_isClopen (hg : ProperCovariantHomeomorphism (G := G) g) (hA : ProperInvariant S A.carrier)
    (u : Fin r → RVInfinity M) (t : Fin (s + r) → RVInfinity M) :
    IsClopen (graphFibreRange (prodMap g hAP) u t) := by
  rw [tags_split t, prodMap_range]
  set w : Fin s → RVInfinity M := fun j => t (Fin.castAdd r j)
  set u' : Fin r → RVInfinity M := fun j => t (Fin.natAdd s j)
  by_cases hu : u' = u
  · let ψ := graphFibreMap (g.inverse hg.bijective) w Fin.elim0
    have hψ : ContinuousOn ψ (graphFibreRange g Fin.elim0 w) := by
      have h := hg.inverseContinuous w Fin.elim0
      have hsrc : graphFibreSource (g.inverse hg.bijective) w Fin.elim0 = graphFibreRange g Fin.elim0 w := by
        ext b
        simp only [graphFibreSource, graphFibreRange, Set.mem_setOf_eq, inverse_graphFibre]
      rwa [hsrc] at h
    have heq : {b | ∃ a, (a, u) ∈ A.carrier ∧ u' = u ∧ graphFibre g Fin.elim0 w a b} =
        graphFibreRange g Fin.elim0 w ∩ ψ ⁻¹' vfFibre A.carrier u := by
      ext b
      constructor
      · rintro ⟨a, ha, -, hab⟩
        refine ⟨⟨a, hab⟩, ?_⟩
        have hinv : graphFibre (g.inverse hg.bijective) w Fin.elim0 b a := (inverse_graphFibre g hg.bijective _ _ a b).mpr hab
        have hsrc : b ∈ graphFibreSource (g.inverse hg.bijective) w Fin.elim0 := ⟨a, hinv⟩
        have hψb : ψ b = a := graphFibre_functional _ _ _ (graphFibreMap_graph _ _ _ hsrc) hinv
        show ψ b ∈ vfFibre A.carrier u
        rw [hψb]
        exact ha
      · rintro ⟨⟨a, hab⟩, hb⟩
        have hinv : graphFibre (g.inverse hg.bijective) w Fin.elim0 b a := (inverse_graphFibre g hg.bijective _ _ a b).mpr hab
        have hsrc : b ∈ graphFibreSource (g.inverse hg.bijective) w Fin.elim0 := ⟨a, hinv⟩
        have hψb : ψ b = a := graphFibre_functional _ _ _ (graphFibreMap_graph _ _ _ hsrc) hinv
        refine ⟨a, ?_, hu, hab⟩
        have h' : ψ b ∈ vfFibre A.carrier u := hb
        rw [hψb] at h'
        exact h'
    rw [heq]
    have hR := range_isClopen_of_covariant hv hg.covariant Fin.elim0 w
    have hV := hA.clopen_fibres hv u
    exact ⟨hψ.preimage_isClosed_of_isClosed hR.isClosed hV.isClosed, hψ.isOpen_inter_preimage hR.isOpen hV.isOpen⟩
  · have : {b | ∃ a, (a, u) ∈ A.carrier ∧ u' = u ∧ graphFibre g Fin.elim0 w a b} = ∅ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a, -, h, -⟩
      exact hu h
    rw [this]
    exact isClopen_empty

include hv in
theorem prodMap_source_isOpen (hg : ProperCovariantHomeomorphism (G := G) g) (hA : ProperInvariant S A.carrier)
    (u : Fin r → RVInfinity M) (t : Fin (s + r) → RVInfinity M) :
    IsOpen (graphFibreSource (prodMap g hAP) u t) := by
  rw [tags_split t, prodMap_source]
  set w : Fin s → RVInfinity M := fun j => t (Fin.castAdd r j)
  set u' : Fin r → RVInfinity M := fun j => t (Fin.natAdd s j)
  by_cases hu : u' = u
  · have heq : {a | (a, u) ∈ A.carrier ∧ u' = u ∧ a ∈ graphFibreSource g Fin.elim0 w} =
        vfFibre A.carrier u ∩ graphFibreSource g Fin.elim0 w := by
      ext a
      exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hu, h3⟩⟩
    rw [heq]
    exact (hA.clopen_fibres hv u).isOpen.inter (source_isOpen_of_covariant hv hg.covariant Fin.elim0 w).isOpen
  · have : {a | (a, u) ∈ A.carrier ∧ u' = u ∧ a ∈ graphFibreSource g Fin.elim0 w} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, h, -⟩
      exact hu h
    rw [this]
    exact isOpen_empty

theorem prodMap_continuous (hg : ProperCovariantHomeomorphism (G := G) g) :
    ContinuousOnGraphFibres (G := G) (prodMap g hAP).toImage := by
  intro u t
  change ContinuousOn (graphFibreMap (prodMap g hAP) u t) (graphFibreSource (prodMap g hAP) u t)
  rw [tags_split t]
  set w : Fin s → RVInfinity M := fun j => t (Fin.castAdd r j)
  set u' : Fin r → RVInfinity M := fun j => t (Fin.natAdd s j)
  have hsub : graphFibreSource (prodMap g hAP) u (Fin.append w u') ⊆ graphFibreSource g Fin.elim0 w := by
    rw [prodMap_source]
    exact fun a ha => ha.2.2
  exact ((hg.continuous Fin.elim0 w).mono hsub).congr (fun a ha => prodMap_fibreMap_eq g hAP u w u' ha)

/-! ### The image and the homeomorphism -/

theorem prodMap_vfFibre_image (t : Fin (s + r) → RVInfinity M) :
    vfFibre (prodMap g hAP).image.carrier t = graphFibreRange (prodMap g hAP) (fun j => t (Fin.natAdd s j)) t := by
  ext b
  constructor
  · rintro ⟨p, hp⟩
    have hu : p.val.2 = fun j => t (Fin.natAdd s j) := by
      funext j
      rw [← prodMap_labels g hAP p j]
      exact congrFun (congrArg Prod.snd hp) (Fin.natAdd s j)
    exact ⟨p.val.1, p, Prod.ext rfl hu, hp⟩
  · rintro ⟨a, p, -, hp⟩
    exact ⟨p, hp⟩

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)

include h00 hc hκ hs hv in
/-- **The image of `g ⋉ A` is proper invariant.** -/
theorem prodMap_image_properInvariant (hg : ProperCovariantHomeomorphism (G := G) g)
    (hA : ProperInvariant S A.carrier) : ProperInvariant S (prodMap g hAP).image.carrier := by
  obtain ⟨γ₁, hγ₁⟩ := hg.covariant.imageVFBounded
  obtain ⟨δ₁, hδ₁⟩ := hg.covariant.imageRVBounded
  obtain ⟨δ₂, hδ₂⟩ := hA.rvBounded
  refine ⟨(prodMap g hAP).image.definable, ⟨γ₁, ?_⟩, ⟨max δ₁ δ₂, ?_⟩, fun t => ?_⟩
  · rintro _ ⟨p, rfl⟩ i
    exact hγ₁ _ ⟨baseMap hAP p, rfl⟩ i
  · rintro _ ⟨p, rfl⟩ i
    have h1 : ((max δ₁ δ₂)⁻¹).val ≤ (δ₁⁻¹).val := show (max δ₁ δ₂)⁻¹ ≤ δ₁⁻¹ from inv_le_inv' (le_max_left _ _)
    have h2 : ((max δ₁ δ₂)⁻¹).val ≤ (δ₂⁻¹).val := show (max δ₁ δ₂)⁻¹ ≤ δ₂⁻¹ from inv_le_inv' (le_max_right _ _)
    have h3 : δ₁.val ≤ (max δ₁ δ₂).val := show δ₁ ≤ max δ₁ δ₂ from le_max_left _ _
    have h4 : δ₂.val ≤ (max δ₁ δ₂).val := show δ₂ ≤ max δ₁ δ₂ from le_max_right _ _
    dsimp only
    rw [prodMap_apply]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · simp only [Fin.append_left]
      obtain ⟨hl, hu⟩ := hδ₁ _ ⟨baseMap hAP p, rfl⟩ l
      exact ⟨h1.trans hl, hu.trans h3⟩
    · simp only [Fin.append_right]
      obtain ⟨hl, hu⟩ := hδ₂ _ p.property l
      exact ⟨h2.trans hl, hu.trans h4⟩
  · rw [prodMap_vfFibre_image]
    have hcl := prodMap_range_isClopen g hAP hv hg hA (fun j => t (Fin.natAdd s j)) t
    have hdef := graphFibreRange_definable (prodMap g hAP) (fun j => t (Fin.natAdd s j)) t
    have hsub : graphFibreBase S (fun j => t (Fin.natAdd s j)) t ⊆ S ∪ Set.range (rvValues t) := by
      rintro x ((hx | ⟨j, rfl⟩) | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨Fin.natAdd s j, rfl⟩
      · exact Or.inr hx
    have hbd : ∃ γ : Gamma M, ∀ x ∈ graphFibreRange (prodMap g hAP) (fun j => t (Fin.natAdd s j)) t, ∀ i,
        γ.val ≤ vfValue (x i) := by
      refine ⟨γ₁, fun x hx i => ?_⟩
      obtain ⟨a, p, -, hp⟩ := hx
      have := hγ₁ _ ⟨baseMap hAP p, rfl⟩ i
      rw [prodMap_apply] at hp
      have hx1 : (g (baseMap hAP p)).val.1 = x := congrArg Prod.fst hp
      rw [← hx1]
      exact this
    obtain ⟨δ, hδ, hinv⟩ := clopen_has_named_invariant_radius h00 hc hκ hs hv _ (hdef.mono hsub) hcl hbd
    exact ⟨fun _ => δ, fun _ => hδ, hinv⟩

variable (linear : GammaPiecewiseRationalAffineInput (M := M)) (hsmall : Cardinal.mk S < κ)
  (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))

include h00 hc hκ hs hv linear hsmall hΓ in
/-- **`g ⋉ A` is a proper covariant homeomorphism onto its image.** -/
theorem prodMap_properHomeomorphism (hg : ProperCovariantHomeomorphism (G := G) g)
    (hA : ProperInvariant S A.carrier) : ProperCovariantHomeomorphism (G := G) (prodMap g hAP).toImage := by
  have hB := prodMap_image_properInvariant g hAP hv h00 hc hκ hs hg hA
  have hcont := prodMap_continuous g hAP hg
  have hcov : ProperCovariant (prodMap g hAP).toImage :=
    properCovariant_of_clopen_ranges h00 hc hκ hs hv _ hA hB hcont
      (fun u t => prodMap_source_isOpen g hAP hv hg hA u t)
      (fun u t => prodMap_range_isClopen g hAP hv hg hA u t)
  have hbij : Function.Bijective (prodMap g hAP).toImage := by
    refine ⟨fun p q he => prodMap_injective g hAP hg.bijective.1 (Subtype.ext (by
      have h := congrArg Subtype.val he
      exact h)), ?_⟩
    rintro ⟨_, p, rfl⟩
    exact ⟨p, rfl⟩
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ _ hcov hbij hcont

end DiamondIntegral.Section7.Lemma714Prod
