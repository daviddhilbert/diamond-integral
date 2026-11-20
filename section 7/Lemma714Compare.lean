import «section 7».Lemma714HeadSteps
import «section 7».SetBaseMatching

/-! Lemma 7.14, part 16: Lemma 7.13 with a head start.

`muIsp_head` is the head-start form of Lemma 7.13 (core form). Let `X`, `Y` be
unary head-start chain sets with labels `λ`, `μ` over a base with support data,
and let `f : X → Y` be a proper covariant homeomorphism that keeps the labels
(`f(p)_{μ i} = p_{λ i}`) and has generic Jacobian `ω / σ`. Then the head-start
classes are `μIsp^db`-related in grade `1 + k`.

Proof. Lemma 6.38's core (`lemma_6_38_bounded_variable_apertures_of_support`)
needs no finite RV fibres, so it applies to `f`. Its chains carry the labels,
and the head-start Lemma 7.11 (`claimH_relative_chain`) turns them into blowups.
The matching of the final sets keeps the labels and the product
"form × leading value" (`PreparedUnaryRVMatching.volume`). So the final
head-start contractions are isomorphic (`clsH_eq_of_balance`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### Coordinates of head-start tuples -/

section Apply
variable {X : Type*} {n : ℕ}

omit [LRV.Structure M] hM in
theorem headStartBaseVF_apply : ∀ (k : ℕ) (z : Fin (n + k) → X) (i : Fin n),
    headStartBaseVF n k z i = z (Fin.castAdd k i)
  | 0, _, _ => rfl
  | k + 1, z, i => by
    change headStartBaseVF n k (Fin.init z) i = _
    rw [headStartBaseVF_apply k (Fin.init z) i]
    rfl

omit [LRV.Structure M] hM in
theorem headStartExtraVF_apply : ∀ (k : ℕ) (z : Fin (n + k) → X) (j : Fin k),
    headStartExtraVF n k z j = z (Fin.natAdd n j)
  | 0, _, j => j.elim0
  | k + 1, z, j => by
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp only [headStartExtraVF, Fin.lastCases_last]
      rfl
    · simp only [headStartExtraVF, Fin.lastCases_castSucc]
      rw [headStartExtraVF_apply k (Fin.init z) j']
      rfl

end Apply

/-! ### Head-start classes along a balanced matching -/

section Balance
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {r s k : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {Y : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)}
  {lab : Fin k → Fin r} {lab' : Fin k → Fin s}

theorem codeValue_rv_eq (t : RVInfinity M) (ht : t.val ≠ iRVZero) :
    GammaParameters.codeValue t.val = Values.gammaOf t ht := by
  apply Subtype.ext
  rw [nonzero_rv_codeValue_val t (fun h => ht (congrArg Subtype.val h))]
  rfl

theorem hsObj_volumeGamma (g : HGood X lab)
    (hT : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (p : rvHeadStartBundle X k lab) :
    (hsObj g hT).volumeGamma (pureRVTagQuotient _ p) =
      ∏ i, GammaParameters.codeValue (rv M (p.val.1 i)).val := by
  unfold MeasuredRVObject.volumeGamma rvVolumeGamma
  apply Finset.prod_congr rfl
  intro i _
  have hne : rv M (p.val.1 i) ≠ rvZero M := by
    intro he
    exact (bundleGood g).vfBounded.nonzero p.property i ((rv_eq_zero_iff _).mp he)
  rw [codeValue_rv_eq _ (fun h => hne (Subtype.ext h))]
  congr 1
  change (preparedRVObject (rvHeadStartBundle X k lab) _).value (pureRVTagQuotient _ p) i = _
  rw [preparedRVObject_value]
  rfl

/-- **Balanced matchings keep the head-start class.** A bijection of
head-start chain sets that maps whole label fibres, keeps the labels and keeps
the product of the form and the leading value gives isomorphic head-start
contractions. -/
theorem clsH_eq_of_balance (g : HGood X lab) (g' : HGood Y lab')
    (hTX : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hTY : ∀ p ∈ Y.carrier, ∀ q ∈ Y.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (f : Map X Y) (hf : Function.Bijective f) (hm : MapsWholeTagFibres f)
    (hL : ∀ p : X, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i))
    (hbal : ∀ p : X, gammaMapValue g'.form (f p) * GammaParameters.codeValue (rv M ((f p).val.1 0)).val =
      gammaMapValue g.form p * GammaParameters.codeValue (rv M (p.val.1 0)).val) :
    clsH hc g = clsH hc g' := by
  rw [clsH_eq_hsObj hc g hTX, clsH_eq_hsObj hc g' hTY]
  apply cls_objOf_eq hc
  let H := carryHeadStartBijection f hf k lab lab' hL
  have hmH := carried_wholeFibres f hf hm hL
  refine ⟨rvIsoOfFiniteFibres (pureRVTagMatchingMap H.map hmH) (pureRVTagMatchingMap_bijective H.map H.bijective hmH)
    (hsObj g hTX).finiteVolume (hsObj g' hTY).finiteVolume (hsObj g hTX).nonzero (hsObj g' hTY).nonzero, fun u => ?_⟩
  obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ u
  rw [rvIsoOfFiniteFibres_map, pureRVTagMatchingMap_commutes]
  unfold MeasuredRVObject.totalWeight
  rw [hsObj_volumeGamma, hsObj_volumeGamma]
  have hf1 : gammaMapValue (hsObj g hTX).form (pureRVTagQuotient _ p) =
      gammaMapValue g.form (headStartBaseProjection X k lab p) :=
    contractedMeasuredRVObject_form _ _ _ _ _ _ _ p
  have hf2 : gammaMapValue (hsObj g' hTY).form (pureRVTagQuotient _ (H.map p)) =
      gammaMapValue g'.form (f (headStartBaseProjection X k lab p)) := by
    rw [← H.base p]
    exact contractedMeasuredRVObject_form _ _ _ _ _ _ _ (H.map p)
  rw [hf1, hf2, Fin.prod_univ_add, Fin.prod_univ_add, Fin.prod_univ_one, Fin.prod_univ_one]
  have hbase : ∀ z : rvHeadStartBundle X k lab, z.val.1 (Fin.castAdd k 0) = (headStartBaseProjection X k lab z).val.1 0 := by
    intro z
    rw [headStartBaseProjection_value]
    exact (headStartBaseVF_apply k _ 0).symm
  have hbase' : (H.map p).val.1 (Fin.castAdd k 0) = (f (headStartBaseProjection X k lab p)).val.1 0 := by
    rw [← H.base p, headStartBaseProjection_value]
    exact (headStartBaseVF_apply k _ 0).symm
  have hextra : ∀ j, (H.map p).val.1 (Fin.natAdd 1 j) = p.val.1 (Fin.natAdd 1 j) := by
    intro j
    have := congrFun (H.fixed p) j
    rwa [headStartExtraVF_apply, headStartExtraVF_apply] at this
  rw [hbase p, hbase']
  simp only [hextra]
  rw [← mul_assoc, ← mul_assoc, hbal]

end Balance

/-! ### Lemma 7.13 with a head start -/

section Head
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {r s k : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (W : Set M) (hW : ∀ x ∈ W, iVF x) (hWT : W ⊆ (T : Set M)) (hTW : (T : Set M) ⊆ algebraicClosureSet W)
  (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
  (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include h00 hκ hs hv hW hWT hTW hnt hsmall hΓ in
/-- **Lemma 7.13 with a head start (core form).** A label-preserving proper
covariant homeomorphism with generic Jacobian `ω / σ` between unary head-start
chain sets gives `μIsp^db`-related head-start classes. -/
theorem muIsp_head {X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {Y : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {lab : Fin k → Fin r} {lab' : Fin k → Fin s}
    (g : HGood X lab) (g' : HGood Y lab')
    (hPX : ProperInvariant (T : Set M) X.carrier) (hPY : ProperInvariant (T : Set M) Y.carrier)
    (f : Map X Y) (hf : ProperCovariantHomeomorphism f)
    (hL : ∀ p : X, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i))
    (hωLevels : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a, u) ∈ X.carrier ∧ gammaFormExtension g.form (a, u) = γ})
    (hσLevels : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a, u) ∈ Y.carrier ∧ gammaFormExtension g'.form (a, u) = γ})
    (hGeneric : ∀ a : X, AlgebraicIndependent (vfParameterField (T : Set M)) a.val.1 →
      ∃ J : VF M, HasMixedVFJacobianAt f a J ∧ vfValue J = (gammaMapValue g.form a / gammaMapValue g'.form (f a)).val) :
    MuIsp (clsH hc g) (clsH hc g') := by
  obtain ⟨H, chX, chY⟩ := SetBaseMatching.lemma_6_38_bounded_variable_apertures_of_support (G := G) h00 hc lin hκ hs hv
    (T : Set M) W hW hWT hTW hnt hsmall hΓ X Y f hf hPX hPY g.form g'.form hωLevels hσLevels hGeneric
  obtain ⟨labS, hLS, gS, hfS, m, hm⟩ := claimH_relative_chain hc h00 hκ hs hv hsmall chX lab g
  obtain ⟨labT, hLT, gT, hfT, n, hn⟩ := claimH_relative_chain hc h00 hκ hs hv hsmall chY lab' g'
  have hsrc := H.geometry.sourceChain.bijective h00
  have hFS : ∀ x : H.geometry.source, gS.form x = H.geometry.sourceForm h00 g.form x := by
    intro x
    obtain ⟨a, rfl⟩ := hsrc.2 x
    rw [hfS, UnaryRelativePreparedMatching.sourceForm_transport]
  have hFT : ∀ y : H.geometry.target, gT.form y = H.geometry.targetForm h00 g'.form y := by
    intro y
    obtain ⟨b, rfl⟩ := (H.geometry.targetChain.bijective h00).2 y
    rw [hfT, UnaryRelativePreparedMatching.targetForm_transport]
  have heq : clsH hc gS = clsH hc gT := by
    refine clsH_eq_of_balance hc gS gT H.geometry.sourceTagged H.geometry.targetTagged H.geometry.map
      H.geometry.bijective H.geometry.wholeFibres ?_ ?_
    · intro x i
      obtain ⟨a, rfl⟩ := hsrc.2 x
      rw [H.geometry.commutes, hLT, hL, hLS]
    · intro x
      have h := H.rv.volume (rvTagQuotientMap H.geometry.source x)
      rw [H.rv.commutes x] at h
      unfold gammaMapValue
      rw [hFS, hFT, ← gammaFormExtension_at, ← gammaFormExtension_at,
        ← H.sourceContracted_at x.val x.property, ← H.targetContracted_at (H.geometry.map x).val (H.geometry.map x).property,
        H.sourceLeading x.val x.property, H.targetLeading (H.geometry.map x).val (H.geometry.map x).property]
      exact h.symm
  exact ⟨clsH hc gT, m, n, heq ▸ hm, hn⟩

end Head

end DiamondIntegral.Section7.Lemma714Head
