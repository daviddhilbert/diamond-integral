import «section 7».ProductClasses
import «section 7».BlowupResults
import «section 7».FiberwiseInput

/-! Lemma 7.10 (`isp:congruence:vol`), multiplicative part: `μIsp^db` is
compatible with products on both sides.

Statement. For classes `x, y` of `μRV^db[1+k]` and `z` of `μRV^db[l]`, if
`(x, y) ∈ μIsp^db` then `(x z, y z) ∈ μIsp^db` and `(z x, z y) ∈ μIsp^db`, read in
any degree `1 + K` equal to the degree of the products (`muIsp_mul_right`,
`muIsp_mul_left`). Together with the additive congruence
(`BlowupResults.lemma_7_10_addCon`) this is `lemma_7_10`. In the graded form,
with `μIsp^db` in degree `0` read as equality of classes
(`FiberwiseInput.IspRel`), `μIsp^db[*]` is an equivalence relation in every
degree, compatible with sums and with products of homogeneous classes of any
degrees (`lemma_7_10_graded`): the semiring congruence of the paper.

Route (PLAN §7.10, Remark 7.25: "the product of a generator with a class `[W]`
is the generator for the pulled-back aperture on the product object").
For an aperture datum `D = (U, j, τ)` of degree `1+k` and an object `W` of
degree `l`, `datumMul D W h` is the datum on `U × W` with the coordinate `j` of
`U` and the pulled-back aperture `τ(u, w) = τ(u)`, read in degree `1 + K` along
`h : l + (1 + k) = 1 + K`. The finite-to-one condition survives because the
inactive projection of `U × W` is the inactive projection of `U` joined with the
structural map of `W` (`inactiveFinite_prod`); the pulled-back aperture is
definable over the same base with the same bound `Δ` because it is a coordinate
projection followed by `τ`, and `U × W` is doubly bounded
(`RVMeasuredProductProperties.product_domain_bounded`). The
shell and the endpoint graph of `datumMul D W h` are isomorphic to `U♭_shell × W`
and `U♭_end × W` by a permutation of raw coordinates (`shellProdIso`,
`endProdIso`); the weights agree because the blown-up coordinate of `U × W` is
the blown-up coordinate of `U` joined with the coordinates of `W`
(`prod_blown_weight`). Hence the source and blowup classes of `datumMul D W h`
are `[U] [W]` and `[U♭] [W]` (`cls_datumMul_source`, `cls_datumMul_annular`), a
blowup step of `x` gives a blowup step of `x z` (`step_mul_right`), and left
products follow by commutativity (`ProductClasses.cls_mul_comm`). In Section 4's
ring the generator of the product datum is the generator of `D` times `[W]`
(`generator_datumMul`), the sentence of Remark 7.25 quoted above. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.ProductBlowups
open DiamondIntegral.Section4
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions FiniteTupleBlocks FiniteTupleGraphProduct
open RVRealProducts RVMeasuredProduct
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ProductClasses
open DiamondIntegral.Section7.FiberwiseInput (IspRel ispRel_iff)
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)}

/-! ### Finite tuples -/

theorem headIndex_ne_tailIndex (n m : ℕ) (i : Fin m) (j : Fin n) : headIndex n m i ≠ tailIndex n m j := by
  intro h
  have h1 := congrArg Fin.val h
  rw [headIndex_val, tailIndex_val] at h1
  have := i.isLt
  omega

theorem update_join_head {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) (j : Fin m) (v : α) :
    Function.update (join n m u y) (headIndex n m j) v = join n m (Function.update u j v) y := by
  apply block_ext n m
  · funext i
    simp only [Function.comp_apply]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, join_head, Function.update_self]
    · rw [Function.update_of_ne ((headIndex_injective n m).ne hij), join_head, join_head,
        Function.update_of_ne hij]
  · funext i
    simp only [Function.comp_apply]
    rw [Function.update_of_ne (headIndex_ne_tailIndex n m j i).symm, join_tail, join_tail]

theorem join_inj {α : Type*} (n m : ℕ) {u u' : Fin m → α} {y y' : Fin n → α}
    (h : join n m u y = join n m u' y') : u = u' ∧ y = y' :=
  ⟨funext fun i => by simpa using congrFun h (headIndex n m i),
    funext fun i => by simpa using congrFun h (tailIndex n m i)⟩

/-! ### Degree casts of apertures and of the finite-to-one condition -/

section Cast
variable {m m' : ℕ} (h : m = m')

/-- An aperture read on the degree cast (same domain and function). -/
def apCast {Q : Chart B m} (τ : Aperture Q) : Aperture (castChart h Q) :=
  ⟨τ.aperture, τ.graph_definable, τ.nonzero, τ.nonnegative, τ.bound, τ.bounded⟩

theorem inactiveFinite_cast {Q : Chart B m} {j : Fin m} (hf : InactiveFinite Q j) :
    InactiveFinite (castChart h Q) (Fin.cast h j) := by
  subst h
  exact hf

theorem castBlown_weight (Q : Chart B m) (j : Fin m) (u : Fin Q.arity → M) (s : M) :
    (castChart h Q).volume u * ∏ i, codeValue (blownCoordinate (castChart h Q) (Fin.cast h j) u s i) =
      Q.volume u * ∏ i, codeValue (blownCoordinate Q j u s i) := by
  subst h
  rfl

end Cast

/-! ### The product chart, its finite-to-one condition and its aperture -/

section Product
variable {k l : ℕ} (r : Chart B (1 + k)) (c : Chart B l)

theorem prod_coordinate_join (x : Fin r.arity → M) (y : Fin c.arity → M) :
    (product r c).coordinate (join c.arity r.arity x y) = join l (1 + k) (r.coordinate x) (c.coordinate y) :=
  productMap_join r.coordinate c.coordinate x y

/-- The blown-up coordinate of `U × W` is that of `U` joined with the
coordinates of `W`. -/
theorem blown_prod (j : Fin (1 + k)) (x : Fin r.arity → M) (y : Fin c.arity → M) (s : M) :
    blownCoordinate (product r c) (headIndex l (1 + k) j) (join c.arity r.arity x y) s =
      join l (1 + k) (blownCoordinate r j x s) (c.coordinate y) := by
  unfold blownCoordinate
  rw [prod_coordinate_join, join_head, update_join_head]

/-- The weight of a blown-up point of `U × W` is the blown-up weight of `U`
times the weight of `W`. -/
theorem prod_blown_weight (j : Fin (1 + k)) (x : Fin r.arity → M) (y : Fin c.arity → M) (s : M) :
    (product r c).volume (join c.arity r.arity x y) *
        ∏ i, codeValue (blownCoordinate (product r c) (headIndex l (1 + k) j) (join c.arity r.arity x y) s i) =
      (r.volume x * ∏ i, codeValue (blownCoordinate r j x s i)) * c.correctedWeight y := by
  have hp := GammaSumMap.prod_blocks l (1 + k)
    (fun i => codeValue (join l (1 + k) (blownCoordinate r j x s) (c.coordinate y) i))
  simp only [join_head, join_tail] at hp
  rw [product_volume_join, blown_prod, hp]
  change _ = _ * (c.volume y * ∏ i, codeValue (c.coordinate y i))
  ac_rfl

theorem inactive_prod (j : Fin (1 + k)) (x : Fin r.arity → M) (y : Fin c.arity → M) :
    inactive (product r c) (headIndex l (1 + k) j) (join c.arity r.arity x y) =
      join l (1 + k) (inactive r j x) (c.coordinate y) := by
  unfold inactive
  rw [prod_coordinate_join, update_join_head]

/-- Definition 7.2's finite-to-one condition survives the product. -/
theorem inactiveFinite_prod (j : Fin (1 + k)) (hf : InactiveFinite r j) :
    InactiveFinite (product r c) (headIndex l (1 + k) j) := by
  intro t
  let A : Set (Fin r.arity → M) := {x | x ∈ r.domain ∧ inactive r j x = t ∘ headIndex l (1 + k)}
  let C : Set (Fin c.arity → M) := {y | y ∈ c.domain ∧ c.coordinate y = t ∘ tailIndex l (1 + k)}
  have hfin : ((fun p : (Fin r.arity → M) × (Fin c.arity → M) => join c.arity r.arity p.1 p.2) ''
      (A ×ˢ C)).Finite := ((hf _).prod (c.finite_fibres _)).image _
  apply hfin.subset
  rintro p ⟨hpd, hpt⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := (productSet_exists _ _ p).mp hpd
  rw [inactive_prod] at hpt
  refine ⟨(x, y), ⟨⟨hx, ?_⟩, hy, ?_⟩, rfl⟩
  · rw [← hpt]
    funext i
    simp
  · rw [← hpt]
    funext i
    simp

/-- The pulled-back aperture `τ(u, w) = τ(u)` on `U × W`. -/
def apProd (τ : Aperture r) : Aperture (product r c) where
  aperture p := τ.aperture (p ∘ headIndex c.arity r.arity)
  graph_definable :=
    RVGraphComposition.graph_compose_definable B (product r c).domain r.domain
      (fun p => p ∘ headIndex c.arity r.arity) (fun u => ![τ.aperture u])
      (RVCoordinateMaps.coordinate_graph_definable B _ (product r c).domain_definable (headIndex c.arity r.arity))
      τ.graph_definable (fun _ hp => hp.1)
  nonzero _ hp := τ.nonzero _ hp.1
  nonnegative _ hp := τ.nonnegative _ hp.1
  bound := τ.bound
  bounded _ hp := τ.bounded _ hp.1

theorem apProd_join (τ : Aperture r) (x : Fin r.arity → M) (y : Fin c.arity → M) :
    (apProd r c τ).aperture (join c.arity r.arity x y) = τ.aperture x :=
  congrArg τ.aperture (funext (join_head c.arity r.arity x y))

end Product

/-! ### The product datum -/

/-- The product of an aperture datum `D = (U, j, τ)` with an object `W`: the
datum on `U × W` with the coordinate `j` of `U` and the pulled-back aperture,
read in degree `1 + K` along `h : l + (1 + k) = 1 + K`. -/
def datumMul {k l K : ℕ} (D : AnnularDatum B k) (c : Obj B l) (h : l + (1 + k) = 1 + K) :
    AnnularDatum B K where
  chart := castChart h (product D.chart c.toChart)
  coordinate := Fin.cast h (headIndex l (1 + k) D.coordinate)
  finite := inactiveFinite_cast h (inactiveFinite_prod D.chart c.toChart D.coordinate D.finite)
  aperture := apCast h (apProd D.chart c.toChart D.aperture)
  bounded := RVMeasuredProductProperties.product_domain_bounded D.chart c.toChart D.bounded c.domain_bounded

/-- The source of the product datum is `U × W`. -/
theorem cls_datumMul_source {k l K : ℕ} (D : AnnularDatum B k) (c : Obj B l) (h : l + (1 + k) = 1 + K) :
    cls (datumMul D c h).source = castCls h (cls D.source * cls c) := by
  rw [cls_mul, castCls_cls]
  rfl

/-! ### Points of the shell and of the endpoint graph -/

section Points
variable {m : ℕ}

theorem mem_graph_iff (Q : Chart B m) (σ : Aperture Q) (w : Fin (1 + Q.arity) → M) :
    w ∈ (graphChart Q σ).domain ↔ ∃ x ∈ Q.domain, w = join 1 Q.arity x ![σ.aperture x] :=
  graphOn_exists Q.domain (fun u => ![σ.aperture u]) w

theorem mem_shell_iff (Q : Chart B m) (σ : Aperture Q) (w : Fin (1 + (1 + Q.arity)) → M) :
    w ∈ shellDomain Q σ ↔ ∃ x s, (x, s) ∈ shellPoints Q σ ∧
      w = join 1 (1 + Q.arity) (join 1 Q.arity x ![σ.aperture x]) ![s] := by
  constructor
  · intro hw
    exact ⟨w ∘ xIdx Q, w (sIdx Q), shell_points Q σ hw, shell_canonical Q σ hw⟩
  · rintro ⟨x, s, ⟨hx, hs, h1, h2⟩, rfl⟩
    have e1 : join 1 (1 + Q.arity) (join 1 Q.arity x ![σ.aperture x]) ![s] ∘ headIndex 1 (1 + Q.arity) =
        join 1 Q.arity x ![σ.aperture x] := funext (join_head _ _ _ _)
    have e2 : join 1 (1 + Q.arity) (join 1 Q.arity x ![σ.aperture x]) ![s] ∘ tailIndex 1 (1 + Q.arity) =
        ![s] := funext (join_tail _ _ _ _)
    have e3 : join 1 (1 + Q.arity) (join 1 Q.arity x ![σ.aperture x]) ![s] (sIdx Q) = s := by
      simp [sIdx]
    have e4 : join 1 Q.arity x ![σ.aperture x] (aIdx Q) = σ.aperture x := by
      simp [aIdx]
    rw [shell_iff, e1, e2, e3, e4]
    refine ⟨(mem_graph_iff Q σ _).mpr ⟨x, hx, rfl⟩, ?_, h1, h2⟩
    intro i
    fin_cases i
    exact hs

/-- The weight of a shell point depends only on `u` and `s`. -/
theorem shell_weight_join (Q : Chart B m) (j : Fin m) (hfin : InactiveFinite Q j) (σ : Aperture Q)
    (x : Fin Q.arity → M) (a s : M) :
    (shellChart Q j hfin σ).correctedWeight (join 1 (1 + Q.arity) (join 1 Q.arity x ![a]) ![s]) =
      Q.volume x * ∏ i, codeValue (blownCoordinate Q j x s i) := by
  have hx : join 1 (1 + Q.arity) (join 1 Q.arity x ![a]) ![s] ∘ xIdx Q = x := by
    funext i
    simp [xIdx]
  have hs : join 1 (1 + Q.arity) (join 1 Q.arity x ![a]) ![s] (sIdx Q) = s := by
    simp [sIdx]
  change Q.volume (join 1 (1 + Q.arity) (join 1 Q.arity x ![a]) ![s] ∘ xIdx Q) *
      ∏ i, codeValue (blownCoordinate Q j (join 1 (1 + Q.arity) (join 1 Q.arity x ![a]) ![s] ∘ xIdx Q)
        (join 1 (1 + Q.arity) (join 1 Q.arity x ![a]) ![s] (sIdx Q)) i) = _
  rw [hx, hs]

/-- The weight of an endpoint. -/
theorem endpoint_weight_join (Q : Chart B m) (j : Fin m) (hfin : InactiveFinite Q j) (σ : Aperture Q)
    (x : Fin Q.arity → M) (a : M) :
    (endpointChart Q j hfin σ).correctedWeight (join 1 Q.arity x ![a]) =
      Q.volume x * ∏ i, codeValue (blownCoordinate Q j x a i) := by
  have hx : join 1 Q.arity x ![a] ∘ headIndex 1 Q.arity = x := funext (join_head _ _ _ _)
  have ha : join 1 Q.arity x ![a] (aIdx Q) = a := by
    simp [aIdx]
  change Q.volume (join 1 Q.arity x ![a] ∘ headIndex 1 Q.arity) *
      ∏ i, codeValue (blownCoordinate Q j (join 1 Q.arity x ![a] ∘ headIndex 1 Q.arity)
        (join 1 Q.arity x ![a] (aIdx Q)) i) = _
  rw [hx, ha]

end Points

/-! ### Permutations of raw coordinates -/

section Perm
variable (A C : ℕ)

/-- The raw coordinates of `((u, w), τ(u), s)` rearranged as `((u, τ(u), s), w)`. -/
def shellPerm : Fin (C + (1 + (1 + A))) → Fin (1 + (1 + (C + A))) :=
  join C (1 + (1 + A))
    (join 1 (1 + A)
      (join 1 A (fun i => headIndex 1 (1 + (C + A)) (headIndex 1 (C + A) (headIndex C A i)))
        (fun _ => headIndex 1 (1 + (C + A)) (tailIndex 1 (C + A) 0)))
      (fun _ => tailIndex 1 (1 + (C + A)) 0))
    (fun i => headIndex 1 (1 + (C + A)) (headIndex 1 (C + A) (tailIndex C A i)))

omit [LRV.Structure M] hM in
theorem shellPerm_join (x : Fin A → M) (y : Fin C → M) (a s : M) :
    join 1 (1 + (C + A)) (join 1 (C + A) (join C A x y) ![a]) ![s] ∘ shellPerm A C =
      join C (1 + (1 + A)) (join 1 (1 + A) (join 1 A x ![a]) ![s]) y := by
  apply block_ext C (1 + (1 + A))
  · apply block_ext 1 (1 + A)
    · apply block_ext 1 A
      · funext i
        simp [shellPerm, Function.comp_apply]
      · funext i
        simp [shellPerm, Function.comp_apply]
    · funext i
      simp [shellPerm, Function.comp_apply]
  · funext i
    simp [shellPerm, Function.comp_apply]

/-- The raw coordinates of `((u, w), τ(u))` rearranged as `((u, τ(u)), w)`. -/
def endPerm : Fin (C + (1 + A)) → Fin (1 + (C + A)) :=
  join C (1 + A)
    (join 1 A (fun i => headIndex 1 (C + A) (headIndex C A i)) (fun _ => tailIndex 1 (C + A) 0))
    (fun i => headIndex 1 (C + A) (tailIndex C A i))

omit [LRV.Structure M] hM in
theorem endPerm_join (x : Fin A → M) (y : Fin C → M) (a : M) :
    join 1 (C + A) (join C A x y) ![a] ∘ endPerm A C = join C (1 + A) (join 1 A x ![a]) y := by
  apply block_ext C (1 + A)
  · apply block_ext 1 A
    · funext i
      simp [endPerm, Function.comp_apply]
    · funext i
      simp [endPerm, Function.comp_apply]
  · funext i
    simp [endPerm, Function.comp_apply]

end Perm

/-! ### The shell and the endpoint graph of the product datum -/

section Iso
variable {k l K : ℕ} (r : Chart B (1 + k)) (j : Fin (1 + k)) (hfin : InactiveFinite r j) (τ : Aperture r)
  (c : Chart B l) (h : l + (1 + k) = 1 + K)

theorem mem_shellProd (w : Fin (1 + (1 + (c.arity + r.arity))) → M) :
    w ∈ shellDomain (castChart h (product r c)) (apCast h (apProd r c τ)) ↔
      ∃ x y s, (x, s) ∈ shellPoints r τ ∧ y ∈ c.domain ∧
        w = join 1 (1 + (c.arity + r.arity)) (join 1 (c.arity + r.arity) (join c.arity r.arity x y)
          ![τ.aperture x]) ![s] := by
  rw [mem_shell_iff]
  constructor
  · rintro ⟨p, s, ⟨hp, hs, h1, h2⟩, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (productSet_exists _ _ p).mp hp
    have ha := apProd_join r c τ x y
    refine ⟨x, y, s, ⟨hx, hs, h1, ?_⟩, hy, ?_⟩
    · rw [← ha]
      exact h2
    · change join 1 (1 + (c.arity + r.arity)) (join 1 (c.arity + r.arity) (join c.arity r.arity x y)
          ![(apProd r c τ).aperture (join c.arity r.arity x y)]) ![s] = _
      rw [ha]
  · rintro ⟨x, y, s, ⟨hx, hs, h1, h2⟩, hy, rfl⟩
    have ha := apProd_join r c τ x y
    refine ⟨join c.arity r.arity x y, s, ⟨(productSet_join _ _ x y).mpr ⟨hx, hy⟩, hs, h1, ?_⟩, ?_⟩
    · change codeValue s ≤ codeValue ((apProd r c τ).aperture (join c.arity r.arity x y))
      rw [ha]
      exact h2
    · change _ = join 1 (1 + (c.arity + r.arity)) (join 1 (c.arity + r.arity) (join c.arity r.arity x y)
          ![(apProd r c τ).aperture (join c.arity r.arity x y)]) ![s]
      rw [ha]

theorem mem_endProd (w : Fin (1 + (c.arity + r.arity)) → M) :
    w ∈ (graphChart (castChart h (product r c)) (apCast h (apProd r c τ))).domain ↔
      ∃ x y, x ∈ r.domain ∧ y ∈ c.domain ∧
        w = join 1 (c.arity + r.arity) (join c.arity r.arity x y) ![τ.aperture x] := by
  rw [mem_graph_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (productSet_exists _ _ p).mp hp
    refine ⟨x, y, hx, hy, ?_⟩
    change join 1 (c.arity + r.arity) (join c.arity r.arity x y)
      ![(apProd r c τ).aperture (join c.arity r.arity x y)] = _
    rw [apProd_join]
  · rintro ⟨x, y, hx, hy, rfl⟩
    refine ⟨join c.arity r.arity x y, (productSet_join _ _ x y).mpr ⟨hx, hy⟩, ?_⟩
    change _ = join 1 (c.arity + r.arity) (join c.arity r.arity x y)
      ![(apProd r c τ).aperture (join c.arity r.arity x y)]
    rw [apProd_join]

/-- The shell of the product datum is isomorphic to the product of the shell of
`D` with `W`. -/
def shellProdIso :
    Iso (shellChart (castChart h (product r c)) (Fin.cast h (headIndex l (1 + k) j))
        (inactiveFinite_cast h (inactiveFinite_prod r c j hfin)) (apCast h (apProd r c τ)))
      (castChart h (product (shellChart r j hfin τ) c)) := by
  refine RVCoordinateMaps.coordinateIso _ _ (shellPerm r.arity c.arity) ?_ ?_
  · change Set.BijOn (fun w : Fin (1 + (1 + (c.arity + r.arity))) → M =>
        (w ∘ shellPerm r.arity c.arity : Fin (c.arity + (1 + (1 + r.arity))) → M))
      (shellDomain (castChart h (product r c)) (apCast h (apProd r c τ)))
      (productSet (shellDomain r τ) c.domain)
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨x, y, s, hxs, hy, rfl⟩ := (mem_shellProd r τ c h w).mp hw
      beta_reduce
      rw [shellPerm_join, productSet_join]
      exact ⟨(mem_shell_iff r τ _).mpr ⟨x, s, hxs, rfl⟩, hy⟩
    · intro w hw w' hw' he
      obtain ⟨x, y, s, _, _, rfl⟩ := (mem_shellProd r τ c h w).mp hw
      obtain ⟨x', y', s', _, _, rfl⟩ := (mem_shellProd r τ c h w').mp hw'
      have he' : join c.arity (1 + (1 + r.arity)) (join 1 (1 + r.arity) (join 1 r.arity x ![τ.aperture x]) ![s]) y =
          join c.arity (1 + (1 + r.arity)) (join 1 (1 + r.arity) (join 1 r.arity x' ![τ.aperture x']) ![s']) y' := by
        rw [← shellPerm_join, ← shellPerm_join]
        exact he
      obtain ⟨h1, rfl⟩ := join_inj _ _ he'
      obtain ⟨h2, h3⟩ := join_inj _ _ h1
      obtain ⟨rfl, _⟩ := join_inj _ _ h2
      have : s = s' := congrFun h3 0
      subst this
      rfl
    · intro v hv
      obtain ⟨q, hq, y, hy, rfl⟩ := (productSet_exists _ _ v).mp hv
      obtain ⟨x, s, hxs, rfl⟩ := (mem_shell_iff r τ q).mp hq
      exact ⟨_, (mem_shellProd r τ c h _).mpr ⟨x, y, s, hxs, hy, rfl⟩, shellPerm_join _ _ _ _ _ _⟩
  · change ∀ w : Fin (1 + (1 + (c.arity + r.arity))) → M,
      w ∈ shellDomain (castChart h (product r c)) (apCast h (apProd r c τ)) →
      (shellChart (castChart h (product r c)) (Fin.cast h (headIndex l (1 + k) j))
        (inactiveFinite_cast h (inactiveFinite_prod r c j hfin)) (apCast h (apProd r c τ))).correctedWeight w =
        (castChart h (product (shellChart r j hfin τ) c)).correctedWeight
          (w ∘ shellPerm r.arity c.arity : Fin (c.arity + (1 + (1 + r.arity))) → M)
    intro w hw
    obtain ⟨x, y, s, _, _, rfl⟩ := (mem_shellProd r τ c h w).mp hw
    refine (shell_weight_join (castChart h (product r c)) (Fin.cast h (headIndex l (1 + k) j))
      (inactiveFinite_cast h (inactiveFinite_prod r c j hfin)) (apCast h (apProd r c τ))
      (join c.arity r.arity x y) (τ.aperture x) s).trans ?_
    refine (castBlown_weight h (product r c) (headIndex l (1 + k) j) (join c.arity r.arity x y) s).trans ?_
    refine (prod_blown_weight r c j x y s).trans ?_
    refine Eq.trans ?_ (castChart_weight h (product (shellChart r j hfin τ) c) _).symm
    rw [shellPerm_join]
    refine Eq.trans ?_ (prod_weight_join (shellChart r j hfin τ) c
      (join 1 (1 + r.arity) (join 1 r.arity x ![τ.aperture x]) ![s]) y).symm
    rw [shell_weight_join]

/-- The endpoint graph of the product datum is isomorphic to the product of the
endpoint graph of `D` with `W`. -/
def endProdIso :
    Iso (endpointChart (castChart h (product r c)) (Fin.cast h (headIndex l (1 + k) j))
        (inactiveFinite_cast h (inactiveFinite_prod r c j hfin)) (apCast h (apProd r c τ)))
      (castChart h (product (endpointChart r j hfin τ) c)) := by
  refine RVCoordinateMaps.coordinateIso _ _ (endPerm r.arity c.arity) ?_ ?_
  · change Set.BijOn (fun w : Fin (1 + (c.arity + r.arity)) → M =>
        (w ∘ endPerm r.arity c.arity : Fin (c.arity + (1 + r.arity)) → M))
      (graphChart (castChart h (product r c)) (apCast h (apProd r c τ))).domain
      (productSet (graphChart r τ).domain c.domain)
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨x, y, hx, hy, rfl⟩ := (mem_endProd r τ c h w).mp hw
      beta_reduce
      rw [endPerm_join, productSet_join]
      exact ⟨(mem_graph_iff r τ _).mpr ⟨x, hx, rfl⟩, hy⟩
    · intro w hw w' hw' he
      obtain ⟨x, y, _, _, rfl⟩ := (mem_endProd r τ c h w).mp hw
      obtain ⟨x', y', _, _, rfl⟩ := (mem_endProd r τ c h w').mp hw'
      have he' : join c.arity (1 + r.arity) (join 1 r.arity x ![τ.aperture x]) y =
          join c.arity (1 + r.arity) (join 1 r.arity x' ![τ.aperture x']) y' := by
        rw [← endPerm_join, ← endPerm_join]
        exact he
      obtain ⟨h1, rfl⟩ := join_inj _ _ he'
      obtain ⟨rfl, _⟩ := join_inj _ _ h1
      rfl
    · intro v hv
      obtain ⟨q, hq, y, hy, rfl⟩ := (productSet_exists _ _ v).mp hv
      obtain ⟨x, hx, rfl⟩ := (mem_graph_iff r τ q).mp hq
      exact ⟨_, (mem_endProd r τ c h _).mpr ⟨x, y, hx, hy, rfl⟩, endPerm_join _ _ _ _ _⟩
  · change ∀ w : Fin (1 + (c.arity + r.arity)) → M,
      w ∈ (graphChart (castChart h (product r c)) (apCast h (apProd r c τ))).domain →
      (endpointChart (castChart h (product r c)) (Fin.cast h (headIndex l (1 + k) j))
        (inactiveFinite_cast h (inactiveFinite_prod r c j hfin)) (apCast h (apProd r c τ))).correctedWeight w =
        (castChart h (product (endpointChart r j hfin τ) c)).correctedWeight
          (w ∘ endPerm r.arity c.arity : Fin (c.arity + (1 + r.arity)) → M)
    intro w hw
    obtain ⟨x, y, _, _, rfl⟩ := (mem_endProd r τ c h w).mp hw
    refine (endpoint_weight_join (castChart h (product r c)) (Fin.cast h (headIndex l (1 + k) j))
      (inactiveFinite_cast h (inactiveFinite_prod r c j hfin)) (apCast h (apProd r c τ))
      (join c.arity r.arity x y) (τ.aperture x)).trans ?_
    refine (castBlown_weight h (product r c) (headIndex l (1 + k) j) (join c.arity r.arity x y)
      (τ.aperture x)).trans ?_
    refine (prod_blown_weight r c j x y (τ.aperture x)).trans ?_
    refine Eq.trans ?_ (castChart_weight h (product (endpointChart r j hfin τ) c) _).symm
    rw [endPerm_join]
    refine Eq.trans ?_ (prod_weight_join (endpointChart r j hfin τ) c
      (join 1 r.arity x ![τ.aperture x]) y).symm
    rw [endpoint_weight_join]

end Iso

/-- **Remark 7.25, product of a generator with a class.** The blowup of the
product datum is `U♭ × W`: its class is `[U♭] [W]`. -/
theorem cls_datumMul_annular {k l K : ℕ} (D : AnnularDatum B k) (c : Obj B l) (h : l + (1 + k) = 1 + K) :
    cls (datumMul D c h).annularObject = castCls h (cls D.annularObject * cls c) := by
  rw [cls_annular (datumMul D c h), cls_annular D, ProductClasses.cls_add_mul, castCls_add, cls_mul, cls_mul,
    castCls_cls, castCls_cls]
  congr 1
  · exact cls_eq_of_iso (shellProdIso D.chart D.coordinate D.finite D.aperture c.toChart h)
  · exact cls_eq_of_iso (endProdIso D.chart D.coordinate D.finite D.aperture c.toChart h)

theorem toRing_castCls {m m' : ℕ} (e : m = m') (x : Cls B m) : toRing (castCls e x) = toRing x := by
  subst e
  rfl

/-- **Remark 7.25, in Section 4's ring.** The manuscript generator
`[(U × W)^{τ,j}] - [U × W]` of the product datum is the generator
`[U^{τ,j}] - [U]` of `D` times `[W]`. -/
theorem generator_datumMul {k l K : ℕ} (D : AnnularDatum B k) (c : Obj B l) (h : l + (1 + k) = 1 + K) :
    (datumMul D c h).generator = D.generator * RVBoundedRing.objectClass c := by
  have ha : RVBoundedRing.objectClass (datumMul D c h).annularObject =
      RVBoundedRing.objectClass D.annularObject * RVBoundedRing.objectClass c := by
    rw [← toRing_cls, cls_datumMul_annular, toRing_castCls, cls_mul, toRing_cls,
      RVBoundedRing.objectClass_product]
  have hs : RVBoundedRing.objectClass (datumMul D c h).source =
      RVBoundedRing.objectClass D.source * RVBoundedRing.objectClass c := by
    rw [← toRing_cls, cls_datumMul_source, toRing_castCls, cls_mul, toRing_cls,
      RVBoundedRing.objectClass_product]
  rw [AnnularDatum.generator, AnnularDatum.generator, ha, hs, sub_mul]

/-! ### Blowups and `μIsp^db` under products -/

section Congruence
variable {k l K : ℕ}

/-- A blowup of length one, multiplied on the right by a class, is a blowup of
length one of the product. -/
theorem step_mul_right {x y : Cls B (1 + k)} (z : Cls B l) (h : l + (1 + k) = 1 + K) (hs : Step x y) :
    Step (castCls h (x * z)) (castCls h (y * z)) := by
  obtain ⟨c, rfl⟩ := cls_surjective z
  obtain ⟨n, D, w, rfl, rfl⟩ := hs
  refine ⟨n, fun i => datumMul (D i) c h, castCls h (w * cls c), ?_, ?_⟩
  · rw [ProductClasses.cls_add_mul, cls_sum_mul, castCls_add, castCls_sum]
    simp only [cls_datumMul_source]
  · rw [ProductClasses.cls_add_mul, cls_sum_mul, castCls_add, castCls_sum]
    simp only [cls_datumMul_annular]

/-- A blowup of length one, multiplied on the left by a class, is a blowup of
length one of the product. -/
theorem step_mul_left {x y : Cls B (1 + k)} (z : Cls B l) (h : (1 + k) + l = 1 + K) (hs : Step x y) :
    Step (castCls h (z * x)) (castCls h (z * y)) := by
  rw [← ProductClasses.cls_mul_comm x z, ← ProductClasses.cls_mul_comm y z, castCls_castCls, castCls_castCls]
  exact step_mul_right z _ hs

theorem steps_mul_right {n : ℕ} {x y : Cls B (1 + k)} (z : Cls B l) (h : l + (1 + k) = 1 + K)
    (hs : BlowupSteps n x y) : BlowupSteps n (castCls h (x * z)) (castCls h (y * z)) :=
  Steps.map (fun x => castCls h (x * z)) (fun hxy => step_mul_right z h hxy) hs

theorem steps_mul_left {n : ℕ} {x y : Cls B (1 + k)} (z : Cls B l) (h : (1 + k) + l = 1 + K)
    (hs : BlowupSteps n x y) : BlowupSteps n (castCls h (z * x)) (castCls h (z * y)) :=
  Steps.map (fun x => castCls h (z * x)) (fun hxy => step_mul_left z h hxy) hs

/-- Lemma 7.10, product on the right: `μIsp^db` is compatible with right
multiplication by any class. -/
theorem muIsp_mul_right {x y : Cls B (1 + k)} (z : Cls B l) (h : l + (1 + k) = 1 + K) (hm : MuIsp x y) :
    MuIsp (castCls h (x * z)) (castCls h (y * z)) := by
  obtain ⟨w, m, n, hx, hy⟩ := hm
  exact ⟨castCls h (w * z), m, n, steps_mul_right z h hx, steps_mul_right z h hy⟩

/-- Lemma 7.10, product on the left: `μIsp^db` is compatible with left
multiplication by any class. -/
theorem muIsp_mul_left {x y : Cls B (1 + k)} (z : Cls B l) (h : (1 + k) + l = 1 + K) (hm : MuIsp x y) :
    MuIsp (castCls h (z * x)) (castCls h (z * y)) := by
  obtain ⟨w, m, n, hx, hy⟩ := hm
  exact ⟨castCls h (z * w), m, n, steps_mul_left z h hx, steps_mul_left z h hy⟩

/-- Products of `μIsp^db`-related pairs in positive degrees are related. -/
theorem muIsp_mul {k' : ℕ} {x y : Cls B (1 + k)} {x' y' : Cls B (1 + k')}
    (h : (1 + k') + (1 + k) = 1 + K) (hm : MuIsp x y) (hm' : MuIsp x' y') :
    MuIsp (castCls h (x * x')) (castCls h (y * y')) :=
  BlowupResults.muIsp_transitive (muIsp_mul_right x' h hm) (muIsp_mul_left y h hm')

end Congruence

/-- **Lemma 7.10 (`isp:congruence:vol`).** `μIsp^db[1+k]` is a congruence of the
additive monoid of isomorphism classes (`BlowupResults.lemma_7_10_addCon`), and
`μIsp^db[*]` is compatible with products on both sides: multiplying a
`μIsp^db`-related pair by any class `z` of degree `l`, on the right or on the
left, gives a `μIsp^db`-related pair, read in any degree `1 + K` equal to the
degree of the products. -/
theorem lemma_7_10 :
    (∀ {k : ℕ} (x y : Cls B (1 + k)), BlowupResults.lemma_7_10_addCon x y ↔ MuIsp x y) ∧
    (∀ {k l K : ℕ} (h : l + (1 + k) = 1 + K) (x y : Cls B (1 + k)) (z : Cls B l),
      MuIsp x y → MuIsp (castCls h (x * z)) (castCls h (y * z))) ∧
    (∀ {k l K : ℕ} (h : (1 + k) + l = 1 + K) (x y : Cls B (1 + k)) (z : Cls B l),
      MuIsp x y → MuIsp (castCls h (z * x)) (castCls h (z * y))) :=
  ⟨fun _ _ => Iff.rfl, fun h _ _ z hm => muIsp_mul_right z h hm, fun h _ _ z hm => muIsp_mul_left z h hm⟩

/-! ### The graded form: `μIsp^db[*]` in every degree -/

section Graded
variable {m l : ℕ}

theorem fiberwise_castCls {a b : ℕ} (e : a = b) (x : Cls B a) :
    FiberwiseInput.castCls e x = castCls e x := rfl

theorem ispRel_refl (x : Cls B m) : IspRel x x := by
  by_cases hm : m = 0
  · rw [IspRel, dite_eq_left hm]
  · rw [IspRel, dite_eq_right hm]
    exact muIsp_refl _

theorem ispRel_symm {x y : Cls B m} (h : IspRel x y) : IspRel y x := by
  by_cases hm : m = 0
  · rw [IspRel, dite_eq_left hm] at h ⊢
    exact h.symm
  · rw [IspRel, dite_eq_right hm] at h ⊢
    exact muIsp_symm h

theorem ispRel_trans {x y z : Cls B m} (h₁ : IspRel x y) (h₂ : IspRel y z) : IspRel x z := by
  by_cases hm : m = 0
  · rw [IspRel, dite_eq_left hm] at h₁ h₂ ⊢
    exact h₁.trans h₂
  · rw [IspRel, dite_eq_right hm] at h₁ h₂ ⊢
    exact BlowupResults.muIsp_transitive h₁ h₂

theorem eq_of_ispRel_zero {x y : Cls B m} (hm : m = 0) (h : IspRel x y) : x = y := by
  rw [IspRel, dite_eq_left hm] at h
  exact h

theorem ispRel_add {x y x' y' : Cls B m} (h : IspRel x y) (h' : IspRel x' y') : IspRel (x + x') (y + y') := by
  by_cases hm : m = 0
  · rw [eq_of_ispRel_zero hm h, eq_of_ispRel_zero hm h']
    exact ispRel_refl _
  · obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
    rw [ispRel_iff rfl] at h h' ⊢
    exact muIsp_add h h'

theorem ispRel_mul_right {x y : Cls B m} (z : Cls B l) (h : IspRel x y) : IspRel (x * z) (y * z) := by
  by_cases hm : m = 0
  · rw [eq_of_ispRel_zero hm h]
    exact ispRel_refl _
  · obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
    rw [ispRel_iff rfl] at h
    rw [ispRel_iff (show l + (1 + j) = 1 + (l + j) by omega), fiberwise_castCls, fiberwise_castCls]
    exact muIsp_mul_right z _ h

theorem ispRel_mul_left {x y : Cls B m} (z : Cls B l) (h : IspRel x y) : IspRel (z * x) (z * y) := by
  by_cases hm : m = 0
  · rw [eq_of_ispRel_zero hm h]
    exact ispRel_refl _
  · obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
    rw [ispRel_iff rfl] at h
    rw [ispRel_iff (show (1 + j) + l = 1 + (j + l) by omega), fiberwise_castCls, fiberwise_castCls]
    exact muIsp_mul_left z _ h

/-- Products of `μIsp^db`-related homogeneous classes of any degrees are
`μIsp^db`-related. -/
theorem ispRel_mul {x y : Cls B m} {x' y' : Cls B l} (h : IspRel x y) (h' : IspRel x' y') :
    IspRel (x * x') (y * y') :=
  ispRel_trans (ispRel_mul_right x' h) (ispRel_mul_left y h')

end Graded

/-- **Lemma 7.10 (`isp:congruence:vol`), graded form.** With `μIsp^db[0]` read
as equality of classes (`FiberwiseInput.IspRel`), `μIsp^db[m]` is an equivalence
relation compatible with sums in every degree `m`, and products of related
homogeneous classes of degrees `m` and `l` are related in degree `l + m`. This
is the statement that `μIsp^db[*]` is a semiring congruence on
`⨁ₘ K₊ μRV^db[m]`, checked on homogeneous elements. -/
theorem lemma_7_10_graded :
    (∀ {m : ℕ}, Equivalence (IspRel (B := B) (m := m))) ∧
    (∀ {m : ℕ} {x y x' y' : Cls B m}, IspRel x y → IspRel x' y' → IspRel (x + x') (y + y')) ∧
    (∀ {m l : ℕ} {x y : Cls B m} {x' y' : Cls B l}, IspRel x y → IspRel x' y' → IspRel (x * x') (y * y')) :=
  ⟨⟨ispRel_refl, ispRel_symm, ispRel_trans⟩, ispRel_add, ispRel_mul⟩

end DiamondIntegral.Section7.ProductBlowups
