import NumberFieldKB.WeilBNT.SUnits
import NumberFieldKB.MilneCFT.Ch5Ideles
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Weil, *Basic Number Theory*, VII.§8, Proposition 15: $k^\times G_P$ is dense in the ideles

$k$ is a number field (`K`). For a finite set $P$ of places containing the infinite ones, written $P=P_\infty\cup S$
with $S$ a finite set of finite places, $G_P$ is the group of ideles $(z_v)$ with $z_v=1$ for all $v\in P$
(`idelesOneAt S`).

* **Prop. 15** (p. 135): $k^\times G_P$ is dense in $k_{\mathbb A}^\times$ (`weil_VII_8_prop15`).
* **Text p. 135**: a continuous morphism of $k_{\mathbb A}^\times$ into a Hausdorff topological group, trivial on
  $k^\times$, is determined by its values on $G_P$ (`weil_VII_8_text135`).

*Proof* (Weil's): $k_{\mathbb A}^\times=k_P^\times\times G_P$ with $k_P=\prod_{v\in P}k_v$, and the assertion is that $k^\times$
projects onto a dense subgroup of $k_P^\times$; this holds because $k^\times_P$ is open in $k_P$ with the induced topology
and $k$ is dense in $k_P$ (weak approximation for finitely many places, which is what Weil's appeal to IV.§2 Cor. 2 of
Thm. 3 amounts to here).
-/

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-- Weil's $G_P$ for $P=P_\infty\cup S$: the ideles equal to $1$ at every infinite place and at every $v\in S$. -/
def idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {a | (a : AdeleRing (𝓞 K) K).1 = 1 ∧ ∀ v ∈ S, (a : AdeleRing (𝓞 K) K).2 v = 1}
  one_mem' := by
    exact ⟨rfl, fun v _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, fun v hv => ?_⟩
    · show (a : AdeleRing (𝓞 K) K).1 * (b : AdeleRing (𝓞 K) K).1 = 1
      rw [ha1, hb1, one_mul]
    · show (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v = 1
      rw [ha2 v hv, hb2 v hv, one_mul]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have h : (a : AdeleRing (𝓞 K) K) * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := a.mul_inv
    refine ⟨?_, fun v hv => ?_⟩
    · have h1 : (a : AdeleRing (𝓞 K) K).1 * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 :=
        congrArg Prod.fst h
      rwa [ha1, one_mul] at h1
    · have h1 : (a : AdeleRing (𝓞 K) K).2 v *
          ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
        congrArg (fun x : AdeleRing (𝓞 K) K => x.2 v) h
      rwa [ha2 v hv, one_mul] at h1

section Helpers

open NumberFieldKB.MilneCFT

/-- Weak approximation for all infinite places and finitely many finite places, with an arbitrary
precision at the infinite places (a variant of `NumberFieldKB.MilneCFT.exists_approx`). -/
theorem exists_approx_eps (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : HeightOneSpectrum (𝓞 K) → K) (δ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ))
    (hδ : ∀ v ∈ S, δ v ≠ 0) (q : InfinitePlace K → K) (ε : InfinitePlace K → ℝ) (hε : ∀ w, 0 < ε w) :
    ∃ b : K, (∀ v ∈ S, v.valuation K (b - c v) < δ v) ∧ ∀ w, w (b - q w) < ε w := by
  have hd := AbsoluteValue.denseRange_algebraMap_pi (approx_nontrivial S Finset.univ)
    (approx_pairwise S Finset.univ)
  let z : (i : S ⊕ (Finset.univ : Finset (InfinitePlace K))) → WithAbs (approxAbv S Finset.univ i) := fun i =>
    Sum.rec (fun v => WithAbs.toAbs _ (c v.1)) (fun w => WithAbs.toAbs _ (q w.1)) i
  let e : S ⊕ (Finset.univ : Finset (InfinitePlace K)) → ℝ :=
    Sum.elim (fun v => (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v.1) (δ v.1) : ℝ))
      (fun w => ε w.1)
  have hU : IsOpen (Set.pi Set.univ fun i => Metric.ball (z i) (e i)) :=
    isOpen_set_pi Set.finite_univ fun i _ => Metric.isOpen_ball
  have hne : (Set.pi Set.univ fun i => Metric.ball (z i) (e i)).Nonempty := by
    refine ⟨z, fun i _ => ?_⟩
    rw [Metric.mem_ball, dist_self]
    rcases i with v | w
    · exact_mod_cast WithZeroMulInt.toNNReal_pos _ (hδ v.1 v.2)
    · exact hε w.1
  obtain ⟨y, hmem⟩ := hd.exists_mem_open hU hne
  refine ⟨y, fun v hv => ?_, fun w => ?_⟩
  · have := hmem (Sum.inl ⟨v, hv⟩) (Set.mem_univ _)
    rw [Metric.mem_ball] at this
    rw [dist_eq_norm] at this
    change HeightOneSpectrum.adicAbv K v (y - c v) <
      ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (δ v) : NNReal) : ℝ) at this
    rw [HeightOneSpectrum.adicAbv_def] at this
    exact (WithZeroMulInt.toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal v)).lt_iff_lt.1
      (NNReal.coe_lt_coe.1 this)
  · have := hmem (Sum.inr ⟨w, Finset.mem_univ w⟩) (Set.mem_univ _)
    rw [Metric.mem_ball, dist_eq_norm] at this
    change w.1 (y - q w) < ε w at this
    exact this

/-- The product of the completions at all infinite places and at the places of `S`. -/
abbrev placeProd (S : Finset (HeightOneSpectrum (𝓞 K))) : Type :=
  (∀ w : InfinitePlace K, w.Completion) × (∀ v : S, (v.1).adicCompletion K)

/-- The diagonal embedding of `K` in `placeProd S`. -/
def pdiag (S : Finset (HeightOneSpectrum (𝓞 K))) (b : K) : placeProd S :=
  (fun w => (b : w.Completion), fun v => algebraMap K ((v.1).adicCompletion K) b)

omit [NumberField K] in
theorem norm_coe_completion (w : InfinitePlace K) (k : K) : ‖(k : w.Completion)‖ = w k := by
  have := InfinitePlace.Completion.norm_coe (v := w) ((WithAbs.equiv w.1).symm k)
  simpa using this

theorem denseRange_pdiag (S : Finset (HeightOneSpectrum (𝓞 K))) : DenseRange (pdiag (K := K) S) := by
  classical
  intro z
  rw [mem_closure_iff_nhds]
  intro N hN
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hN
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := hN
  rw [nhds_pi, Filter.mem_pi] at ht1 ht2
  obtain ⟨I1, -, s1, hs1, hI1⟩ := ht1
  obtain ⟨I2, -, s2, hs2, hI2⟩ := ht2
  have h1 : ∀ w : InfinitePlace K, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z.1 w) ε ⊆ s1 w := fun w => by
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 (hs1 w)
    exact ⟨ε, hε, h⟩
  choose ε hε hball using h1
  have h2 : ∀ v : S, ∃ γ : (WithZero (Multiplicative ℤ))ˣ,
      {y : (v.1).adicCompletion K | Valued.v (y - z.2 v) < γ} ⊆ s2 v := fun v => by
    obtain ⟨γ0, h⟩ := Valued.mem_nhds.1 (hs2 v)
    refine ⟨Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := ((Valued.v : Valuation ((v.1).adicCompletion K) (WithZero (Multiplicative ℤ))) :
        (v.1).adicCompletion K →*₀ WithZero (Multiplicative ℤ)))) γ0, fun y hy => h ?_⟩
    simpa [Valuation.restrict_lt_iff_lt_embedding] using hy
  choose γ hγ using h2
  have h3 : ∀ w : InfinitePlace K, ∃ q : K, dist (z.1 w) (q : w.Completion) < ε w / 2 := fun w => by
    have hd : DenseRange (fun x : K => (algebraMap K (InfiniteAdeleRing K) x) w) :=
      (Function.surjective_eval w).denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap K)
        (continuous_apply w)
    exact Metric.denseRange_iff.1 hd (z.1 w) (ε w / 2) (half_pos (hε w))
  choose q hq using h3
  have h4 : ∀ v : S, ∃ c : K, Valued.v (algebraMap K ((v.1).adicCompletion K) c - z.2 v) < γ v :=
    fun v => exists_close v.1 (z.2 v) (γ v) (Units.ne_zero _)
  choose c hc using h4
  obtain ⟨b, hb1, hb2⟩ := exists_approx_eps S (fun v => if h : v ∈ S then c ⟨v, h⟩ else 0)
    (fun v => if h : v ∈ S then (γ ⟨v, h⟩ : WithZero (Multiplicative ℤ)) else 1)
    (fun v hv => by simp [hv]) q (fun w => ε w / 2) (fun w => half_pos (hε w))
  refine ⟨pdiag S b, hsub ⟨hI1 ?_, hI2 ?_⟩, ⟨b, rfl⟩⟩
  · intro w _
    apply hball w
    rw [Metric.mem_ball]
    calc dist (b : w.Completion) (z.1 w) ≤ dist (b : w.Completion) (q w) + dist (q w : w.Completion) (z.1 w) :=
          dist_triangle _ _ _
      _ < ε w / 2 + ε w / 2 := by
          refine add_lt_add ?_ ?_
          · have hs : ((b - q w : K) : w.Completion) = (b : w.Completion) - (q w : w.Completion) :=
              map_sub (algebraMap K w.Completion) b (q w)
            rw [dist_eq_norm, ← hs, norm_coe_completion]
            exact hb2 w
          · rw [dist_comm]; exact hq w
      _ = ε w := by ring
  · intro v _
    apply hγ v
    show Valued.v (algebraMap K ((v.1).adicCompletion K) b - z.2 v) < γ v
    have h1 : Valued.v (algebraMap K ((v.1).adicCompletion K) (b - c v)) < γ v := by
      have e : Valued.v (algebraMap K ((v.1).adicCompletion K) (b - c v)) = v.1.valuation K (b - c v) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _
      rw [e]
      have := hb1 v.1 v.2
      simpa [v.2] using this
    have : algebraMap K ((v.1).adicCompletion K) b - z.2 v =
        algebraMap K ((v.1).adicCompletion K) (b - c v) +
          (algebraMap K ((v.1).adicCompletion K) (c v) - z.2 v) := by
      rw [map_sub]; ring
    rw [this]
    exact Valuation.map_add_lt _ h1 (hc v)

/-- The `P`-part of an idele: its components at the infinite places and at the places of `S`. -/
abbrev placeUnits (S : Finset (HeightOneSpectrum (𝓞 K))) : Type :=
  (∀ w : InfinitePlace K, (w.Completion)ˣ) × (∀ v : S, ((v.1).adicCompletion K)ˣ)

/-- Component of an idele at an infinite place, as a unit. -/
def pinf (w : InfinitePlace K) : IdeleGroup (𝓞 K) K →* (w.Completion)ˣ :=
  Units.map ((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) :
      AdeleRing (𝓞 K) K →+* w.Completion).toMonoidHom

/-- Component of an idele at a finite place, as a unit. -/
def pfin (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup (𝓞 K) K →* (v.adicCompletion K)ˣ :=
  Units.map ((RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) v).comp
    (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) :
      AdeleRing (𝓞 K) K →+* v.adicCompletion K).toMonoidHom

/-- The projection of ideles onto their `P`-part. -/
def pproj (S : Finset (HeightOneSpectrum (𝓞 K))) : IdeleGroup (𝓞 K) K →* placeUnits S :=
  (MonoidHom.pi fun w : InfinitePlace K => pinf w).prod (MonoidHom.pi fun v : S => pfin (K := K) v.1)

theorem continuous_pproj (S : Finset (HeightOneSpectrum (𝓞 K))) : Continuous (pproj (K := K) S) := by
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun v => ?_)
  · refine Continuous.units_map _ ?_
    exact (continuous_apply w).comp continuous_fst
  · refine Continuous.units_map _ ?_
    exact (RestrictedProduct.continuous_eval v.1).comp continuous_snd

/-- The section of `pproj`: put the given local unit at each place of `P` and `1` elsewhere. -/
def psect (S : Finset (HeightOneSpectrum (𝓞 K))) : placeUnits S →* IdeleGroup (𝓞 K) K where
  toFun c := (∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (c.1 w)) *
    ∏ v : S, IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 (c.2 v)
  map_one' := by simp
  map_mul' c d := by
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

theorem continuous_psect (S : Finset (HeightOneSpectrum (𝓞 K))) : Continuous (psect (K := K) S) := by
  refine Continuous.mul (continuous_finsetProd _ fun w _ => ?_) (continuous_finsetProd _ fun v _ => ?_)
  · exact (NumberFieldKB.MilneCFT.item_4_3.2 w).continuous.comp ((continuous_apply w).comp continuous_fst)
  · exact (NumberFieldKB.MilneCFT.item_4_3.1 v.1).continuous.comp ((continuous_apply v).comp continuous_snd)

theorem pproj_psect (S : Finset (HeightOneSpectrum (𝓞 K))) (c : placeUnits S) : pproj S (psect S c) = c := by
  let _ := Classical.decEq (InfinitePlace K)
  let _ := Classical.decEq (HeightOneSpectrum (𝓞 K))
  have key1 : ∀ (c : placeUnits S) (w : InfinitePlace K), ((psect S c : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K).1 w = (c.1 w : w.Completion) := by
    intro c w
    let f : AdeleRing (𝓞 K) K →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
    show f ((((∏ w', IdeleGroup.ofCompletion (𝓞 K) K w' (c.1 w')) *
      ∏ v : S, IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 (c.2 v) : IdeleGroup (𝓞 K) K)) :
        AdeleRing (𝓞 K) K) = _
    rw [Units.val_mul, Units.coe_prod, Units.coe_prod, map_mul, map_prod, map_prod]
    have h2 : ∀ v : S, f ((IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 (c.2 v) : IdeleGroup (𝓞 K) K) :
        AdeleRing (𝓞 K) K) = 1 := fun v => rfl
    simp only [h2, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single w]
    · show (Pi.mulSingle w ((c.1 w : (w.Completion)ˣ) : w.Completion) : InfiniteAdeleRing K) w = _
      exact Pi.mulSingle_eq_same w _
    · intro i _ hi
      show (Pi.mulSingle i ((c.1 i : (i.Completion)ˣ) : i.Completion) : InfiniteAdeleRing K) w = 1
      exact Pi.mulSingle_eq_of_ne (Ne.symm hi) _
    · intro h; exact absurd (Finset.mem_univ w) h
  have key2 : ∀ (c : placeUnits S) (v : S), ((psect S c : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K).2 v = (c.2 v : (v.1).adicCompletion K) := by
    intro c v
    let f : AdeleRing (𝓞 K) K →+* (v.1).adicCompletion K :=
      (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) v.1).comp
        (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
    show f ((((∏ w', IdeleGroup.ofCompletion (𝓞 K) K w' (c.1 w')) *
      ∏ v : S, IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 (c.2 v) : IdeleGroup (𝓞 K) K)) :
        AdeleRing (𝓞 K) K) = _
    rw [Units.val_mul, Units.coe_prod, Units.coe_prod, map_mul, map_prod, map_prod]
    have h2 : ∀ w : InfinitePlace K, f ((IdeleGroup.ofCompletion (𝓞 K) K w (c.1 w) : IdeleGroup (𝓞 K) K) :
        AdeleRing (𝓞 K) K) = 1 := fun w => rfl
    simp only [h2, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single v]
    · show ((Pi.mulSingle v.1 ((c.2 v : ((v.1).adicCompletion K)ˣ) : (v.1).adicCompletion K) :
        ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)) v.1 = _
      exact Pi.mulSingle_eq_same v.1 _
    · intro i _ hi
      show ((Pi.mulSingle i.1 ((c.2 i : ((i.1).adicCompletion K)ˣ) : (i.1).adicCompletion K) :
        ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)) v.1 = 1
      exact Pi.mulSingle_eq_of_ne (fun h => hi (Subtype.ext h.symm)) _
    · intro h; exact absurd (Finset.mem_univ v) h
  refine Prod.ext (funext fun w => Units.ext ?_) (funext fun v => Units.ext ?_)
  · exact key1 c w
  · exact key2 c v

theorem mem_idelesOneAt_of_pproj_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) {x : IdeleGroup (𝓞 K) K}
    (h : pproj S x = 1) : x ∈ idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))) := by
  refine ⟨funext fun w => ?_, fun v hv => ?_⟩
  · exact congrArg (fun p : placeUnits S => ((p.1 w : (w.Completion)ˣ) : w.Completion)) h
  · exact congrArg (fun p : placeUnits S => ((p.2 ⟨v, hv⟩ : ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ) :
      (v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) h

theorem exists_unit_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Set (placeUnits S)) (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ ξ : Kˣ, pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ) ∈ W := by
  let e : placeUnits S → placeProd S := fun t => (fun w => (t.1 w : w.Completion), fun v => (t.2 v : (v.1).adicCompletion K))
  have he : Topology.IsOpenEmbedding e :=
    (Topology.IsOpenEmbedding.piMap fun w : InfinitePlace K => Units.isOpenEmbedding_val).prodMap
      (Topology.IsOpenEmbedding.piMap fun v : S => Units.isOpenEmbedding_val)
  obtain ⟨b, t, htW, hty⟩ := (denseRange_pdiag S).exists_mem_open (he.isOpenMap _ hW) (hne.image e)
  have hb : b ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have h1 : ((t.1 w : (w.Completion)ˣ) : w.Completion) = ((0 : K) : w.Completion) :=
      congrFun (congrArg Prod.fst hty) w
    rw [InfinitePlace.Completion.coe_zero] at h1
    exact (t.1 w).ne_zero h1
  refine ⟨Units.mk0 b hb, ?_⟩
  have : pproj S (IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 b hb)) = t := by
    apply he.injective
    exact hty.symm
  rw [this]; exact htW

end Helpers

/-- **Weil, VII.§8, Proposition 15** (p. 135): for $P=P_\infty\cup S$ with $S$ a finite set of finite places,
$k^\times G_P$ is dense in $k_{\mathbb A}^\times$. -/
@[kb "weil1973bnt" "Ch. VII, §8, Prop. 15 (p. 135), number field case"]
theorem weil_VII_8_prop15 (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Dense {x : IdeleGroup (𝓞 K) K |
      ∃ ξ : Kˣ, ∃ g ∈ idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))),
        x = IdeleGroup.unitEmbedding (𝓞 K) K ξ * g} := by
  intro a
  rw [mem_closure_iff]
  intro U hU haU
  set a' : IdeleGroup (𝓞 K) K := (psect S (pproj S a))⁻¹ * a with ha'
  have ha'G : a' ∈ idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))) := by
    apply mem_idelesOneAt_of_pproj_eq_one
    rw [ha', map_mul, map_inv, pproj_psect, inv_mul_cancel]
  have hφ : Continuous fun c : placeUnits S => psect S c * a' := (continuous_psect S).mul continuous_const
  have hV : IsOpen ((fun c : placeUnits S => psect S c * a') ⁻¹' U) := hU.preimage hφ
  have hmem : pproj S a ∈ (fun c : placeUnits S => psect S c * a') ⁻¹' U := by
    show psect S (pproj S a) * a' ∈ U
    rw [ha', mul_inv_cancel_left]; exact haU
  obtain ⟨ξ, hξ⟩ := exists_unit_mem S _ hV ⟨_, hmem⟩
  set ξ' : IdeleGroup (𝓞 K) K := (psect S (pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ)))⁻¹ *
    IdeleGroup.unitEmbedding (𝓞 K) K ξ with hξ'
  have hξ'G : ξ' ∈ idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))) := by
    apply mem_idelesOneAt_of_pproj_eq_one
    rw [hξ', map_mul, map_inv, pproj_psect, inv_mul_cancel]
  refine ⟨IdeleGroup.unitEmbedding (𝓞 K) K ξ * (ξ'⁻¹ * a'), ?_, ξ, ξ'⁻¹ * a', ?_, rfl⟩
  · have : IdeleGroup.unitEmbedding (𝓞 K) K ξ * (ξ'⁻¹ * a') =
        psect S (pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ)) * a' := by
      rw [hξ']; group
    rw [this]; exact hξ
  · exact mul_mem (inv_mem hξ'G) ha'G

/-- **Weil, VII.§8, text p. 135**: two continuous morphisms of $k_{\mathbb A}^\times$ into a Hausdorff topological
group, trivial on $k^\times$ and equal on $G_P$, are equal. -/
@[kb "weil1973bnt" "Ch. VII, §8, text p. 135 (determined by values on G_P), number field case"]
theorem weil_VII_8_text135 {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ω ω' : IdeleGroup (𝓞 K) K →* Γ) (hω : Continuous ω)
    (hω' : Continuous ω') (hk : ∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1)
    (hk' : ∀ ξ : Kˣ, ω' (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1)
    (hG : ∀ g ∈ idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))), ω g = ω' g) : ω = ω' := by
  refine DFunLike.ext _ _ fun x => ?_
  have hd := weil_VII_8_prop15 S
  have h : Set.EqOn ω ω' {x : IdeleGroup (𝓞 K) K |
      ∃ ξ : Kˣ, ∃ g ∈ idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))),
        x = IdeleGroup.unitEmbedding (𝓞 K) K ξ * g} := by
    rintro y ⟨ξ, g, hg, rfl⟩
    rw [map_mul, map_mul, hk ξ, hk' ξ, one_mul, one_mul]
    exact hG g hg
  exact congrFun (hω.ext_on hd hω' h) x

end NumberFieldKB.WeilBNT
