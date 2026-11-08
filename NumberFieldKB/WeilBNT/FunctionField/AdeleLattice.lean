import NumberFieldKB.WeilBNT.FunctionField.AdeleVolume

/-!
# Products of lattices in $k_{\mathbb A}$ (Weil VI.§1, Prop. 1, $E=k$)

For $E=k$ a $k_v$-lattice in $k_v$ is $\mathfrak p_v^{-n_v}$, $n_v\in\mathbb Z$. For any family $n=(n_v)$ let
`FFAdeleRing.Ufam n` be the set of adeles with $v(x_v)\le e^{n_v}$ for all $v$, i.e. $k_{\mathbb A}\cap\prod_v
\mathfrak p_v^{-n_v}$.

* **`FFAdeleRing.weil_VI_1_prop1_open`**: it is open iff $\mathfrak p_v^{-n_v}\supseteq\mathfrak r_v$ for almost all
  $v$ ($n_v\ge0$ a.e.);
* **`FFAdeleRing.weil_VI_1_prop1_compact`**: if $\mathfrak p_v^{-n_v}\subseteq\mathfrak r_v$ for almost all $v$
  ($n_v\le0$ a.e., i.e. $\prod_v\mathfrak p_v^{-n_v}\subseteq k_{\mathbb A}$), it is compact; in particular
* **`FFAdeleRing.weil_VI_1_prop1`**: for a family with $\prod_v\mathfrak p_v^{-n_v}\subseteq k_{\mathbb A}$, the product
  is open and compact iff $n_v=0$ for almost all $v$ (Weil VI.§1, Prop. 1 for $E=k$, basis $\{1\}$).
Compactness of every $U(\mathfrak a)$ is `FFAdeleRing.isCompact_U` (`AdeleVolume.lean`).
-/

open scoped WithZero RestrictedProduct Pointwise
open Valuation IsDedekindDomain Topology Filter

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFAdeleRing

/-- $k_{\mathbb A}\cap\prod_v\mathfrak p_v^{-n_v}$ for an arbitrary family $n$ of integers. -/
def Ufam (n : Place Fq k → ℤ) : AddSubgroup (FFAdeleRing Fq k) where
  carrier := {x | ∀ v : Place Fq k, Valued.v (x v) ≤ WithZero.exp (n v)}
  zero_mem' := fun v => by simp
  add_mem' {x y} hx hy := fun v => by
    show Valued.v (x v + y v) ≤ _
    exact (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))
  neg_mem' {x} hx := fun v => by
    show Valued.v (-(x v)) ≤ _
    rw [Valuation.map_neg]; exact hx v

theorem mem_Ufam_iff (n : Place Fq k → ℤ) (x : FFAdeleRing Fq k) :
    x ∈ Ufam n ↔ ∀ v : Place Fq k, Valued.v (x v) ≤ WithZero.exp (n v) := Iff.rfl

theorem isClosed_Ufam (n : Place Fq k → ℤ) : IsClosed (Ufam n : Set (FFAdeleRing Fq k)) := by
  have : (Ufam n : Set (FFAdeleRing Fq k)) =
      ⋂ v, (fun x : FFAdeleRing Fq k => x v) ⁻¹' {y | Valued.v y ≤ WithZero.exp (n v)} := by
    ext x; simp [mem_Ufam_iff]
  rw [this]
  refine isClosed_iInter fun v => ?_
  refine IsClosed.preimage (RestrictedProduct.continuous_eval v) ?_
  -- an open subgroup is closed
  let H : AddSubgroup v.Completion :=
    { carrier := {y | Valued.v y ≤ WithZero.exp (n v)}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => show Valued.v (a + b) ≤ _ from
        (Valuation.map_add _ _ _).trans (max_le ha hb)
      neg_mem' := fun {a} ha => by simpa [Valuation.map_neg] using ha }
  exact AddSubgroup.isClosed_of_isOpen H (Place.isOpen_valued_le v (n v))

/-- **Weil VI.§1, Prop. 1** ($E=k$), openness: $\prod_v\mathfrak p_v^{-n_v}\cap k_{\mathbb A}$ is open iff
$\mathfrak p_v^{-n_v}\supseteq\mathfrak r_v$ for almost all $v$. -/
theorem weil_VI_1_prop1_open (n : Place Fq k → ℤ) :
    IsOpen (Ufam n : Set (FFAdeleRing Fq k)) ↔ ∀ᶠ v in cofinite, 0 ≤ n v := by
  classical
  constructor
  · intro hO
    -- a neighbourhood of 0 contains all adeles that are integral and small at finitely many places
    have h0 : (Ufam n : Set (FFAdeleRing Fq k)) ∈ 𝓝 (0 : FFAdeleRing Fq k) := hO.mem_nhds (Ufam n).zero_mem
    have hz : (0 : FFAdeleRing Fq k) = RestrictedProduct.structureMap _ _ cofinite
        (0 : ∀ v : Place Fq k, (v.completionIntegers : Set v.Completion)) := rfl
    rw [hz, RestrictedProduct.nhds_eq_map_structureMap (fun v => Valued.isOpen_valuationSubring v.Completion),
      Filter.mem_map, nhds_pi, Filter.mem_pi] at h0
    obtain ⟨I, hI, t, ht, hsub⟩ := h0
    refine hI.eventually_cofinite_notMem.mono fun v hv => ?_
    by_contra hneg
    push Not at hneg
    -- the adele `1` at `v`, `0` elsewhere
    let x : ∀ w : Place Fq k, (w.completionIntegers : Set w.Completion) :=
      fun w => if h : w = v then ⟨1, by subst h; exact w.completionIntegers.one_mem⟩ else 0
    have hx : x ∈ Set.pi I t := by
      intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      simp only [x, dif_neg hwv]
      exact mem_of_mem_nhds (ht w)
    have := hsub hx
    have hv1 : Valued.v (1 : v.Completion) ≤ WithZero.exp (n v) := by
      have := this v
      simpa [x, RestrictedProduct.structureMap] using this
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv1
    omega
  · intro h
    have hfin : {v | ¬ 0 ≤ n v}.Finite := Filter.eventually_cofinite.1 h
    let b : Divisor Fq k := Finsupp.ofSupportFinite (fun v => min (n v) 0) (by
      refine hfin.subset fun v hv => ?_
      simp only [Function.mem_support, ne_eq] at hv
      simp only [Set.mem_ofPred_eq, not_le]
      omega)
    have hle : U b ≤ Ufam n := fun x hx v => by
      refine (hx v).trans (WithZero.exp_le_exp.2 ?_)
      show min (n v) 0 ≤ n v
      exact min_le_left _ _
    exact AddSubgroup.isOpen_mono hle (isOpen_U b)

/-- **Weil VI.§1, Prop. 1** ($E=k$), compactness: if $\mathfrak p_v^{-n_v}\subseteq\mathfrak r_v$ for almost all $v$,
then $\prod_v\mathfrak p_v^{-n_v}$ is compact. -/
theorem weil_VI_1_prop1_compact (n : Place Fq k → ℤ) (h : ∀ᶠ v in cofinite, n v ≤ 0) :
    IsCompact (Ufam n : Set (FFAdeleRing Fq k)) := by
  have hfin : {v | ¬ n v ≤ 0}.Finite := Filter.eventually_cofinite.1 h
  let a : Divisor Fq k := Finsupp.ofSupportFinite (fun v => max (n v) 0) (by
    refine hfin.subset fun v hv => ?_
    simp only [Function.mem_support, ne_eq] at hv
    simp only [Set.mem_ofPred_eq, not_le]
    omega)
  have hle : (Ufam n : Set (FFAdeleRing Fq k)) ⊆ U a := fun x hx v => by
    refine (hx v).trans (WithZero.exp_le_exp.2 ?_)
    show n v ≤ max (n v) 0
    exact le_max_left _ _
  exact (isCompact_U a).of_isClosed_subset (isClosed_Ufam n) hle

/-- **Weil VI.§1, Prop. 1** ($E=k$, basis $\{1\}$): for a family of lattices $\mathfrak p_v^{-n_v}$ with
$\prod_v\mathfrak p_v^{-n_v}\subseteq k_{\mathbb A}$ (i.e. $n_v\le0$ for almost all $v$), the product is open and compact
iff $\mathfrak p_v^{-n_v}=\mathfrak r_v$ for almost all $v$. -/
@[kb "weil1973bnt" "Ch. VI, §1, Prop. 1 (p. 97), E = k"]
theorem weil_VI_1_prop1 (n : Place Fq k → ℤ) (h : ∀ᶠ v in cofinite, n v ≤ 0) :
    (IsOpen (Ufam n : Set (FFAdeleRing Fq k)) ∧ IsCompact (Ufam n : Set (FFAdeleRing Fq k))) ↔
      ∀ᶠ v in cofinite, n v = 0 := by
  constructor
  · rintro ⟨hO, -⟩
    filter_upwards [(weil_VI_1_prop1_open n).1 hO, h] with v h1 h2
    omega
  · intro h0
    refine ⟨(weil_VI_1_prop1_open n).2 (h0.mono fun v hv => hv.ge), weil_VI_1_prop1_compact n h⟩

end FFAdeleRing

end NumberFieldKB.WeilBNT.FF
