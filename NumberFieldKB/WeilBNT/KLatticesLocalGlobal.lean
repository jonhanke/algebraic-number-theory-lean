import NumberFieldKB.WeilBNT.KLattices

/-!
# Weil, *Basic Number Theory*, V.§2, Theorem 2 and its Corollary: $k$-lattices are determined place by place

$k$ is a number field (`K`), $\mathfrak r$ its ring of integers, $E=k^n$ (a basis identifies Weil's $E$ with $k^n$),
and $v$ runs over the finite places. `IsKLattice`, `localLattice L v` ($L_v$) and Prop. 4 are in `KLattices.lean`.

* **II.§2, Def. 2** (p. 28): a $k_v$-lattice in $E_v=k_v^n$ is a compact and open $r_v$-module (`IsLocalLattice`).
  $L_v$ is one for every $k$-lattice $L$ (`isLocalLattice_localLattice`).
* `globalOfLocal M` is Weil's $\bigcap_v(E\cap M_v)$.
* **Thm. 2** (p. 84): for a $k$-lattice $L$ and $k_v$-lattices $M_v$, there is a $k$-lattice $M$ with closure $M_v$ in
  $E_v$ for every $v$ iff $M_v=L_v$ for almost all $v$ (`weil_V_2_thm2`); then $M=\bigcap_v(E\cap M_v)$ is such a lattice
  (`weil_V_2_thm2_exists`) and is the only one (`weil_V_2_thm2_unique`). In particular $L=\bigcap_v(E\cap L_v)$
  (`globalOfLocal_localLattice`).
* **Corollary** (p. 85): $L+L'$ and $L\cap L'$ are $k$-lattices with closures $L_v+L'_v$ and $L_v\cap L'_v$
  (`weil_V_2_thm2_cor_sup`, `weil_V_2_thm2_cor_inf`); the intersection is done by Weil's argument through Thm. 2.

*Proof.* "Only if" (Weil: Cor. 1 of III.1 Thm. 3): $dL\subset M$ and $d'M\subset L$ for integers $d,d'>0$
(`exists_nat_smul_mem`, the $\mathfrak r$-module form of V.§1 Prop. 1), so $L_v=M_v$ wherever $dd'$ is a unit.
Uniqueness is Weil's argument verbatim: $M'\subset M$, $mM\subset M'$, and the density of $M'$ in $\prod_vM_v$ (Prop. 4)
gives, for $\mu\in M$, some $\mu'\in M'$ with $\mu-\mu'\in mM\subset M'$ (`eq_globalOfLocal`).
Existence departs from Weil in one point. Weil gets that $M$ is finitely generated from V.§2 Lemma 1 and its density
in $\prod_vM_v$ from IV.§2 Cor. 2 of Thm. 3 (strong approximation, not available here). Instead: $DM\subset\mathfrak r^n$
for an integer $D$ (a compact $M_v$ is brought into $r_v^n$ by a power of the norm of $v$, and an element of $k$ integral
at every finite place is in $\mathfrak r$), so $M$ is finitely generated; $CL\subset M$ (the open $M_v$ absorbs the
compact $L_v$), so $M$ contains a basis; and density comes from Prop. 4 applied to the auxiliary lattice $c^{-1}L$,
whose closures contain every $M_w$ and lie in $M_w$ outside a finite set (`globalOfLocal_spec`).
-/

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/-! ### `toLocal` is additive and $k$-semilinear -/

theorem coe_eq_algebraMap (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (x : v.adicCompletion K) = algebraMap K (v.adicCompletion K) x := rfl

theorem toLocal_add (v : HeightOneSpectrum (𝓞 K)) (x y : Fin n → K) :
    toLocal v (x + y) = toLocal v x + toLocal v y := by
  funext i; exact map_add (algebraMap K (v.adicCompletion K)) (x i) (y i)

theorem toLocal_zero (v : HeightOneSpectrum (𝓞 K)) : toLocal v (0 : Fin n → K) = 0 := by
  funext i; exact map_zero (algebraMap K (v.adicCompletion K))

theorem toLocal_sub (v : HeightOneSpectrum (𝓞 K)) (x y : Fin n → K) :
    toLocal v (x - y) = toLocal v x - toLocal v y := by
  funext i; exact map_sub (algebraMap K (v.adicCompletion K)) (x i) (y i)

theorem toLocal_smul (v : HeightOneSpectrum (𝓞 K)) (a : K) (x : Fin n → K) :
    toLocal v (a • x) = (a : v.adicCompletion K) • toLocal v x := by
  funext i; exact map_mul (algebraMap K (v.adicCompletion K)) a (x i)

theorem toLocal_nsmul (v : HeightOneSpectrum (𝓞 K)) (d : ℕ) (x : Fin n → K) :
    toLocal v (d • x) = d • toLocal v x := by
  funext i; exact map_nsmul (algebraMap K (v.adicCompletion K)) d (x i)

theorem toLocal_osmul (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (x : Fin n → K) :
    toLocal v (a • x) = (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) • toLocal v x := by
  have h1 : a • x = ((a : K)) • x := rfl
  rw [h1, toLocal_smul]
  rfl

/-! ### Units at a place -/

/-- The $v$-adic valuation of a natural number prime to $v$ is $1$. -/
theorem valued_natCast_eq_one {v : HeightOneSpectrum (𝓞 K)} {d : ℕ} (hd : (d : 𝓞 K) ∉ v.asIdeal) :
    Valued.v (d : v.adicCompletion K) = 1 := by
  have h1 : (d : v.adicCompletion K) = ((d : K) : v.adicCompletion K) :=
    (map_natCast (algebraMap K (v.adicCompletion K)) d).symm
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have : ((d : K)) = algebraMap (𝓞 K) K (d : 𝓞 K) := by simp
  rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hd

/-- If $d$ is prime to $v$, an $r_v$-module is stable under division by $d$. -/
theorem mem_of_nsmul_mem {v : HeightOneSpectrum (𝓞 K)} {d : ℕ} (hd : (d : 𝓞 K) ∉ v.asIdeal)
    (N : Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)) {y : Fin n → v.adicCompletion K}
    (hy : d • y ∈ N) : y ∈ N := by
  have h0 : (d : v.adicCompletion K) ≠ 0 := by
    intro h; have := valued_natCast_eq_one hd; rw [h] at this; simp at this
  have hinv : ((d : v.adicCompletion K))⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one hd, inv_one]
  have hy' : (⟨_, hinv⟩ : v.adicCompletionIntegers K) • (d • y) = y := by
    show ((d : v.adicCompletion K))⁻¹ • (d • y) = y
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion K), smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [← hy']
  exact N.smul_mem _ hy

/-- Only finitely many places divide a nonzero natural number. -/
theorem finite_natCast_mem {d : ℕ} (hd : d ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (d : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {(d : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hd
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact hv

/-! ### Comparison of $k$-lattices (Weil, V.§1, Prop. 1, for $\mathfrak r$-modules) -/

/-- A finite family of elements of $k$ has a common denominator in $\mathbf N$. -/
theorem exists_nat_mul_integral {ι : Type} [Fintype ι] (c : ι → K) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ i, ∃ a : 𝓞 K, (a : K) = (d : K) * c i := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.mpr hy0, fun i => ?_⟩
  have hi := hy (c i) (Finset.mem_image_of_mem c (Finset.mem_univ i))
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with h | h
  · refine ⟨⟨_, hi⟩, ?_⟩
    show (y : K) * c i = _
    conv_lhs => rw [h]
    simp
  · refine ⟨-⟨_, hi⟩, ?_⟩
    show -((y : K) * c i) = _
    conv_lhs => rw [h]
    simp

/-- **Weil, V.§1, Prop. 1** in the form used in V.§2: if $L$ is a $k$-lattice and $L'$ a finitely generated
$\mathfrak r$-module in $k^n$, then $dL'\subset L$ for some integer $d>0$. -/
theorem exists_nat_smul_mem {L L' : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L) (hL' : L'.FG) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ x ∈ L', d • x ∈ L := by
  obtain ⟨b, hb⟩ := hL.2
  obtain ⟨m, g, hg⟩ := exists_gen_family hL'
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_integral (fun p : Fin m × Fin n => b.repr (g p.1) p.2)
  refine ⟨d, hd0, fun x hx => ?_⟩
  have hgen : ∀ j, d • g j ∈ L := by
    intro j
    rw [← b.sum_repr (g j), Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hd (j, i)
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← ha]
    exact L.smul_mem a (hb i)
  rw [← hg] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hgen j
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem a hx

/-- Scaling passes to the local lattices: if $dL\subset L'$ then $dL_v\subset L'_v$. -/
theorem localLattice_nsmul {L L' : Submodule (𝓞 K) (Fin n → K)} {d : ℕ} (h : ∀ x ∈ L, d • x ∈ L')
    (v : HeightOneSpectrum (𝓞 K)) {y : Fin n → v.adicCompletion K} (hy : y ∈ localLattice L v) :
    d • y ∈ localLattice L' v := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← toLocal_nsmul]
    exact toLocal_mem_localLattice L' v ⟨_, h x hx⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

/-! ### The standard lattice $\mathfrak r^n$ and its completions $r_v^n$ -/

variable (K n) in
/-- The standard lattice $\mathfrak r^n\subset k^n$. -/
def intVec : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))

omit [NumberField K] in
theorem isKLattice_intVec : IsKLattice K n (intVec K n) :=
  ⟨Submodule.fg_span (Set.finite_range _), Pi.basisFun K (Fin n), fun i => by
    rw [Pi.basisFun_apply]; exact Submodule.subset_span ⟨i, rfl⟩⟩

omit [NumberField K] in
theorem mem_intVec_iff (x : Fin n → K) : x ∈ intVec K n ↔ ∀ i, ∃ a : 𝓞 K, (a : K) = x i := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hij]⟩
    | zero => exact fun i => ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i; obtain ⟨a, ha⟩ := hx i; obtain ⟨b, hb⟩ := hy i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul c x _ hx =>
      intro i; obtain ⟨a, ha⟩ := hx i
      exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩
  · intro h
    choose a ha using h
    have hx : x = ∑ i, a i • (Pi.single i 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- An element of $\mathfrak r$ lies in $r_v$. -/
theorem coe_integer_mem (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    ((a : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have : (a : K) = algebraMap (𝓞 K) K a := rfl
  rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one v a

/-- $r_v^n$, as a set of vectors. -/
def intLocal (v : HeightOneSpectrum (𝓞 K)) : Set (Fin n → v.adicCompletion K) :=
  {y | ∀ i, y i ∈ v.adicCompletionIntegers K}

theorem isOpen_intLocal (v : HeightOneSpectrum (𝓞 K)) : IsOpen (intLocal (n := n) v) := by
  have : intLocal (n := n) v =
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
    ext y; simp [intLocal]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

theorem nsmul_mem_intLocal {v : HeightOneSpectrum (𝓞 K)} {y : Fin n → v.adicCompletion K}
    (hy : y ∈ intLocal v) (m : ℕ) : m • y ∈ intLocal v := fun i => by
  simpa using nsmul_mem (hy i) m

/-- If the coordinates of every element of $L$ are integral, $L_v\subset r_v^n$. -/
theorem localLattice_subset_intLocal {L : Submodule (𝓞 K) (Fin n → K)} (h : L ≤ intVec K n)
    (v : HeightOneSpectrum (𝓞 K)) {y : Fin n → v.adicCompletion K} (hy : y ∈ localLattice L v) :
    y ∈ intLocal v := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    intro i
    obtain ⟨a, ha⟩ := (mem_intVec_iff x).mp (h hx) i
    show ((x i : K) : v.adicCompletion K) ∈ _
    rw [← ha]; exact coe_integer_mem v a
  | zero => intro i; exact (v.adicCompletionIntegers K).zero_mem
  | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
  | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)

/-- A vector of $k^n$ whose image in $E_v$ lies in $r_v^n$ for every $v$ lies in $\mathfrak r^n$. -/
theorem mem_intVec_of_local {x : Fin n → K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), toLocal v x ∈ intLocal v) : x ∈ intVec K n := by
  rw [mem_intVec_iff]
  intro i
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x i) ≤ 1 := by
    intro v
    have := h v i
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    simpa only [toLocal, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using this
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (x i) hv
  exact ⟨a, ha⟩

/-! ### Compact sets are brought into open modules by an integer -/

/-- For $C$ compact and $U$ an open set containing $0$ and stable under multiplication by integers,
$dC\subset U$ for some integer $d>0$ (take $d$ a power of the norm of $v$). -/
theorem exists_nat_smul_subset (v : HeightOneSpectrum (𝓞 K)) {C : Set (Fin n → v.adicCompletion K)}
    (hC : IsCompact C) {U : Set (Fin n → v.adicCompletion K)} (hU : IsOpen U) (h0 : (0 : Fin n → _) ∈ U)
    (hUs : ∀ y ∈ U, ∀ m : ℕ, m • y ∈ U) : ∃ d : ℕ, d ≠ 0 ∧ ∀ y ∈ C, d • y ∈ U := by
  set p : ℕ := Ideal.absNorm v.asIdeal with hp
  have hp0 : p ≠ 0 := by have := HeightOneSpectrum.one_lt_absNorm v; omega
  have hlt : ‖(p : v.adicCompletion K)‖ < 1 := by
    have h1 := (FinitePlace.norm_lt_one_iff_mem K v (p : 𝓞 K)).mpr (Ideal.absNorm_mem v.asIdeal)
    simpa [FinitePlace.embedding_apply] using h1
  let W : ℕ → Set (Fin n → v.adicCompletion K) := fun j => {y | ((p : v.adicCompletion K) ^ j) • y ∈ U}
  have hW : ∀ j, IsOpen (W j) := fun j => hU.preimage (continuous_const_smul _)
  have hcover : C ⊆ ⋃ j, W j := by
    intro y _
    have ht : Tendsto (fun j : ℕ => ((p : v.adicCompletion K) ^ j) • y) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).smul_const y
    obtain ⟨j, hj⟩ := (ht.eventually (hU.mem_nhds h0)).exists
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have hmono : Monotone W := by
    intro j j' hjj' y hy
    have : ((p : v.adicCompletion K) ^ j') • y = (p ^ (j' - j)) • (((p : v.adicCompletion K) ^ j) • y) := by
      rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion K), smul_smul, Nat.cast_pow, ← pow_add,
        Nat.sub_add_cancel hjj']
    show _ ∈ U
    rw [this]; exact hUs _ hy _
  obtain ⟨j, hj⟩ := hC.elim_directed_cover W hW hcover hmono.directed_le
  refine ⟨p ^ j, pow_ne_zero _ hp0, fun y hy => ?_⟩
  have := hj hy
  simpa [W, ← Nat.cast_smul_eq_nsmul (v.adicCompletion K)] using this

/-! ### Local lattices (Weil, II.§2, Def. 2) -/

/-- **Weil, II.§2, Definition 2** ($V=k_v^n$): a $k_v$-lattice in $k_v^n$ is a compact and open
$r_v$-module. -/
def IsLocalLattice (v : HeightOneSpectrum (𝓞 K))
    (M : Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)) : Prop :=
  IsCompact (M : Set (Fin n → v.adicCompletion K)) ∧ IsOpen (M : Set (Fin n → v.adicCompletion K))

theorem toLocal_single (v : HeightOneSpectrum (𝓞 K)) (i : Fin n) :
    toLocal v (Pi.single i 1 : Fin n → K) = Pi.single i 1 := by
  funext j
  simp only [toLocal, Pi.single_apply]
  split_ifs
  · exact map_one (algebraMap K (v.adicCompletion K))
  · exact map_zero (algebraMap K (v.adicCompletion K))

/-- For a $k$-lattice $L$ and a finite place $v$, $L_v$ is a $k_v$-lattice (Weil, V.§2, text p. 84). -/
theorem isLocalLattice_localLattice {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (v : HeightOneSpectrum (𝓞 K)) : IsLocalLattice v (localLattice L v) := by
  obtain ⟨m, l, hl⟩ := exists_gen_family hL.1
  constructor
  · have hrange : (localLattice L v : Set (Fin n → v.adicCompletion K)) = Set.range (lcLocal l v) := by
      ext y; exact mem_localLattice_iff hl v y
    rw [hrange]
    exact isCompact_range (continuous_lcLocal l v)
  · obtain ⟨d, hd0, hd⟩ := exists_nat_smul_mem hL (isKLattice_intVec (K := K) (n := n)).1
    have hd' : (d : v.adicCompletion K) ≠ 0 := by
      rw [← map_natCast (algebraMap K (v.adicCompletion K)), map_ne_zero]; exact_mod_cast hd0
    have hsub : ∀ z ∈ intLocal (n := n) v, d • z ∈ localLattice L v := by
      intro z hz
      have hz' : z = ∑ i, z i • (Pi.single i 1 : Fin n → v.adicCompletion K) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      rw [hz', Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : d • (z i • (Pi.single i 1 : Fin n → v.adicCompletion K)) =
          (⟨z i, hz i⟩ : v.adicCompletionIntegers K) • toLocal v (d • (Pi.single i 1 : Fin n → K)) := by
        rw [toLocal_nsmul, toLocal_single, smul_comm]; rfl
      rw [hi]
      exact Submodule.smul_mem _ _ (toLocal_mem_localLattice L v
        ⟨_, hd _ (Submodule.subset_span ⟨i, rfl⟩)⟩)
    let O : Set (Fin n → v.adicCompletion K) := {y | ((d : v.adicCompletion K))⁻¹ • y ∈ intLocal v}
    have hO : IsOpen O := (isOpen_intLocal v).preimage (continuous_const_smul _)
    have hO0 : (0 : Fin n → v.adicCompletion K) ∈ O := by
      show _ ∈ intLocal v
      rw [smul_zero]; intro i; exact (v.adicCompletionIntegers K).zero_mem
    have hOL : O ⊆ localLattice L v := by
      intro y hy
      have := hsub _ hy
      rwa [← Nat.cast_smul_eq_nsmul (v.adicCompletion K), smul_smul, mul_inv_cancel₀ hd', one_smul] at this
    exact (localLattice L v).toAddSubgroup.isOpen_of_mem_nhds
      (Filter.mem_of_superset (hO.mem_nhds hO0) hOL)

/-! ### Rescaled lattices $aL$ -/

theorem natCast_ne_zero_local (v : HeightOneSpectrum (𝓞 K)) {d : ℕ} (hd : d ≠ 0) :
    (d : v.adicCompletion K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (v.adicCompletion K)), map_ne_zero]; exact_mod_cast hd

theorem coe_natCast_inv (v : HeightOneSpectrum (𝓞 K)) (d : ℕ) :
    (((d : K)⁻¹ : K) : v.adicCompletion K) = ((d : v.adicCompletion K))⁻¹ := by
  rw [coe_eq_algebraMap, map_inv₀, map_natCast]

/-- $aL$, for $a\in k$. -/
def scaleLat (a : K) (L : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) :=
  L.map ((LinearMap.lsmul K (Fin n → K) a).restrictScalars (𝓞 K))

omit [NumberField K] in
theorem mem_scaleLat {a : K} {L : Submodule (𝓞 K) (Fin n → K)} {x : Fin n → K} :
    x ∈ scaleLat a L ↔ ∃ y ∈ L, a • y = x := by
  simp [scaleLat]

omit [NumberField K] in
theorem smul_mem_scaleLat {a : K} {L : Submodule (𝓞 K) (Fin n → K)} {y : Fin n → K} (hy : y ∈ L) :
    a • y ∈ scaleLat a L :=
  mem_scaleLat.mpr ⟨y, hy, rfl⟩

omit [NumberField K] in
theorem isKLattice_scaleLat {a : K} (ha : a ≠ 0) {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L) :
    IsKLattice K n (scaleLat a L) := by
  obtain ⟨b, hb⟩ := hL.2
  refine ⟨hL.1.map _, b.map (LinearEquiv.smulOfNeZero K (Fin n → K) a ha), fun i => ?_⟩
  rw [Module.Basis.map_apply]
  exact smul_mem_scaleLat (hb i)

/-- $a L_v\subset (aL)_v$. -/
theorem smul_mem_localLattice_scaleLat (a : K) {L : Submodule (𝓞 K) (Fin n → K)}
    (w : HeightOneSpectrum (𝓞 K)) {y : Fin n → w.adicCompletion K} (hy : y ∈ localLattice L w) :
    (a : w.adicCompletion K) • y ∈ localLattice (scaleLat a L) w := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← toLocal_smul]
    exact toLocal_mem_localLattice _ w ⟨_, smul_mem_scaleLat hx⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

/-- If $d$ is prime to $w$, $(d^{-1}L)_w\subset L_w$. -/
theorem localLattice_scaleLat_inv_le {d : ℕ} {w : HeightOneSpectrum (𝓞 K)} (hd : (d : 𝓞 K) ∉ w.asIdeal)
    {L : Submodule (𝓞 K) (Fin n → K)} {y : Fin n → w.adicCompletion K}
    (hy : y ∈ localLattice (scaleLat ((d : K)⁻¹) L) w) : y ∈ localLattice L w := by
  have hinv : ((d : w.adicCompletion K))⁻¹ ∈ w.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one hd, inv_one]
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := mem_scaleLat.mp hx
    rw [toLocal_smul, coe_natCast_inv]
    exact Submodule.smul_mem _ (⟨_, hinv⟩ : w.adicCompletionIntegers K) (toLocal_mem_localLattice L w ⟨z, hz⟩)
  | zero => simp
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/-! ### Approximation at finitely many places (from Prop. 4) -/

/-- From Prop. 4: given finitely many places $w\in T$ and open sets $U_w\subset E_w$ meeting $L_w$, some
element of $L$ lies in $U_w$ for every $w\in T$. -/
theorem exists_approx {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (U : ∀ w : HeightOneSpectrum (𝓞 K), Set (Fin n → w.adicCompletion K)) (hU : ∀ w ∈ T, IsOpen (U w))
    (hne : ∀ w ∈ T, ∃ z ∈ U w, z ∈ localLattice L w) : ∃ x ∈ L, ∀ w ∈ T, toLocal w x ∈ U w := by
  have hd := weil_V_2_prop4_partial hL T
  have : Finite T := hT.to_subtype
  choose z hzU hzL using hne
  let Ω : Set (∀ w : T, localLattice L w.1) := Set.pi Set.univ (fun w => Subtype.val ⁻¹' U w.1)
  have hΩ : IsOpen Ω :=
    isOpen_set_pi Set.finite_univ (fun w _ => (hU w.1 w.2).preimage continuous_subtype_val)
  have hne' : Ω.Nonempty := ⟨fun w => ⟨z w.1 w.2, hzL w.1 w.2⟩, fun w _ => hzU w.1 w.2⟩
  obtain ⟨l, hl⟩ := hd.exists_mem_open hΩ hne'
  exact ⟨l.1, l.2, fun w hw => hl ⟨w, hw⟩ (Set.mem_univ _)⟩

/-! ### The lattice $\bigcap_v(E\cap M_v)$ -/

/-- Weil's $M=\bigcap_v(E\cap M_v)$ for a family of $r_v$-modules $M_v\subset E_v$. -/
def globalOfLocal
    (Mloc : ∀ v : HeightOneSpectrum (𝓞 K), Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)) :
    Submodule (𝓞 K) (Fin n → K) where
  carrier := {x | ∀ v, toLocal v x ∈ Mloc v}
  add_mem' {x y} hx hy v := by
    show toLocal v (x + y) ∈ Mloc v
    rw [toLocal_add]; exact add_mem (hx v) (hy v)
  zero_mem' v := by
    show toLocal v 0 ∈ Mloc v
    rw [toLocal_zero]; exact zero_mem _
  smul_mem' a x hx v := by
    show toLocal v (a • x) ∈ Mloc v
    rw [toLocal_osmul]; exact Submodule.smul_mem _ _ (hx v)

theorem mem_globalOfLocal
    {Mloc : ∀ v : HeightOneSpectrum (𝓞 K), Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)}
    {x : Fin n → K} : x ∈ globalOfLocal Mloc ↔ ∀ v, toLocal v x ∈ Mloc v :=
  Iff.rfl

variable {Mloc : ∀ v : HeightOneSpectrum (𝓞 K),
  Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)}

/-- Theorem 2, "only if": if a $k$-lattice $M$ has $M_v$ for all $v$, then $M_v=L_v$ for almost all $v$. -/
theorem finite_of_localLattice_eq {L M : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : IsKLattice K n M) (hcl : ∀ v, localLattice M v = Mloc v) :
    {v | Mloc v ≠ localLattice L v}.Finite := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_smul_mem hM hL.1
  obtain ⟨d', hd'0, hd'⟩ := exists_nat_smul_mem hL hM.1
  refine (finite_natCast_mem (K := K) (mul_ne_zero hd0 hd'0)).subset fun w hw => ?_
  by_contra hnot
  simp only [Set.mem_ofPred_eq] at hw hnot
  push_cast at hnot
  have h1 : (d : 𝓞 K) ∉ w.asIdeal := fun h => hnot (Ideal.mul_mem_right _ _ h)
  have h2 : (d' : 𝓞 K) ∉ w.asIdeal := fun h => hnot (Ideal.mul_mem_left _ _ h)
  apply hw
  rw [← hcl w]
  apply le_antisymm
  · intro y hy; exact mem_of_nsmul_mem h2 _ (localLattice_nsmul hd' w hy)
  · intro y hy; exact mem_of_nsmul_mem h1 _ (localLattice_nsmul hd w hy)

/-- Theorem 2, existence: if $M_v=L_v$ for almost all $v$, then $M=\bigcap_v(E\cap M_v)$ is a $k$-lattice
with $M_v$ as its closure in $E_v$ for every $v$. -/
theorem globalOfLocal_spec {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : ∀ v, IsLocalLattice v (Mloc v)) (hfin : {v | Mloc v ≠ localLattice L v}.Finite) :
    IsKLattice K n (globalOfLocal Mloc) ∧ ∀ v, localLattice (globalOfLocal Mloc) v = Mloc v := by
  classical
  set S := hfin.toFinset with hS
  have hSmem : ∀ w, w ∉ S → Mloc w = localLattice L w := fun w hw => by
    by_contra h; exact hw (hfin.mem_toFinset.mpr h)
  -- an upper bound: `D • M ⊆ 𝔯ⁿ`
  obtain ⟨d0, hd00, hd0⟩ := exists_nat_smul_mem (isKLattice_intVec (K := K) (n := n)) hL.1
  have hloc : ∀ w : HeightOneSpectrum (𝓞 K), ∃ d : ℕ, d ≠ 0 ∧ ∀ y ∈ (Mloc w : Set (Fin n → w.adicCompletion K)), d • y ∈ intLocal w :=
    fun w => exists_nat_smul_subset w (hM w).1 (isOpen_intLocal w)
      (fun i => (w.adicCompletionIntegers K).zero_mem) (fun y hy m => nsmul_mem_intLocal hy m)
  choose dl hdl0 hdl using hloc
  set D := d0 * ∏ w ∈ S, dl w with hDdef
  have hD0 : D ≠ 0 := mul_ne_zero hd00 (Finset.prod_ne_zero_iff.mpr fun w _ => hdl0 w)
  have hD : ∀ w, ∀ y ∈ Mloc w, D • y ∈ intLocal w := by
    intro w y hy
    by_cases hw : w ∈ S
    · obtain ⟨e, he⟩ := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem dl hw) d0
      rw [hDdef, he, mul_comm, mul_smul]; exact nsmul_mem_intLocal (hdl w y hy) e
    · rw [hSmem w hw] at hy
      have h2 := localLattice_subset_intLocal le_rfl w (localLattice_nsmul hd0 w hy)
      rw [hDdef, mul_comm, mul_smul]; exact nsmul_mem_intLocal h2 _
  have hMint : ∀ x ∈ globalOfLocal Mloc, D • x ∈ intVec K n := fun x hx =>
    mem_intVec_of_local fun w => by rw [toLocal_nsmul]; exact hD w _ (hx w)
  have hFG : (globalOfLocal Mloc).FG := by
    refine Submodule.FG.of_le ((isKLattice_intVec (K := K) (n := n)).1.map
      ((LinearMap.lsmul K (Fin n → K) ((D : K)⁻¹)).restrictScalars (𝓞 K))) ?_
    intro x hx
    refine mem_scaleLat.mpr ⟨D • x, hMint x hx, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hD0), one_smul]
  -- a lower bound: `C • L ⊆ M`
  have hloc2 : ∀ w : HeightOneSpectrum (𝓞 K), ∃ c : ℕ, c ≠ 0 ∧
      ∀ y ∈ (localLattice L w : Set (Fin n → w.adicCompletion K)), c • y ∈ (Mloc w : Set _) :=
    fun w => exists_nat_smul_subset w (isLocalLattice_localLattice hL w).1 (hM w).2 (Mloc w).zero_mem
      (fun y hy m => nsmul_mem (S := Mloc w) hy m)
  choose cl hcl0 hcl using hloc2
  set C := ∏ w ∈ S, cl w with hCdef
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hcl0 w
  have hC : ∀ w, ∀ y ∈ localLattice L w, C • y ∈ Mloc w := by
    intro w y hy
    by_cases hw : w ∈ S
    · obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem cl hw
      rw [hCdef, he, mul_comm, mul_smul]; exact nsmul_mem (S := Mloc w) (hcl w y hy) e
    · rw [hSmem w hw]; exact nsmul_mem hy C
  have hCL : ∀ x ∈ L, C • x ∈ globalOfLocal Mloc := fun x hx w => by
    rw [toLocal_nsmul]; exact hC w _ (toLocal_mem_localLattice L w ⟨x, hx⟩)
  have hlat : IsKLattice K n (globalOfLocal Mloc) := by
    obtain ⟨b, hb⟩ := hL.2
    refine ⟨hFG, b.map (LinearEquiv.smulOfNeZero K (Fin n → K) (C : K) (by exact_mod_cast hC0)),
      fun i => ?_⟩
    rw [Module.Basis.map_apply]
    show (C : K) • b i ∈ _
    rw [Nat.cast_smul_eq_nsmul]; exact hCL _ (hb i)
  refine ⟨hlat, fun v => le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩; exact hx v
  · intro y hy
    -- an auxiliary lattice `L'' = c⁻¹ L` with `M_w ⊆ L''_w` for all `w`
    have hloc3 : ∀ w : HeightOneSpectrum (𝓞 K), ∃ c : ℕ, c ≠ 0 ∧
        ∀ y ∈ (Mloc w : Set (Fin n → w.adicCompletion K)), c • y ∈ (localLattice L w : Set _) :=
      fun w => exists_nat_smul_subset w (hM w).1 (isLocalLattice_localLattice hL w).2
        (localLattice L w).zero_mem (fun y hy m => nsmul_mem (S := localLattice L w) hy m)
    choose ml hml0 hml using hloc3
    set c := ∏ w ∈ S, ml w with hcdef
    have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hml0 w
    have hc : ∀ w, ∀ y ∈ Mloc w, c • y ∈ localLattice L w := by
      intro w y hy
      by_cases hw : w ∈ S
      · obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem ml hw
        rw [hcdef, he, mul_comm, mul_smul]; exact nsmul_mem (S := localLattice L w) (hml w y hy) e
      · rw [hSmem w hw] at hy; exact nsmul_mem hy c
    set L'' := scaleLat ((c : K)⁻¹) L with hL''def
    have hL'' : IsKLattice K n L'' := isKLattice_scaleLat (inv_ne_zero (by exact_mod_cast hc0)) hL
    have hsub : ∀ w, ∀ y ∈ Mloc w, y ∈ localLattice L'' w := by
      intro w y hy
      have := smul_mem_localLattice_scaleLat ((c : K)⁻¹) w (hc w y hy)
      rwa [coe_natCast_inv, ← Nat.cast_smul_eq_nsmul (w.adicCompletion K), smul_smul,
        inv_mul_cancel₀ (natCast_ne_zero_local w hc0), one_smul] at this
    set T : Set (HeightOneSpectrum (𝓞 K)) := (↑S ∪ {w | (c : 𝓞 K) ∈ w.asIdeal}) ∪ {v} with hTdef
    have hT : T.Finite := (S.finite_toSet.union (finite_natCast_mem hc0)).union (Set.finite_singleton v)
    rw [← SetLike.mem_coe, ← weil_V_2_prop4_closure hlat v, mem_closure_iff]
    intro o ho hyo
    let U : ∀ w : HeightOneSpectrum (𝓞 K), Set (Fin n → w.adicCompletion K) :=
      Function.update (fun w => (Mloc w : Set (Fin n → w.adicCompletion K))) v (o ∩ Mloc v)
    have hUv : U v = o ∩ Mloc v := Function.update_self _ _ _
    have hUw : ∀ w, w ≠ v → U w = Mloc w := fun w hw => Function.update_of_ne hw _ _
    have hUo : ∀ w ∈ T, IsOpen (U w) := by
      intro w _
      rcases eq_or_ne w v with rfl | hne
      · rw [hUv]; exact ho.inter (hM w).2
      · rw [hUw w hne]; exact (hM w).2
    have hUne : ∀ w ∈ T, ∃ z ∈ U w, z ∈ localLattice L'' w := by
      intro w _
      rcases eq_or_ne w v with rfl | hne
      · exact ⟨y, by rw [hUv]; exact ⟨hyo, hy⟩, hsub w y hy⟩
      · exact ⟨0, by rw [hUw w hne]; exact (Mloc w).zero_mem, zero_mem _⟩
    obtain ⟨x, hxL, hxU⟩ := exists_approx hL'' hT U hUo hUne
    refine ⟨toLocal v x, ?_, x, ?_, rfl⟩
    · have := hxU v (Or.inr rfl)
      rw [hUv] at this; exact this.1
    · intro w
      by_cases hw : w ∈ T
      · have := hxU w hw
        rcases eq_or_ne w v with rfl | hne
        · rw [hUv] at this; exact this.2
        · rw [hUw w hne] at this; exact this
      · have hwS : w ∉ S := fun h => hw (Or.inl (Or.inl h))
        have hwc : (c : 𝓞 K) ∉ w.asIdeal := fun h => hw (Or.inl (Or.inr h))
        rw [hSmem w hwS]
        exact localLattice_scaleLat_inv_le hwc (toLocal_mem_localLattice L'' w ⟨x, hxL⟩)

/-- Theorem 2, uniqueness, by Weil's argument: a $k$-lattice $M'$ with closure $M_v$ in $E_v$ for every $v$ is
$\bigcap_v(E\cap M_v)$. -/
theorem eq_globalOfLocal {L M' : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : ∀ v, IsLocalLattice v (Mloc v)) (hM' : IsKLattice K n M') (hcl : ∀ v, localLattice M' v = Mloc v) :
    M' = globalOfLocal Mloc := by
  have hFG := (globalOfLocal_spec hL hM (finite_of_localLattice_eq hL hM' hcl)).1.1
  have hle : M' ≤ globalOfLocal Mloc := fun x hx =>
    mem_globalOfLocal.mpr fun w => by rw [← hcl w]; exact toLocal_mem_localLattice M' w ⟨x, hx⟩
  obtain ⟨m, hm0, hm⟩ := exists_nat_smul_mem hM' hFG
  refine le_antisymm hle fun μ hμ => ?_
  have hμ' := mem_globalOfLocal.mp hμ
  let U : ∀ w : HeightOneSpectrum (𝓞 K), Set (Fin n → w.adicCompletion K) :=
    fun w => {z | ((m : w.adicCompletion K))⁻¹ • (z - toLocal w μ) ∈ Mloc w}
  have hUo : ∀ w ∈ {w : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ w.asIdeal}, IsOpen (U w) := fun w _ =>
    (hM w).2.preimage ((continuous_const_smul _).comp (continuous_id.sub continuous_const))
  have hUne : ∀ w ∈ {w : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ w.asIdeal},
      ∃ z ∈ U w, z ∈ localLattice M' w := fun w _ =>
    ⟨toLocal w μ, by
      show _ ∈ Mloc w
      rw [sub_self, smul_zero]; exact zero_mem _, by rw [hcl w]; exact hμ' w⟩
  obtain ⟨μ', hμ'M, hμ'U⟩ := exists_approx hM' (finite_natCast_mem hm0) U hUo hUne
  have hdiff : (m : K)⁻¹ • (μ - μ') ∈ globalOfLocal Mloc := by
    rw [mem_globalOfLocal]; intro w
    rw [toLocal_smul, toLocal_sub, coe_natCast_inv]
    by_cases hw : (m : 𝓞 K) ∈ w.asIdeal
    · have h1 : ((m : w.adicCompletion K))⁻¹ • (toLocal w μ' - toLocal w μ) ∈ Mloc w := hμ'U w hw
      have h2 : ((m : w.adicCompletion K))⁻¹ • (toLocal w μ - toLocal w μ') =
          -(((m : w.adicCompletion K))⁻¹ • (toLocal w μ' - toLocal w μ)) := by
        rw [← smul_neg, neg_sub]
      rw [h2]; exact neg_mem h1
    · apply mem_of_nsmul_mem hw
      rw [← Nat.cast_smul_eq_nsmul (w.adicCompletion K), smul_smul,
        mul_inv_cancel₀ (natCast_ne_zero_local w hm0), one_smul]
      exact sub_mem (hμ' w) (by rw [← hcl w]; exact toLocal_mem_localLattice M' w ⟨μ', hμ'M⟩)
  have h3 := hm _ hdiff
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hm0), one_smul] at h3
  have := M'.add_mem h3 hμ'M
  simpa using this

/-! ### Theorem 2, in Weil's words (closures) -/

theorem closure_eq_iff {M : Submodule (𝓞 K) (Fin n → K)} (hM : IsKLattice K n M) (v : HeightOneSpectrum (𝓞 K))
    (N : Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)) :
    closure (toLocal v '' (M : Set (Fin n → K))) = (N : Set (Fin n → v.adicCompletion K)) ↔
      localLattice M v = N := by
  rw [weil_V_2_prop4_closure hM v, SetLike.coe_set_eq]

theorem setOf_ne_closure_eq {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L) :
    {v | (Mloc v : Set (Fin n → v.adicCompletion K)) ≠ closure (toLocal v '' (L : Set (Fin n → K)))} =
      {v | Mloc v ≠ localLattice L v} := by
  ext v
  simp only [Set.mem_ofPred_eq, weil_V_2_prop4_closure hL v, Ne, SetLike.coe_set_eq]

/-- **Weil, V.§2, Theorem 2** (p. 84), $E=k^n$: let $L$ be a $k$-lattice and, for each finite place $v$, $M_v$ a
$k_v$-lattice in $E_v$. There is a $k$-lattice $M$ in $E$ whose closure in $E_v$ is $M_v$ for every $v$ if and
only if $M_v$ equals the closure $L_v$ of $L$ for almost all $v$. -/
@[kb "weil1973bnt" "Ch. V, §2, Thm. 2 (p. 84), E = k^n, existence criterion"]
theorem weil_V_2_thm2 {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : ∀ v, IsLocalLattice v (Mloc v)) :
    (∃ M : Submodule (𝓞 K) (Fin n → K), IsKLattice K n M ∧
      ∀ v, closure (toLocal v '' (M : Set (Fin n → K))) = (Mloc v : Set (Fin n → v.adicCompletion K))) ↔
    {v | (Mloc v : Set (Fin n → v.adicCompletion K)) ≠ closure (toLocal v '' (L : Set (Fin n → K)))}.Finite := by
  rw [setOf_ne_closure_eq hL]
  constructor
  · rintro ⟨M, hMl, hcl⟩
    exact finite_of_localLattice_eq hL hMl fun v => (closure_eq_iff hMl v _).mp (hcl v)
  · intro hfin
    obtain ⟨h1, h2⟩ := globalOfLocal_spec hL hM hfin
    exact ⟨_, h1, fun v => (closure_eq_iff h1 v _).mpr (h2 v)⟩

/-- **Weil, V.§2, Theorem 2**, existence: when $M_v=L_v$ for almost all $v$, $M=\bigcap_v(E\cap M_v)$ is a
$k$-lattice whose closure in $E_v$ is $M_v$ for every $v$. -/
@[kb "weil1973bnt" "Ch. V, §2, Thm. 2 (p. 84), E = k^n, existence, M = ∩ (E ∩ M_v)"]
theorem weil_V_2_thm2_exists {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : ∀ v, IsLocalLattice v (Mloc v))
    (hfin : {v | (Mloc v : Set (Fin n → v.adicCompletion K)) ≠
      closure (toLocal v '' (L : Set (Fin n → K)))}.Finite) :
    IsKLattice K n (globalOfLocal Mloc) ∧
      ∀ v, closure (toLocal v '' (globalOfLocal Mloc : Set (Fin n → K))) =
        (Mloc v : Set (Fin n → v.adicCompletion K)) := by
  rw [setOf_ne_closure_eq hL] at hfin
  obtain ⟨h1, h2⟩ := globalOfLocal_spec hL hM hfin
  exact ⟨h1, fun v => (closure_eq_iff h1 v _).mpr (h2 v)⟩

/-- **Weil, V.§2, Theorem 2**, uniqueness: a $k$-lattice $M$ whose closure in $E_v$ is $M_v$ for every $v$ is
$\bigcap_v(E\cap M_v)$; in particular there is only one. -/
@[kb "weil1973bnt" "Ch. V, §2, Thm. 2 (p. 84), E = k^n, uniqueness"]
theorem weil_V_2_thm2_unique {L M : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : ∀ v, IsLocalLattice v (Mloc v)) (hML : IsKLattice K n M)
    (hcl : ∀ v, closure (toLocal v '' (M : Set (Fin n → K))) = (Mloc v : Set (Fin n → v.adicCompletion K))) :
    M = globalOfLocal Mloc :=
  eq_globalOfLocal hL hM hML fun v => (closure_eq_iff hML v _).mp (hcl v)

/-- A $k$-lattice is recovered from its closures: $L=\bigcap_v(E\cap L_v)$ (Theorem 2 applied to $M_v=L_v$). -/
@[kb "weil1973bnt" "Ch. V, §2, Thm. 2 (p. 84), E = k^n, L = ∩ (E ∩ L_v)"]
theorem globalOfLocal_localLattice {L : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L) :
    globalOfLocal (localLattice L) = L :=
  (eq_globalOfLocal (Mloc := localLattice L) hL (isLocalLattice_localLattice hL) hL fun _ => rfl).symm

/-! ### The Corollary of Theorem 2 -/

theorem localLattice_sup (L L' : Submodule (𝓞 K) (Fin n → K)) (v : HeightOneSpectrum (𝓞 K)) :
    localLattice (L ⊔ L') v = localLattice L v ⊔ localLattice L' v := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [SetLike.mem_coe, toLocal_add]
    exact Submodule.add_mem_sup (toLocal_mem_localLattice L v ⟨y, hy⟩) (toLocal_mem_localLattice L' v ⟨z, hz⟩)
  · exact sup_le (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr le_sup_left)))
      (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr le_sup_right)))

/-- **Weil, V.§2, Corollary of Theorem 2** (p. 85), sums: $L+L'$ is a $k$-lattice and its closure in $E_v$ is
$L_v+L'_v$. -/
@[kb "weil1973bnt" "Ch. V, §2, Cor. of Thm. 2 (p. 85), E = k^n, L + L'"]
theorem weil_V_2_thm2_cor_sup {L L' : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hL' : IsKLattice K n L') :
    IsKLattice K n (L ⊔ L') ∧ ∀ v, localLattice (L ⊔ L') v = localLattice L v ⊔ localLattice L' v := by
  obtain ⟨b, hb⟩ := hL.2
  exact ⟨⟨hL.1.sup hL'.1, b, fun i => le_sup_left (a := L) (hb i)⟩, localLattice_sup L L'⟩

/-- **Weil, V.§2, Corollary of Theorem 2** (p. 85), intersections: $L\cap L'$ is a $k$-lattice and its closure
in $E_v$ is $L_v\cap L'_v$; Weil's proof, through Theorem 2. -/
@[kb "weil1973bnt" "Ch. V, §2, Cor. of Thm. 2 (p. 85), E = k^n, L ∩ L'"]
theorem weil_V_2_thm2_cor_inf {L L' : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hL' : IsKLattice K n L') :
    IsKLattice K n (L ⊓ L') ∧ ∀ v, localLattice (L ⊓ L') v = localLattice L v ⊓ localLattice L' v := by
  let N : ∀ v : HeightOneSpectrum (𝓞 K), Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K) :=
    fun v => localLattice L v ⊓ localLattice L' v
  have hN : ∀ v, IsLocalLattice v (N v) := fun v =>
    ⟨by
      rw [Submodule.coe_inf]
      exact (isLocalLattice_localLattice hL v).1.inter_right (isLocalLattice_localLattice hL' v).1.isClosed,
     by
      rw [Submodule.coe_inf]
      exact (isLocalLattice_localLattice hL v).2.inter (isLocalLattice_localLattice hL' v).2⟩
  have hfin : {v | N v ≠ localLattice L v}.Finite := by
    refine (finite_of_localLattice_eq (Mloc := localLattice L') hL hL' fun _ => rfl).subset fun v hv => ?_
    intro heq
    apply hv
    show localLattice L v ⊓ localLattice L' v = _
    rw [heq, inf_idem]
  obtain ⟨h1, h2⟩ := globalOfLocal_spec hL hN hfin
  have heq : globalOfLocal N = L ⊓ L' := by
    ext x
    constructor
    · intro hx
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← globalOfLocal_localLattice hL]
        exact fun v => (Submodule.mem_inf.mp (mem_globalOfLocal.mp hx v)).1
      · rw [← globalOfLocal_localLattice hL']
        exact fun v => (Submodule.mem_inf.mp (mem_globalOfLocal.mp hx v)).2
    · intro hx
      exact mem_globalOfLocal.mpr fun v => Submodule.mem_inf.mpr
        ⟨toLocal_mem_localLattice L v ⟨x, (Submodule.mem_inf.mp hx).1⟩,
          toLocal_mem_localLattice L' v ⟨x, (Submodule.mem_inf.mp hx).2⟩⟩
  rw [heq] at h1 h2
  exact ⟨h1, h2⟩

end NumberFieldKB.WeilBNT
