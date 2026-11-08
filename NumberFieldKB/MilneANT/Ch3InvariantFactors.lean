import NumberFieldKB.MilneANT.Ch3Modules

/-!
# Milne, *Algebraic Number Theory*, Theorem 3.32: the invariant factor theorem, proved

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), p. 58; bib key `milne2020ant`. Milne only
sketches the proof and refers to Curtis–Reiner, Fröhlich–Taylor and Narkiewicz; the proof here is self-contained
and works over every Dedekind domain $A$ with field of fractions $K$.

Main results:

* `thm_3_32_exists`: for finitely generated $A$-submodules $N \subseteq M$ of an $m$-dimensional $K$-vector space
  $V$, with $N$ spanning $V$, there are a $K$-basis $(e_i)$, invertible fractional ideals $\mathfrak a_i$ and
  nonzero ideals $\mathfrak b_0 \supseteq \cdots \supseteq \mathfrak b_{m-1}$ with
  $M = \bigoplus_i \mathfrak a_i e_i$ and $N = \bigoplus_i \mathfrak a_i \mathfrak b_i e_i$;
* `thm_3_32_unique`: the $\mathfrak b_i$ are determined by the pair $N \subseteq M$;
* `invariantFactorTheorem`: the named statement `InvariantFactorTheorem A K` of `Ch3Modules.lean` holds.

**Proof of existence** (induction on $m$). Let $\mathfrak b = \{r \in A : rM \subseteq N\}$ (the annihilator of
$M/N$; `Submodule.colon`). The key point is a functional $\psi \colon V \to K$ with $\psi(M) \ne 0$ and
$\psi(N) \subseteq \mathfrak b\,\psi(M)$ (`exists_good_functional`). It is built from the lattices
$\{\chi : \chi(N) \subseteq \mathfrak b\}$: for each maximal ideal $\mathfrak p \supseteq \mathfrak b$ such a $\chi$ is
nonzero modulo $\mathfrak p$ on $M$, because otherwise $\mathfrak p^{-1}\mathfrak b M \subseteq N$ by reflexivity
$N = N^{\vee\vee}$ (`mem_of_dual`); the Chinese remainder theorem combines these into one $\psi$ with
$\psi(M) + \mathfrak b = A$, whence $\psi(N) \subseteq \mathfrak b \cap \psi(M) = \mathfrak b\,\psi(M)$. Since
$\mathfrak a = \psi(M)$ is invertible there is $e$ with $\psi(e) = 1$ and $\mathfrak a e \subseteq M$
(`exists_section`), so $M = \mathfrak a e \oplus (M \cap \ker\psi)$ and
$N = \mathfrak a\mathfrak b e \oplus (N \cap \ker\psi)$, and the induction hypothesis applies to $\ker\psi$
(`adapted_succ_of_functional`). Reflexivity of $N$ comes from the case $M = N$ of the same induction step.

**Proof of uniqueness.** The *index ideal* $[M : N]$ (`indexIdeal`), spanned by the determinants
$\det(\chi_s(y_t))$ with $\chi_s(M) \subseteq A$ and $y_t \in N$, is intrinsic and equals $\prod_i \mathfrak b_i$
for any adapted decomposition (`indexIdeal_eq`). Applied to $N + \mathfrak c M$, which has invariant factors
$\mathfrak b_i + \mathfrak c$ (`sup_smul_eq`), it gives $\prod_i (\mathfrak b_i + \mathfrak c) =
\prod_i (\mathfrak b'_i + \mathfrak c)$ for every ideal $\mathfrak c$; for decreasing chains this forces
$\mathfrak b = \mathfrak b'$ by cancellation in the monoid of ideals (`chain_eq_of_prod_eq`).

Internally the induction lists the invariant factors in increasing order (`Adapted`); `thm_3_32_exists` reverses
it to Milne's order. Indices are $0$-based.
-/

set_option linter.unusedSectionVars false

open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.InvariantFactors

section Basic

variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

/-- The $A$-submodule $I v = \{c v : c \in I\}$ of $V$, for an $A$-submodule $I$ of $K$. -/
def line (I : Submodule A K) (v : V) : Submodule A V :=
  I.map ((LinearMap.toSpanSingleton K V v).restrictScalars A)

theorem mem_line {I : Submodule A K} {v x : V} : x ∈ line I v ↔ ∃ c ∈ I, c • v = x := by
  simp [line]

theorem smul_mem_line {I : Submodule A K} {v : V} {c : K} (hc : c ∈ I) : c • v ∈ line I v :=
  mem_line.2 ⟨c, hc, rfl⟩

theorem line_mono {I J : Submodule A K} (h : I ≤ J) (v : V) : line I v ≤ line J v :=
  Submodule.map_mono h

/-- Membership in $\bigoplus_i c_i e_i$ for a $K$-basis $e$: all coordinates lie in the right $c_i$. -/
theorem mem_iSup_line_iff {ι : Type*} [Fintype ι] (e : Module.Basis ι K V) (c : ι → Submodule A K)
    (v : V) : v ∈ ⨆ i, line (c i) (e i) ↔ ∀ i, e.coord i v ∈ c i := by
  classical
  constructor
  · intro hv
    refine Submodule.iSup_induction _ (motive := fun x => ∀ i, e.coord i x ∈ c i) hv ?_ ?_ ?_
    · intro j x hx
      obtain ⟨d, hd, rfl⟩ := mem_line.1 hx
      intro i
      by_cases h : i = j
      · subst h; simpa using hd
      · simp [Module.Basis.coord_apply, Ne.symm h]
    · intro i; simp
    · intro x y hx hy i; simpa using add_mem (hx i) (hy i)
  · intro h
    rw [← e.sum_repr v]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (smul_mem_line (h i))

end Basic

section Lattice

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

theorem exists_smul_mem_of_span_eq_top {N : Submodule A V}
    (hN : Submodule.span K (N : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ N := by
  have hv : v ∈ Submodule.span K (N : Set V) := hN ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem d2 h1
    · rw [mul_smul]; exact N.smul_mem d1 h2
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hs0 : algebraMap A K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    refine ⟨s * d, mul_ne_zero (nonZeroDivisors.ne_zero hs) hd, ?_⟩
    have : (s * d) • ((algebraMap A K r / algebraMap A K s) • x) = r • (d • x) := by
      rw [← algebraMap_smul K (s * d), smul_smul, ← algebraMap_smul K d x, ← algebraMap_smul K r,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact N.smul_mem r h

theorem span_eq_top_of_forall {N : Submodule A V} (h : ∀ v : V, ∃ d : A, d ≠ 0 ∧ d • v ∈ N) :
    Submodule.span K (N : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨d, hd, hdv⟩ := h v
  have hd' : algebraMap A K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  have : v = (algebraMap A K d)⁻¹ • (d • v) := by
    rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hdv)

theorem colon_ne_bot {M N : Submodule A V} (hM : M.FG) (hN : Submodule.span K (N : Set V) = ⊤) :
    N.colon (M : Set V) ≠ ⊥ := by
  classical
  obtain ⟨s, rfl⟩ := hM
  choose d hd hdN using exists_smul_mem_of_span_eq_top hN
  have hmem : (∏ x ∈ s, d x) ∈ N.colon (Submodule.span A (s : Set V) : Set V) := by
    rw [Submodule.mem_colon]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.prod_erase_mul s d hx, mul_smul]
      exact N.smul_mem _ (hdN x)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact N.smul_mem c hx
  intro hbot
  rw [hbot, Submodule.mem_bot, Finset.prod_eq_zero_iff] at hmem
  obtain ⟨x, _, hx⟩ := hmem
  exact hd x hx

end Lattice

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

/-- A nonzero finitely generated $A$-submodule of $K$, as a unit of the group of fractional ideals. -/
noncomputable def unitOfFG (I : Submodule A K) (hI : I.FG) (h0 : I ≠ ⊥) : (FractionalIdeal A⁰ K)ˣ :=
  Units.mk0 (⟨I, FractionalIdeal.isFractional_of_fg hI⟩ : FractionalIdeal A⁰ K) (fun h => h0 (by
    have := congrArg (fun J : FractionalIdeal A⁰ K => (J : Submodule A K)) h
    simpa using this))

@[simp]
theorem coe_unitOfFG (I : Submodule A K) (hI : I.FG) (h0 : I ≠ ⊥) :
    ((unitOfFG I hI h0 : FractionalIdeal A⁰ K) : Submodule A K) = I := rfl

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- If $\mathfrak a = \varphi(M)$ is invertible, the surjection $\varphi \colon M \to \mathfrak a$ has a section
$x \mapsto x e$: there is $e \in V$ with $\varphi(e) = 1$ and $\mathfrak a e \subseteq M$. -/
theorem exists_section (φ : V →ₗ[K] K) (M : Submodule A V) (a : (FractionalIdeal A⁰ K)ˣ)
    (ha : ((a : FractionalIdeal A⁰ K) : Submodule A K) = M.map (φ.restrictScalars A)) :
    ∃ e : V, φ e = 1 ∧ line ((a : FractionalIdeal A⁰ K) : Submodule A K) e ≤ M := by
  let E : Submodule A V :=
    { carrier := {e | ∀ z ∈ ((a : FractionalIdeal A⁰ K) : Submodule A K), z • e ∈ M}
      add_mem' := fun h1 h2 z hz => by rw [smul_add]; exact add_mem (h1 z hz) (h2 z hz)
      zero_mem' := fun z _ => by simp
      smul_mem' := fun r e h z hz => by rw [smul_comm]; exact M.smul_mem r (h z hz) }
  have key : ((a : FractionalIdeal A⁰ K) : Submodule A K) * ((a⁻¹ : (FractionalIdeal A⁰ K)ˣ) :
      FractionalIdeal A⁰ K) ≤ E.map (φ.restrictScalars A) := by
    rw [Submodule.mul_le]
    intro x hx y hy
    have hx' := hx
    rw [ha] at hx'
    obtain ⟨m, hm, rfl⟩ := hx'
    refine ⟨y • m, ?_, by simp [mul_comm]⟩
    intro z hz
    have hzy : z * y ∈ (1 : FractionalIdeal A⁰ K) := by
      rw [← a.mul_inv, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul]
      exact Submodule.mul_mem_mul hz hy
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hzy
    rw [smul_smul, ← hr, algebraMap_smul]
    exact M.smul_mem r hm
  have h1 : (1 : K) ∈ E.map (φ.restrictScalars A) := by
    apply key
    rw [← FractionalIdeal.coe_mul, Units.mul_inv, FractionalIdeal.mem_coe]
    exact FractionalIdeal.one_mem_one _
  obtain ⟨e, he, he1⟩ := h1
  refine ⟨e, he1, ?_⟩
  intro x hx
  obtain ⟨c, hc, rfl⟩ := mem_line.1 hx
  exact he c hc

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- The image of a line of a subspace $W$ in $V$. -/
theorem map_line (W : Submodule K V) (I : Submodule A K) (w : W) :
    (line I w).map ((W.subtype).restrictScalars A) = line I (w : V) := by
  ext x
  simp only [Submodule.mem_map, mem_line, LinearMap.coe_restrictScalars, Submodule.coe_subtype]
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c • w, ⟨c, hc, rfl⟩, rfl⟩

omit [IsDedekindDomain A] [IsFractionRing A K] in
theorem finiteDimensional_of_fg {N : Submodule A V} (hN : N.FG)
    (hspan : Submodule.span K (N : Set V) = ⊤) : FiniteDimensional K V := by
  obtain ⟨s, rfl⟩ := hN
  rw [Submodule.span_span_of_tower] at hspan
  exact Module.Finite.of_fg_top (hspan ▸ Submodule.fg_span s.finite_toSet)

/-- The statement proved by induction on the dimension $m$: adapted bases exist, with the invariant factors
listed in *increasing* order $\mathfrak b_0 \subseteq \mathfrak b_1 \subseteq \cdots$ (reversed at the end). -/
def Adapted (m : ℕ) (M N : Submodule A V) : Prop :=
  ∃ (e : Module.Basis (Fin m) K V) (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (b : Fin m → Ideal A),
    (∀ i, b i ≠ ⊥) ∧ Monotone b ∧
    M = ⨆ i, line ((a i : FractionalIdeal A⁰ K) : Submodule A K) (e i) ∧
    N = ⨆ i, line (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K) (e i)

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- A submodule of a finitely generated submodule is finitely generated ($A$ is noetherian). -/
theorem fg_of_le_fg [IsNoetherianRing A] {P Q : Submodule A V} (hQ : Q.FG) (h : P ≤ Q) : P.FG := by
  have := isNoetherian_of_fg_of_noetherian Q hQ
  have h2 := (IsNoetherian.noetherian (P.comap Q.subtype)).map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 h] at h2

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- Reassembling $P = c_0 e \oplus P'$ where $P' = P \cap \ker\varphi$ is decomposed along a basis $e'$ of
$\ker \varphi$. -/
theorem eq_iSup_cons {m : ℕ} (φ : V →ₗ[K] K) (e : V) (he1 : φ e = 1)
    (e' : Fin m → LinearMap.ker φ) (E : Fin (m + 1) → V)
    (hE : E = Fin.cons e (fun i => (e' i : V)))
    (P : Submodule A V) (c : Fin (m + 1) → Submodule A K)
    (hP' : P.comap ((LinearMap.ker φ).subtype.restrictScalars A) = ⨆ i, line (c i.succ) (e' i))
    (hline : line (c 0) e ≤ P) (hφP : ∀ v ∈ P, φ v ∈ c 0) :
    P = ⨆ i, line (c i) (E i) := by
  set ι : LinearMap.ker φ →ₗ[A] V := (LinearMap.ker φ).subtype.restrictScalars A with hι
  have hmap : (⨆ i, line (c i.succ) (e' i)).map ι = ⨆ i, line (c i.succ) (e' i : V) := by
    rw [Submodule.map_iSup]
    exact iSup_congr fun i => map_line _ _ _
  apply le_antisymm
  · intro v hv
    have hw : v - φ v • e ∈ LinearMap.ker φ := by simp [he1]
    have hwP : (⟨v - φ v • e, hw⟩ : LinearMap.ker φ) ∈ P.comap ι := by
      rw [Submodule.mem_comap]
      exact sub_mem hv (hline (smul_mem_line (hφP v hv)))
    rw [hP'] at hwP
    have hw' : v - φ v • e ∈ ⨆ i, line (c i.succ) (e' i : V) := by
      rw [← hmap]; exact Submodule.mem_map_of_mem hwP
    have hv' : v = φ v • e + (v - φ v • e) := by abel
    rw [hv']
    refine add_mem (Submodule.mem_iSup_of_mem 0 (by rw [hE]; exact smul_mem_line (hφP v hv))) ?_
    have hle : (⨆ i, line (c i.succ) (e' i : V)) ≤ ⨆ i, line (c i) (E i) :=
      iSup_le fun i => le_iSup_of_le i.succ (by rw [hE]; exact le_rfl)
    exact hle hw'
  · refine iSup_le fun i => ?_
    induction i using Fin.cases with
    | zero => rw [hE]; exact hline
    | succ i =>
      rw [hE]
      simp only [Fin.cons_succ]
      rw [← map_line]
      refine (Submodule.map_mono ?_).trans (Submodule.map_comap_le ι P)
      rw [hP']
      exact le_iSup (fun j => line (c j.succ) (e' j)) i

end Dedekind

section Induction

universe u v w

variable (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- The statement proved by induction on the dimension $m$ (for spaces $V$ in a fixed universe). -/
def Stmt (m : ℕ) : Prop :=
  ∀ (V : Type w) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V],
    Module.finrank K V = m → ∀ M N : Submodule A V, M.FG → N.FG → N ≤ M →
      Submodule.span K (N : Set V) = ⊤ → Adapted (A := A) (K := K) m M N

variable {A K}

/-- The induction step, given a functional $\varphi$ with $\varphi(M) \ne 0$ and
$\varphi(N) \subseteq \mathfrak b\,\varphi(M)$, where $\mathfrak b$ is the annihilator of $M/N$. -/
theorem adapted_succ_of_functional {m : ℕ} (IH : Stmt.{u, v, w} A K m)
    {V : Type w} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (hV : Module.finrank K V = m + 1) {M N : Submodule A V} (hM : M.FG) (hNM : N ≤ M)
    (hN : Submodule.span K (N : Set V) = ⊤) (φ : V →ₗ[K] K)
    (hφ : M.map (φ.restrictScalars A) ≠ ⊥)
    (hφN : ∀ v ∈ N, φ v ∈ ((N.colon (M : Set V) : FractionalIdeal A⁰ K) : Submodule A K) *
      M.map (φ.restrictScalars A)) :
    Adapted (K := K) (m + 1) M N := by
  classical
  have hMspan : Submodule.span K (M : Set V) = ⊤ :=
    eq_top_iff.2 (hN ▸ Submodule.span_mono hNM)
  have : FiniteDimensional K V := finiteDimensional_of_fg hM hMspan
  set b : Ideal A := N.colon (M : Set V) with hb
  have hb0 : b ≠ ⊥ := colon_ne_bot hM hN
  set a := unitOfFG (M.map (φ.restrictScalars A)) (hM.map _) hφ with ha
  have ha' : ((a : FractionalIdeal A⁰ K) : Submodule A K) = M.map (φ.restrictScalars A) :=
    coe_unitOfFG _ _ _
  obtain ⟨e, he1, heM⟩ := exists_section φ M a ha'
  have hφM : ∀ v ∈ M, φ v ∈ ((a : FractionalIdeal A⁰ K) : Submodule A K) := fun v hv =>
    ha' ▸ ⟨v, hv, rfl⟩
  have hlineN : line (((a : FractionalIdeal A⁰ K) * (b : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K) e ≤ N := by
    rw [line, Submodule.map_le_iff_le_comap, FractionalIdeal.coe_mul, Submodule.mul_le]
    intro y hy z hz
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply]
    rw [mul_comm, mul_smul, algebraMap_smul]
    exact (Submodule.mem_colon.1 hr) _ (heM (smul_mem_line hy))
  have hφN' : ∀ v ∈ N, φ v ∈ (((a : FractionalIdeal A⁰ K) * (b : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K) := by
    intro v hv
    rw [FractionalIdeal.coe_mul, mul_comm, ha']
    exact hφN v hv
  -- the hyperplane `W = ker φ`
  set W := LinearMap.ker φ with hW
  set ι : W →ₗ[A] V := W.subtype.restrictScalars A with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  set M' := M.comap ι
  set N' := N.comap ι
  have hM'fg : M'.FG := Submodule.fg_of_fg_map_injective ι hιinj
    (fg_of_le_fg hM (Submodule.map_comap_le ι M))
  have hN'fg : N'.FG := Submodule.fg_of_fg_map_injective ι hιinj
    (fg_of_le_fg hM ((Submodule.map_comap_le ι N).trans hNM))
  have hN'span : Submodule.span K (N' : Set W) = ⊤ := by
    apply span_eq_top_of_forall
    intro w
    obtain ⟨d, hd, hdN⟩ := exists_smul_mem_of_span_eq_top hN (w : V)
    exact ⟨d, hd, by simpa [N', ι] using hdN⟩
  have hsurj : Function.Surjective φ := fun c => ⟨c • e, by simp [he1]⟩
  have hWrank : Module.finrank K W = m := by
    show Module.finrank K (LinearMap.ker φ) = m
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hV] at this
    omega
  obtain ⟨e', a', b', hb'0, hb'mono, hM', hN'⟩ :=
    IH W hWrank M' N' hM'fg hN'fg (Submodule.comap_mono hNM) hN'span
  -- `b ⊆ b' j` for all `j`
  have hbb : ∀ j, b ≤ b' j := by
    intro j
    have key : (b : FractionalIdeal A⁰ K) * (a' j : FractionalIdeal A⁰ K) ≤
        (a' j : FractionalIdeal A⁰ K) * (b' j : FractionalIdeal A⁰ K) := by
      rw [FractionalIdeal.mul_le]
      intro x hx y hy
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      have hyM : y • e' j ∈ M' := by
        rw [hM']; exact Submodule.mem_iSup_of_mem j (smul_mem_line hy)
      have hN'm : r • (y • e' j) ∈ N' := by
        rw [Submodule.mem_comap] at hyM ⊢
        simpa [ι] using (Submodule.mem_colon.1 hr) _ hyM
      rw [hN', mem_iSup_line_iff] at hN'm
      have := hN'm j
      rw [← algebraMap_smul K r, smul_smul, map_smul] at this
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_coeIdeal]
      simpa using this
    have h2 := mul_le_mul' (le_refl (((a' j)⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)) key
    rw [mul_comm (b : FractionalIdeal A⁰ K), ← mul_assoc, ← mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul, one_mul] at h2
    exact (FractionalIdeal.coeIdeal_le_coeIdeal K).1 h2
  -- the new basis
  have hli : ∀ (c : K), ∀ x ∈ W, c • e + x = 0 → c = 0 := by
    intro c x hx h
    have := congrArg φ h
    rw [map_add, map_smul, he1, LinearMap.mem_ker.1 hx] at this
    simpa using this
  have hsp : ∀ z : V, ∃ c : K, z + c • e ∈ W := fun z => ⟨-φ z, by rw [hW, LinearMap.mem_ker]; simp [he1]⟩
  set E := Module.Basis.mkFinCons e e' hli hsp with hEdef
  have hE : (E : Fin (m + 1) → V) = Fin.cons e (fun i => (e' i : V)) :=
    Module.Basis.coe_mkFinCons _ _ _ _
  refine ⟨E, Fin.cons a a', Fin.cons b b', ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hb0
    | succ i => simpa using hb'0 i
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact le_rfl
      | succ j => simpa using hbb j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd (Fin.le_zero_iff.1 hij) (Fin.succ_ne_zero i)
      | succ j => simpa using hb'mono (Fin.succ_le_succ_iff.1 hij)
  · refine eq_iSup_cons φ e he1 e' E hE M _ ?_ ?_ ?_
    · simpa using hM'
    · simpa using heM
    · simpa using hφM
  · refine eq_iSup_cons φ e he1 e' E hE N _ ?_ ?_ ?_
    · simpa using hN'
    · simpa using hlineN
    · simpa using hφN'

/-- Base of the induction: dimension zero. -/
theorem stmt_zero : Stmt.{u, v, w} A K 0 := by
  intro V _ _ _ _ hV M N _ hN _ hspan
  have : FiniteDimensional K V := finiteDimensional_of_fg hN hspan
  have : Subsingleton V := Module.finrank_zero_iff.1 hV
  refine ⟨Module.Basis.empty V, finZeroElim, finZeroElim, fun i => i.elim0, fun i => i.elim0, ?_, ?_⟩
  · rw [iSup_of_empty]; exact Submodule.eq_bot_of_subsingleton
  · rw [iSup_of_empty]; exact Submodule.eq_bot_of_subsingleton

omit [IsDedekindDomain A] in
/-- A functional that does not vanish on a lattice spanning $V \ne 0$. -/
theorem exists_functional {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V] (hV : 0 < Module.finrank K V) (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) : ∃ φ : V →ₗ[K] K, M.map (φ.restrictScalars A) ≠ ⊥ := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K V = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hV).symm⟩
  let f := Module.finBasisOfFinrankEq K V hn
  refine ⟨f.coord 0, fun h => ?_⟩
  have hle : (M : Set V) ⊆ LinearMap.ker (f.coord 0) := by
    intro x hx
    have : (f.coord 0).restrictScalars A x ∈ M.map ((f.coord 0).restrictScalars A) :=
      Submodule.mem_map_of_mem hx
    rw [h] at this
    simpa using this
  have := Submodule.span_le.2 hle
  rw [hM, top_le_iff, LinearMap.ker_eq_top] at this
  have := congrArg (fun g : V →ₗ[K] K => g (f 0)) this
  simp at this

/-- The case $N = \mathfrak b M$ with $\mathfrak b = A$, i.e. $N = M$ up to the annihilator being trivial. -/
theorem adapted_succ_of_colon_eq_top {m : ℕ} (IH : Stmt.{u, v, w} A K m)
    {V : Type w} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (hV : Module.finrank K V = m + 1) {M N : Submodule A V} (hM : M.FG) (hNM : N ≤ M)
    (hN : Submodule.span K (N : Set V) = ⊤) (htop : N.colon (M : Set V) = ⊤) :
    Adapted (K := K) (m + 1) M N := by
  have hMspan : Submodule.span K (M : Set V) = ⊤ :=
    eq_top_iff.2 (hN ▸ Submodule.span_mono hNM)
  have : FiniteDimensional K V := finiteDimensional_of_fg hM hMspan
  obtain ⟨φ, hφ⟩ := exists_functional (A := A) (by omega) M hMspan
  refine adapted_succ_of_functional IH hV hM hNM hN φ hφ fun v hv => ?_
  rw [htop, FractionalIdeal.coeIdeal_top, FractionalIdeal.coe_one, one_mul]
  exact ⟨v, hNM hv, rfl⟩

/-- Reflexivity of a lattice $L$ that has an adapted decomposition: $L = L^{\vee\vee}$. -/
theorem mem_of_dual {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    {m : ℕ} {L : Submodule A V} (hL : Adapted (K := K) m L L) (v : V)
    (hv : ∀ χ : V →ₗ[K] K, (∀ x ∈ L, χ x ∈ (1 : FractionalIdeal A⁰ K)) →
      χ v ∈ (1 : FractionalIdeal A⁰ K)) : v ∈ L := by
  obtain ⟨e, a, b, -, -, hL1, -⟩ := hL
  rw [hL1, mem_iSup_line_iff]
  intro i
  have key : (((a i)⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) *
      FractionalIdeal.spanSingleton A⁰ (e.coord i v) ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro y hy z hz
    obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hz
    have hχ := hv (y • e.coord i) (by
      intro x hx
      rw [hL1, mem_iSup_line_iff] at hx
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [← Units.val_one, ← inv_mul_cancel (a i), Units.val_mul]
      exact FractionalIdeal.mul_mem_mul hy (FractionalIdeal.mem_coe.1 (hx i)))
    simp only [LinearMap.smul_apply, smul_eq_mul] at hχ
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ t hχ
  have h2 := mul_le_mul' (le_refl ((a i : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)) key
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, mul_one] at h2
  exact FractionalIdeal.mem_coe.2 (h2 (FractionalIdeal.mem_spanSingleton_self _ _))

/-- **Key lemma.** Let $\mathfrak b \ne A$ be the annihilator of $M/N$ and suppose $N$ is reflexive. Then there is a
functional $\psi$ with $\psi(M) \ne 0$ and $\psi(N) \subseteq \mathfrak b\,\psi(M)$. -/
theorem exists_good_functional {V : Type*} [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower A K V] {M N : Submodule A V} (hM : M.FG) (hNM : N ≤ M)
    (hN : Submodule.span K (N : Set V) = ⊤)
    (hrefl : ∀ v : V, (∀ χ : V →ₗ[K] K, (∀ x ∈ N, χ x ∈ (1 : FractionalIdeal A⁰ K)) →
      χ v ∈ (1 : FractionalIdeal A⁰ K)) → v ∈ N)
    (hbtop : N.colon (M : Set V) ≠ ⊤) :
    ∃ ψ : V →ₗ[K] K, M.map (ψ.restrictScalars A) ≠ ⊥ ∧ ∀ v ∈ N,
      ψ v ∈ ((N.colon (M : Set V) : FractionalIdeal A⁰ K) : Submodule A K) *
        M.map (ψ.restrictScalars A) := by
  classical
  set b : Ideal A := N.colon (M : Set V) with hbdef
  have hb0 : b ≠ ⊥ := colon_ne_bot hM hN
  have hb0' : (b : FractionalIdeal A⁰ K) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have hcolon : ∀ r ∈ b, ∀ x ∈ M, r • x ∈ N := fun r hr x hx => Submodule.mem_colon.1 hr x hx
  -- `D χ`: the functional `χ` maps `N` into `b`
  let D : (V →ₗ[K] K) → Prop := fun χ => ∀ x ∈ N, χ x ∈ (b : FractionalIdeal A⁰ K)
  -- (a) such a functional maps `M` into `A`
  have hint : ∀ χ, D χ → ∀ x ∈ M, χ x ∈ (1 : FractionalIdeal A⁰ K) := by
    intro χ hχ x hx
    have key : (b : FractionalIdeal A⁰ K) * FractionalIdeal.spanSingleton A⁰ (χ x) ≤ b := by
      rw [FractionalIdeal.mul_le]
      intro y hy z hz
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hz
      have : algebraMap A K r * (t • χ x) = χ ((r * t) • x) := by
        rw [← algebraMap_smul K (r * t) x, map_smul, smul_eq_mul, Algebra.smul_def, map_mul,
          mul_assoc]
      rw [this, mul_smul]
      exact hχ _ (hcolon r hr _ (M.smul_mem t hx))
    have h2 := mul_le_mul' (le_refl (b : FractionalIdeal A⁰ K)⁻¹) key
    rw [← mul_assoc, inv_mul_cancel₀ hb0', one_mul] at h2
    exact h2 (FractionalIdeal.mem_spanSingleton_self _ _)
  -- (b) for every maximal ideal `p ⊇ b` some such functional is nonzero modulo `p` on `M`
  have hloc : ∀ p : Ideal A, p.IsMaximal → b ≤ p →
      ∃ χ, D χ ∧ ∃ x ∈ M, χ x ∉ (p : FractionalIdeal A⁰ K) := by
    intro p hp hbp
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc⟩ := Ideal.dvd_iff_le.2 hbp
    have hc0 : c ≠ ⊥ := by rintro rfl; rw [Ideal.mul_bot] at hc; exact hb0 hc
    have hc0' : (c : FractionalIdeal A⁰ K) ≠ 0 := by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hp0 : p ≠ ⊥ := by rintro rfl; rw [Ideal.bot_mul] at hc; exact hb0 hc
    have hp0' : (p : FractionalIdeal A⁰ K) ≠ 0 := by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hcb : c ≤ b := by
      intro r hr
      show r ∈ N.colon (M : Set V)
      rw [Submodule.mem_colon]
      intro x hx
      apply hrefl
      intro χ hχ
      have key : (b : FractionalIdeal A⁰ K) * FractionalIdeal.spanSingleton A⁰ (χ x) ≤ p := by
        rw [FractionalIdeal.mul_le]
        intro y hy z hz
        obtain ⟨s, hs, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
        obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hz
        have hD : D (algebraMap A K (s * t) • χ) := by
          intro n hn
          obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1 (hχ n hn)
          rw [LinearMap.smul_apply, ← hu, smul_eq_mul, ← map_mul]
          exact (FractionalIdeal.mem_coeIdeal _).2 ⟨_, b.mul_mem_right _ (b.mul_mem_right _ hs), rfl⟩
        have := hcon _ hD x hx
        convert this using 1
        simp only [LinearMap.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
        ring
      rw [hc, FractionalIdeal.coeIdeal_mul] at key
      have h2 := mul_le_mul' (le_refl (p : FractionalIdeal A⁰ K)⁻¹) key
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hp0', one_mul] at h2
      have := h2 (FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩)
        (FractionalIdeal.mem_spanSingleton_self _ _))
      rwa [← algebraMap_smul K r x, map_smul, smul_eq_mul]
    have h1 : (c : FractionalIdeal A⁰ K) ≤ (p : FractionalIdeal A⁰ K) * c := by
      rw [← FractionalIdeal.coeIdeal_mul, ← hc]
      exact (FractionalIdeal.coeIdeal_le_coeIdeal K).2 hcb
    have h2 := mul_le_mul' h1 (le_refl (c : FractionalIdeal A⁰ K)⁻¹)
    rw [mul_assoc, mul_inv_cancel₀ hc0', mul_one, ← FractionalIdeal.coeIdeal_top,
      FractionalIdeal.coeIdeal_le_coeIdeal] at h2
    exact hp.ne_top (top_le_iff.1 h2)
  -- (c) the finitely many maximal ideals containing `b`, and the Chinese remainder theorem
  set s := (UniqueFactorizationMonoid.normalizedFactors b).toFinset with hs
  have hs_mem : ∀ q ∈ s, Prime q ∧ q.IsMaximal ∧ b ≤ q := by
    intro q hq
    rw [Multiset.mem_toFinset] at hq
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor q hq
    exact ⟨hprime, (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero,
      Ideal.dvd_iff_le.1 (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq)⟩
  have hs_all : ∀ p : Ideal A, p.IsMaximal → b ≤ p → p ∈ s := by
    intro p hp hbp
    rw [Multiset.mem_toFinset]
    have hp0 : p ≠ ⊥ := by rintro rfl; exact hb0 (le_bot_iff.1 hbp)
    obtain ⟨q, hq, hpq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hb0
      (Ideal.prime_of_isPrime hp0 hp.isPrime).irreducible (Ideal.dvd_iff_le.2 hbp)
    rwa [associated_iff_eq.1 hpq]
  choose χ hχD x hxM hχx using fun q : s => hloc q (hs_mem q q.2).2.1 (hs_mem q q.2).2.2
  have hcrt : ∀ q : s, ∃ y : A, ∀ q' : s, y - (if q' = q then 1 else 0) ∈ (q' : Ideal A) := by
    intro q
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) id (fun _ => 1)
      (fun i hi => (hs_mem i hi).1) (fun i _ j _ hij => hij) (fun q' => if q' = q then 1 else 0)
    exact ⟨y, fun q' => by simpa using hy q' q'.2⟩
  choose y hy using hcrt
  set ψ : V →ₗ[K] K := ∑ q : s, algebraMap A K (y q) • χ q with hψ
  have hψD : D ψ := by
    intro n hn
    rw [hψ, LinearMap.sum_apply, ← FractionalIdeal.mem_coe]
    refine Submodule.sum_mem _ fun q _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (FractionalIdeal.mem_coe.2 (hχD q n hn))
  choose t ht using fun q q' : s => (FractionalIdeal.mem_one_iff _).1 (hint _ (hχD q) _ (hxM q'))
  have hψx : ∀ q0 : s, ψ (x q0) = algebraMap A K (∑ q : s, y q * t q q0) := by
    intro q0
    simp [hψ, LinearMap.sum_apply, ← ht, map_sum, map_mul, Algebra.smul_def]
  have hψx_notMem : ∀ q0 : s, (∑ q : s, y q * t q q0) ∉ (q0 : Ideal A) := by
    intro q0 hmem
    have hdiff : (∑ q : s, y q * t q q0) - t q0 q0 ∈ (q0 : Ideal A) := by
      have : (∑ q : s, y q * t q q0) - t q0 q0 =
          ∑ q : s, (y q - if q0 = q then 1 else 0) * t q q0 := by
        simp [sub_mul, Finset.sum_sub_distrib]
      rw [this]
      exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_right _ _ (hy q q0)
    have htq : t q0 q0 ∈ (q0 : Ideal A) := by
      have := sub_mem hmem hdiff
      rwa [sub_sub_cancel] at this
    apply hχx q0
    rw [← ht]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨_, htq, rfl⟩
  -- the ideal `J = ψ(M) ∩ A`
  set J : Ideal A := (M.map (ψ.restrictScalars A)).comap (Algebra.linearMap A K) with hJ
  have hJb : J ⊔ b = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
    have hps := hs_all p hp (le_sup_right.trans hle)
    apply hψx_notMem ⟨p, hps⟩
    apply hle
    apply Ideal.mem_sup_left
    show algebraMap A K _ ∈ M.map (ψ.restrictScalars A)
    rw [← hψx]
    exact Submodule.mem_map_of_mem (hxM _)
  refine ⟨ψ, fun hbot => ?_, fun v hv => ?_⟩
  · apply hbtop
    have hJbot : J = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      have : algebraMap A K r ∈ M.map (ψ.restrictScalars A) := hr
      rw [hbot, Submodule.mem_bot] at this
      exact (Submodule.mem_bot A).2 ((IsFractionRing.injective A K).eq_iff.1 (this.trans (map_zero _).symm))
    rwa [hJbot, bot_sup_eq] at hJb
  · obtain ⟨r, hr, hrv⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hψD v hv)
    have hrJ : r ∈ J := by
      show algebraMap A K r ∈ M.map (ψ.restrictScalars A)
      rw [hrv]
      exact Submodule.mem_map_of_mem (hNM hv)
    have hrbJ : r ∈ b * J := by
      rw [Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 (by rwa [sup_comm]))]
      exact ⟨hr, hrJ⟩
    have : algebraMap A K r ∈ IsLocalization.coeSubmodule K (b * J) := Submodule.mem_map_of_mem hrbJ
    rw [IsLocalization.coeSubmodule_mul] at this
    rw [← hrv, FractionalIdeal.coe_coeIdeal]
    exact mul_le_mul' le_rfl (Submodule.map_comap_le _ _) this

/-- All dimensions. -/
theorem stmt_all (m : ℕ) : Stmt.{u, v, w} A K m := by
  induction m with
  | zero => exact stmt_zero
  | succ m IH =>
    intro V _ _ _ _ hV M N hM hN hNM hspan
    by_cases hbtop : N.colon (M : Set V) = ⊤
    · exact adapted_succ_of_colon_eq_top IH hV hM hNM hspan hbtop
    · have hdiag : Adapted (K := K) (m + 1) N N :=
        adapted_succ_of_colon_eq_top IH hV hN le_rfl hspan (by
          rw [eq_top_iff]
          intro r _
          rw [Submodule.mem_colon]
          intro x hx
          exact N.smul_mem r hx)
      obtain ⟨ψ, hψ, hψN⟩ :=
        exists_good_functional hM hNM hspan (fun v hv => mem_of_dual hdiag v hv) hbtop
      exact adapted_succ_of_functional IH hV hM hNM hspan ψ hψ hψN

end Induction

section Uniqueness

open scoped Pointwise

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

omit [IsDedekindDomain A] [IsFractionRing A K] in
theorem prod_mem_prod_fin {n : ℕ} (f : Fin n → K) (c : Fin n → Submodule A K)
    (h : ∀ i, f i ∈ c i) : ∏ i, f i ∈ ∏ i, c i := by
  induction n with
  | zero => simpa using Submodule.mem_one.2 ⟨1, map_one _⟩
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    exact Submodule.mul_mem_mul (h 0) (ih _ _ fun i => h _)

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- A determinant whose $i$-th column has entries in $c_i$ lies in $\prod_i c_i$. -/
theorem det_mem_prod_of_col {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (c : Fin n → Submodule A K)
    (h : ∀ s i, X s i ∈ c i) : X.det ∈ ∏ i, c i := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hp := prod_mem_prod_fin (fun i => X (σ i) i) c fun i => h _ i
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1]
  · rwa [one_smul]
  · rw [Units.neg_smul, one_smul]; exact neg_mem hp

/-- The **index ideal** $[M : N]$ of two lattices in an $m$-dimensional space: the $A$-submodule of $K$
spanned by the determinants $\det(\chi_s(y_t))$ with $\chi_s(M) \subseteq A$ and $y_t \in N$. It is intrinsic
(it does not depend on any basis). -/
def indexIdeal (m : ℕ) (M N : Submodule A V) : Submodule A K :=
  Submodule.span A {d | ∃ (χ : Fin m → V →ₗ[K] K) (y : Fin m → V),
    (∀ s, ∀ x ∈ M, χ s x ∈ (1 : Submodule A K)) ∧ (∀ t, y t ∈ N) ∧
      d = (Matrix.of fun s t => χ s (y t)).det}

omit [IsFractionRing A K] in
theorem units_inv_mul_mul (a : (FractionalIdeal A⁰ K)ˣ) (d : FractionalIdeal A⁰ K) :
    ((a⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) * ((a : FractionalIdeal A⁰ K) * d) = d := by
  rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- For an adapted decomposition $M = \bigoplus \mathfrak a_i e_i$, $N = \bigoplus \mathfrak a_i\mathfrak d_i e_i$,
the index ideal is $\prod_i \mathfrak d_i$. -/
theorem indexIdeal_eq {m : ℕ} (e : Module.Basis (Fin m) K V) (a : Fin m → (FractionalIdeal A⁰ K)ˣ)
    (d : Fin m → Ideal A) {M N : Submodule A V}
    (hM : M = ⨆ i, line ((a i : FractionalIdeal A⁰ K) : Submodule A K) (e i))
    (hN : N = ⨆ i, line (((a i : FractionalIdeal A⁰ K) * (d i : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K) (e i)) :
    indexIdeal m M N = ∏ i, ((d i : FractionalIdeal A⁰ K) : Submodule A K) := by
  classical
  have hprod : ∏ i, ((d i : FractionalIdeal A⁰ K) : Submodule A K) =
      ∏ i, ((((a i)⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K) *
        (((a i : FractionalIdeal A⁰ K) * (d i : FractionalIdeal A⁰ K) : FractionalIdeal A⁰ K) :
          Submodule A K) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← FractionalIdeal.coe_mul, units_inv_mul_mul]
  apply le_antisymm
  · rw [indexIdeal, Submodule.span_le]
    rintro _ ⟨χ, y, hχ, hy, rfl⟩
    set X : Matrix (Fin m) (Fin m) K := Matrix.of fun s i => χ s (e i) with hX
    set Y : Matrix (Fin m) (Fin m) K := Matrix.of fun i t => e.coord i (y t) with hY
    have hXY : (Matrix.of fun s t => χ s (y t)) = X * Y := by
      ext s t
      simp only [Matrix.of_apply, Matrix.mul_apply, hX, hY]
      rw [show χ s (y t) = χ s (∑ i, e.repr (y t) i • e i) by rw [e.sum_repr], map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
    rw [SetLike.mem_coe, hXY, Matrix.det_mul, hprod, Finset.prod_mul_distrib]
    refine Submodule.mul_mem_mul (det_mem_prod_of_col X _ fun s i => ?_)
      ((Matrix.det_transpose Y) ▸ det_mem_prod_of_col Y.transpose _ fun t i => ?_)
    · -- `χ s (e i) ∈ (a i)⁻¹`
      have key : (a i : FractionalIdeal A⁰ K) * FractionalIdeal.spanSingleton A⁰ (χ s (e i)) ≤ 1 := by
        rw [FractionalIdeal.mul_le]
        intro z hz w hw
        obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hw
        have hze : z • e i ∈ M := by
          rw [hM]; exact Submodule.mem_iSup_of_mem i (smul_mem_line hz)
        have h1 := hχ s _ hze
        rw [map_smul, smul_eq_mul] at h1
        rw [mul_smul_comm, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
        exact Submodule.smul_mem _ r h1
      have h2 := mul_le_mul' (le_refl (((a i)⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)) key
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at h2
      exact FractionalIdeal.mem_coe.2 (h2 (FractionalIdeal.mem_spanSingleton_self _ _))
    · -- `e.coord i (y t) ∈ a i * d i`
      have := (mem_iSup_line_iff e _ (y t)).1 (hN ▸ hy t) i
      simpa [hY] using this
  · rw [hprod]
    simp_rw [Submodule.mul_eq_span_mul_set]
    rw [Submodule.prod_span]
    rw [indexIdeal]
    apply Submodule.span_mono
    intro z hz
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hz
    have hg' : ∀ i, ∃ α ∈ ((((a i)⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) :
        Submodule A K), ∃ β ∈ (((a i : FractionalIdeal A⁰ K) * (d i : FractionalIdeal A⁰ K) :
          FractionalIdeal A⁰ K) : Submodule A K), α * β = g i := fun i =>
      Set.mem_mul.1 (hg (Finset.mem_univ i))
    choose α hα β hβ hαβ using hg'
    refine ⟨fun s => α s • e.coord s, fun t => β t • e t, ?_, ?_, ?_⟩
    · intro s x hx
      rw [hM, mem_iSup_line_iff] at hx
      simp only [LinearMap.smul_apply, smul_eq_mul]
      have : α s * e.coord s x ∈ (((a s)⁻¹ * a s : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
        rw [Units.val_mul]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.1 (hα s))
          (FractionalIdeal.mem_coe.1 (hx s))
      rw [inv_mul_cancel, Units.val_one, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at this
      exact this
    · intro t
      rw [hN]
      exact Submodule.mem_iSup_of_mem t (smul_mem_line (hβ t))
    · have : (Matrix.of fun s t => (α s • e.coord s) (β t • e t)) =
          Matrix.diagonal fun i => α i * β i := by
        ext s t
        by_cases hst : s = t
        · subst hst; simp [mul_comm]
        · simp [Matrix.diagonal_apply_ne _ hst, Finsupp.single_apply, Ne.symm hst]
      rw [this, Matrix.det_diagonal]
      exact Finset.prod_congr rfl fun i _ => (hαβ i).symm

/-- If $M = \bigoplus \mathfrak a_i e_i$ and $N = \bigoplus \mathfrak a_i \mathfrak b_i e_i$, then
$N + \mathfrak c M = \bigoplus \mathfrak a_i(\mathfrak b_i + \mathfrak c) e_i$. -/
theorem sup_smul_eq {m : ℕ} (e : Module.Basis (Fin m) K V) (a : Fin m → (FractionalIdeal A⁰ K)ˣ)
    (b : Fin m → Ideal A) (c : Ideal A) {M N : Submodule A V}
    (hM : M = ⨆ i, line ((a i : FractionalIdeal A⁰ K) : Submodule A K) (e i))
    (hN : N = ⨆ i, line (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K) (e i)) :
    N ⊔ c • M = ⨆ i, line (((a i : FractionalIdeal A⁰ K) * ((b i ⊔ c : Ideal A) :
      FractionalIdeal A⁰ K) : FractionalIdeal A⁰ K) : Submodule A K) (e i) := by
  have hsplit : ∀ i, (((a i : FractionalIdeal A⁰ K) * ((b i ⊔ c : Ideal A) : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K) =
      (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) : FractionalIdeal A⁰ K) :
        Submodule A K) + ((a i : FractionalIdeal A⁰ K) : Submodule A K) *
          ((c : FractionalIdeal A⁰ K) : Submodule A K) := by
    intro i
    simp only [FractionalIdeal.coeIdeal_sup, mul_add, FractionalIdeal.coe_add, FractionalIdeal.coe_mul]
  apply le_antisymm
  · refine sup_le (hN ▸ iSup_mono fun i => line_mono ?_ _) ?_
    · rw [hsplit]; exact le_sup_left
    · intro v hv
      refine Submodule.smul_induction_on hv (fun r hr x hx => ?_) (fun x y hx hy => add_mem hx hy)
      rw [hM, mem_iSup_line_iff] at hx
      rw [mem_iSup_line_iff]
      intro i
      rw [hsplit, ← algebraMap_smul K r x, map_smul, smul_eq_mul, mul_comm (algebraMap A K r)]
      exact Submodule.mem_sup_right (Submodule.mul_mem_mul (hx i)
        (FractionalIdeal.mem_coe.2 ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩)))
  · intro v hv
    rw [mem_iSup_line_iff] at hv
    have hv' : ∀ i, ∃ u ∈ (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) :
        FractionalIdeal A⁰ K) : Submodule A K), ∃ w ∈ ((a i : FractionalIdeal A⁰ K) : Submodule A K) *
          ((c : FractionalIdeal A⁰ K) : Submodule A K), u + w = e.coord i v := fun i =>
      Submodule.mem_sup.1 (by have := hv i; rwa [hsplit i, Submodule.add_eq_sup] at this)
    choose u hu w hw huw using hv'
    rw [← e.sum_repr v]
    have : ∑ i, e.repr v i • e i = ∑ i, u i • e i + ∑ i, w i • e i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← add_smul, huw, Module.Basis.coord_apply]
    rw [this]
    refine Submodule.add_mem_sup (hN ▸ Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (smul_mem_line (hu i))) (Submodule.sum_mem _ fun i _ => ?_)
    have hle : ((a i : FractionalIdeal A⁰ K) : Submodule A K) *
        ((c : FractionalIdeal A⁰ K) : Submodule A K) ≤
          (c • M).comap ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A) := by
      rw [Submodule.mul_le]
      intro z hz y hy
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 (FractionalIdeal.mem_coe.1 hy)
      simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars,
        LinearMap.toSpanSingleton_apply]
      rw [mul_comm, mul_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul hr (hM ▸ Submodule.mem_iSup_of_mem i (smul_mem_line hz))
    exact hle (hw i)

omit [IsFractionRing A K] in
/-- One half of the cancellation argument: if two decreasing chains of nonzero ideals satisfy
$\prod_i(\mathfrak b_i + \mathfrak c) = \prod_i(\mathfrak b'_i + \mathfrak c)$ for every ideal $\mathfrak c$ and
agree below $k$, then $\mathfrak b'_k \subseteq \mathfrak b_k$. -/
theorem chain_le_of_prod_eq {m : ℕ} (b b' : Fin m → Ideal A) (hb0 : ∀ i, b i ≠ ⊥)
    (hb : ∀ i j, i ≤ j → b j ≤ b i)
    (h : ∀ c : Ideal A, ∏ i, (b i ⊔ c) = ∏ i, (b' i ⊔ c)) (k : Fin m)
    (hlt : ∀ i, i < k → b i = b' i) : b' k ≤ b k := by
  classical
  set f : Fin m → Ideal A := fun i => b i ⊔ b k with hf
  set g : Fin m → Ideal A := fun i => b' i ⊔ b k with hg
  have hfg : ∏ i, f i = ∏ i, g i := h (b k)
  have hgf : ∀ i ∈ Finset.univ.erase k, g i ∣ f i := by
    intro i hi
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with hik | hik
    · rw [hf, hg]; simp only; rw [hlt i hik]
    · rw [Ideal.dvd_iff_le]
      simp only [hf, hg]
      rw [sup_eq_right.2 (hb k i hik.le)]
      exact le_sup_right
  obtain ⟨Q, hQ⟩ := Finset.prod_dvd_prod_of_dvd g f hgf
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ k), hQ] at hfg
  have hG : ∏ i ∈ Finset.univ.erase k, g i ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [Ne, Ideal.zero_eq_bot, ← le_bot_iff]
    intro hle
    exact hb0 k (le_bot_iff.1 (le_sup_right.trans hle))
  have hfk : f k = b k := sup_idem _
  rw [hfk, mul_left_comm] at hfg
  have hgk : g k = b k * Q := (mul_left_cancel₀ hG (hfg.trans (mul_comm _ _))).symm
  exact le_sup_left.trans (Ideal.dvd_iff_le.1 ⟨Q, hgk⟩)

omit [IsFractionRing A K] in
theorem chain_eq_of_prod_eq {m : ℕ} (b b' : Fin m → Ideal A) (hb0 : ∀ i, b i ≠ ⊥)
    (hb'0 : ∀ i, b' i ≠ ⊥) (hb : ∀ i j, i ≤ j → b j ≤ b i) (hb' : ∀ i j, i ≤ j → b' j ≤ b' i)
    (h : ∀ c : Ideal A, ∏ i, (b i ⊔ c) = ∏ i, (b' i ⊔ c)) : b = b' := by
  have key : ∀ n, ∀ k : Fin m, k.val = n → b k = b' k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      have hlt : ∀ i, i < k → b i = b' i := fun i hi => ih i.val (by rw [← hk]; exact hi) i rfl
      exact le_antisymm
        (chain_le_of_prod_eq b' b hb'0 hb' (fun c => (h c).symm) k fun i hi => (hlt i hi).symm)
        (chain_le_of_prod_eq b b' hb0 hb h k hlt)
  funext k
  exact key _ k rfl

omit [IsFractionRing A K] in
theorem coe_prod_coeIdeal {m : ℕ} (I : Fin m → Ideal A) :
    ∏ i, ((I i : FractionalIdeal A⁰ K) : Submodule A K) =
      (((∏ i, I i : Ideal A) : FractionalIdeal A⁰ K) : Submodule A K) := by
  have h1 := map_prod (FractionalIdeal.coeSubmoduleHom A⁰ K) (fun i => (I i : FractionalIdeal A⁰ K))
    Finset.univ
  have h2 := map_prod (FractionalIdeal.coeIdealHom A⁰ K) I Finset.univ
  exact h1.symm.trans (congrArg (FractionalIdeal.coeSubmoduleHom A⁰ K) h2.symm)

/-- **Theorem 3.32** (invariant factor theorem), uniqueness: the invariant factors $\mathfrak b_i$ of an adapted
decomposition depend only on the pair $N \subseteq M$. -/
@[kb "milne2020ant" "v3.08, Thm. 3.32 (uniqueness of the invariant factors), p. 58"]
theorem thm_3_32_unique (m : ℕ) (M N : Submodule A V) (e e' : Module.Basis (Fin m) K V)
    (a a' : Fin m → (FractionalIdeal A⁰ K)ˣ) (b b' : Fin m → Ideal A) (hb0 : ∀ i, b i ≠ ⊥)
    (hb : ∀ i j, i ≤ j → b j ≤ b i) (hb'0 : ∀ i, b' i ≠ ⊥) (hb' : ∀ i j, i ≤ j → b' j ≤ b' i)
    (hMe : M = ⨆ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K).map
      ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A))
    (hNe : N = ⨆ i, (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K).map ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A))
    (hMe' : M = ⨆ i, ((a' i : FractionalIdeal A⁰ K) : Submodule A K).map
      ((LinearMap.toSpanSingleton K V (e' i)).restrictScalars A))
    (hNe' : N = ⨆ i, (((a' i : FractionalIdeal A⁰ K) * (b' i : FractionalIdeal A⁰ K) :
      FractionalIdeal A⁰ K) : Submodule A K).map
        ((LinearMap.toSpanSingleton K V (e' i)).restrictScalars A)) :
    b = b' := by
  refine chain_eq_of_prod_eq b b' hb0 hb'0 hb hb' fun c => ?_
  have h1 := indexIdeal_eq e a (fun i => b i ⊔ c) hMe (sup_smul_eq e a b c hMe hNe)
  have h2 := indexIdeal_eq e' a' (fun i => b' i ⊔ c) hMe' (sup_smul_eq e' a' b' c hMe' hNe')
  have h3 := h1.symm.trans h2
  rw [coe_prod_coeIdeal, coe_prod_coeIdeal] at h3
  exact FractionalIdeal.coeIdeal_injective (FractionalIdeal.coeToSubmodule_injective h3)

end Uniqueness

section Main

universe u

variable {A : Type u} [CommRing A] [IsDedekindDomain A] {K : Type u} [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- **Theorem 3.32** (invariant factor theorem), existence. Let $N \subseteq M$ be finitely generated
$A$-submodules of an $m$-dimensional $K$-vector space $V$, with $N$ spanning $V$. Then there are a $K$-basis
$e_0, \dots, e_{m-1}$ of $V$, invertible fractional ideals $\mathfrak a_i$ and nonzero integral ideals
$\mathfrak b_0 \supseteq \mathfrak b_1 \supseteq \cdots \supseteq \mathfrak b_{m-1}$ with
$M = \bigoplus_i \mathfrak a_i e_i$ and $N = \bigoplus_i \mathfrak a_i \mathfrak b_i e_i$.
(Indices are $0$-based; Milne's $\mathfrak b_1 \supseteq \cdots \supseteq \mathfrak b_m$.) -/
@[kb "milne2020ant" "v3.08, Thm. 3.32 (existence), p. 58"]
theorem thm_3_32_exists (V : Type u) [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower A K V] (m : ℕ) (hV : Module.finrank K V = m) (M N : Submodule A V) (hM : M.FG)
    (hN : N.FG) (hNM : N ≤ M) (hspan : Submodule.span K (N : Set V) = ⊤) :
    ∃ (e : Module.Basis (Fin m) K V) (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (b : Fin m → Ideal A),
      (∀ i, b i ≠ ⊥) ∧ (∀ i j, i ≤ j → b j ≤ b i) ∧
      M = ⨆ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K).map
        ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A) ∧
      N = ⨆ i, (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) : FractionalIdeal A⁰ K) :
        Submodule A K).map ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A) := by
  obtain ⟨e, a, b, hb0, hbmono, hMe, hNe⟩ := stmt_all.{u, u, u} (A := A) (K := K) m V hV M N hM hN hNM hspan
  have key : ∀ g : Fin m → Submodule A V, (⨆ i, g (Fin.rev i)) = ⨆ i, g i := fun g =>
    Equiv.iSup_comp (g := g) Fin.revPerm
  refine ⟨e.reindex Fin.revPerm, a ∘ Fin.rev, b ∘ Fin.rev, fun i => hb0 _,
    fun i j hij => hbmono (Fin.rev_le_rev.2 hij), ?_, ?_⟩
  · rw [hMe, ← key]
    simp [line, Module.Basis.reindex_apply]
  · rw [hNe, ← key]
    simp [line, Module.Basis.reindex_apply]

end Main

/-- **Theorem 3.32** (Milne's invariant factor theorem), proved: the named statement
`NumberFieldKB.MilneANT.InvariantFactorTheorem` holds for every Dedekind domain. -/
@[kb "milne2020ant" "v3.08, Thm. 3.32 and definition in prose (invariant factors), p. 58"]
theorem invariantFactorTheorem.{u} (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] : InvariantFactorTheorem A K where
  exists_adapted V _ _ _ _ m hV M N hM hN hNM hspan := thm_3_32_exists V m hV M N hM hN hNM hspan
  unique _ _ _ _ _ m M N e e' a a' b b' hb0 hb hb'0 hb' hMe hNe hMe' hNe' :=
    thm_3_32_unique m M N e e' a a' b b' hb0 hb hb'0 hb' hMe hNe hMe' hNe'

end NumberFieldKB.MilneANT.InvariantFactors
