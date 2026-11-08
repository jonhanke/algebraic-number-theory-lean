import NumberFieldKB.WeilBNT.FunctionField.WeilDifferential

/-!
# F. K. Schmidt's theorem: a divisor of degree 1 (Weil VII.§5, Cor. 5)

Weil's proof (VII.§5, Cor. 5, p. 126): let $\nu$ be the g.c.d. of the degrees of the places and $k'=k\mathbb F_{q^\nu}$;
by III.§1 Prop. 1, III.§4 Thm. 4 Cor. 1 and I.§1 Thm. 2, every place of $k$ has exactly $\nu=[k':k]$ places of $k'$
above it, each with the same residue field; Cor. 4 (via the pole of the zeta function, Cor. 3) then forces
$\nu=1$.

The splitting of the places of $k$ in the constant field extension is isolated as a proposition and proved in
`PlaceSplitting.lean` (`weilSchmidtInput`, giving the unconditional `weil_VII_5_cor5_ff`):
**`WeilSchmidtInput Fq k`** asks, when $\mathbb F_q$ is the field of constants, for every $n\ge1$ dividing all the
degrees $\deg v$, for a global function field
$k'$ over $\mathbb F_q$ and a bijection $\{\text{places of }k'\}\simeq\{\text{places of }k\}\times\{1,\dots,n\}$ preserving
degrees over $\mathbb F_q$ (the constant field extension $k\mathbb F_{q^n}$ has this property). It says nothing about
divisors of degree 1. From it, the zeta-function argument is formalized with Riemann–Roch in place of the analytic
pole:

* **`effCount_le`**: $A_m\le C\,q^m$ for the number $A_m$ of effective divisors of degree $m$ (any global function
  field, via the finiteness of $D_0/P$ and $\lambda(\mathfrak a)\le\deg\mathfrak a+\lambda(0)$).
* **`effCount_ge`**: if $\mathbb F_q$ is the field of constants and $k$ has a divisor of degree $m\ge2g-1$, then
  $A_m\ge q^{m-g-1}$ (Riemann–Roch).
* **`effCount_split_ge`**: with $n\ge2$ and a degree-preserving $\{\text{places of }k'\}\simeq\{\text{places of }k\}
  \times\{1,\dots,n\}$, $A'_m\ge\sum_{j\le m}A_jA_{m-j}$.
* **`weil_VII_5_cor5`**: with $\mathbb F_q$ the field of constants and the input, there is a divisor of degree $1$.
-/

open scoped Polynomial

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

universe u v

variable {Fq : Type u} {k : Type v} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

variable (Fq k) in
/-- **Named input** (the constant field extension, Weil III.§1 Prop. 1, III.§4 Thm. 4 Cor. 1, I.§1 Thm. 2, used in
VII.§5 Cor. 5): if $\mathbb F_q$ is the field of constants and $n\ge1$ divides the degree of every place of $k$, there is a global function field $k'$ over
$\mathbb F_q$ (namely $k\mathbb F_{q^n}$) whose places correspond to pairs (place of $k$, index $<n$), with the same
degree over $\mathbb F_q$. -/
def WeilSchmidtInput : Prop :=
  IsConstantField Fq k → ∀ n : ℕ, 0 < n → (∀ v : Place Fq k, n ∣ v.degree) →
    ∃ (k' : Type v) (_ : Field k') (_ : Algebra Fq k') (_ : Algebra (RatFunc Fq) k')
      (_ : IsScalarTower Fq (RatFunc Fq) k') (_ : FunctionField Fq k')
      (e : Place Fq k' ≃ Place Fq k × Fin n), ∀ w : Place Fq k', (e w).1.degree = w.degree

/-- The number of effective divisors in a divisor class is at most $q^{\lambda(\mathfrak a)}$ (no hypothesis on the
constants), and is finite. -/
theorem effClassCount_le_pow (a : Divisor Fq k) :
    Finite {b : Divisor Fq k // 0 ≤ b ∧ b - a ∈ principalDivisors Fq k} ∧
      effClassCount a ≤ Nat.card Fq ^ a.ell := by
  classical
  haveI := Divisor.finiteDimensional_riemannRochSpace (Fq := Fq) (k := k) a
  haveI : Finite a.riemannRochSpace := Module.finite_of_finite Fq
  let Xu := {u : kˣ // (u : k) ∈ a.riemannRochSpace}
  let S := {b : Divisor Fq k // 0 ≤ b ∧ b - a ∈ principalDivisors Fq k}
  let ψ : Xu → S := fun u => ⟨a + Divisor.div u.1, (nonneg_add_div_iff a u.1).mpr u.2,
    by rw [add_sub_cancel_left]; exact (mem_principalDivisors_iff _).mpr ⟨u.1, rfl⟩⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨b, hb0, hb⟩
    obtain ⟨u, hu⟩ := (mem_principalDivisors_iff _).mp hb
    have hb' : b = a + Divisor.div u := by rw [hu]; abel
    exact ⟨⟨u, (nonneg_add_div_iff a u).mp (hb' ▸ hb0)⟩, Subtype.ext hb'.symm⟩
  have hinj : Function.Injective
      (fun u : Xu => (⟨(u.1 : k), u.2⟩ : a.riemannRochSpace)) := by
    intro x y h; exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  haveI : Finite Xu := Finite.of_injective _ hinj
  haveI : Finite S := Finite.of_surjective ψ hψ
  refine ⟨inferInstance, ?_⟩
  calc effClassCount a = Nat.card S := rfl
    _ ≤ Nat.card Xu := Nat.card_le_card_of_surjective ψ hψ
    _ ≤ Nat.card a.riemannRochSpace := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card Fq ^ a.ell := natCard_eq_pow_finrank _

/-- The number of effective divisors of degree $m$ grows at most like $q^m$. -/
theorem effCount_le : ∃ C : ℕ, ∀ m : ℕ, effCount Fq k m ≤ C * Nat.card Fq ^ m := by
  classical
  haveI := finite_classGroup0 (Fq := Fq) (k := k)
  haveI := Fintype.ofFinite (ClassGroup0 Fq k)
  refine ⟨Nat.card (ClassGroup0 Fq k) * Nat.card Fq ^ (0 : Divisor Fq k).ell, fun m => ?_⟩
  by_cases hne : ∃ b₀ : Divisor Fq k, 0 ≤ b₀ ∧ Divisor.deg b₀ = m
  swap
  · have : effCount Fq k m = 0 := by
      unfold effCount
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨b, hb⟩ => hne ⟨b, hb⟩⟩
    rw [this]; exact Nat.zero_le _
  obtain ⟨b₀, hb₀, hdeg₀⟩ := hne
  let S := {b : Divisor Fq k // 0 ≤ b ∧ Divisor.deg b = m}
  have hmem : ∀ b : S, b.1 - b₀ ∈ (Divisor.deg (Fq := Fq) (k := k)).ker := fun b => by
    simp [AddMonoidHom.mem_ker, b.2.2, hdeg₀]
  let φ : S → ClassGroup0 Fq k := fun b => QuotientAddGroup.mk ⟨b.1 - b₀, hmem b⟩
  haveI hfin : Finite S :=
    (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (m : ℤ)).to_subtype
  have hfib : ∀ c, Nat.card {b : S // φ b = c} ≤
      Nat.card Fq ^ (0 : Divisor Fq k).ell * Nat.card Fq ^ m := by
    intro c
    by_cases hc : Nonempty {b : S // φ b = c}
    swap
    · rw [not_nonempty_iff] at hc
      rw [Nat.card_of_isEmpty]; exact Nat.zero_le _
    obtain ⟨⟨b₁, h1⟩⟩ := hc
    obtain ⟨hfinB, hle⟩ := effClassCount_le_pow b₁.1
    have hell := Divisor.ell_le_of_le (Fq := Fq) (k := k) b₁.2.1
    rw [map_zero, sub_zero, b₁.2.2] at hell
    have hell' : b₁.1.ell ≤ (0 : Divisor Fq k).ell + m := by omega
    let f : {b : S // φ b = c} →
        {b : Divisor Fq k // 0 ≤ b ∧ b - b₁.1 ∈ principalDivisors Fq k} :=
      fun b => ⟨b.1.1, b.1.2.1, by
        have h2 : φ b₁ = φ b.1 := h1.trans b.2.symm
        have h3 := (QuotientAddGroup.eq).mp h2
        rw [AddSubgroup.mem_addSubgroupOf] at h3
        have e : b.1.1 - b₁.1 = (-(b₁.1 - b₀) + (b.1.1 - b₀)) := by abel
        rw [e]; exact h3⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
    calc Nat.card {b : S // φ b = c} ≤ effClassCount b₁.1 := Nat.card_le_card_of_injective f hf
      _ ≤ Nat.card Fq ^ b₁.1.ell := hle
      _ ≤ Nat.card Fq ^ ((0 : Divisor Fq k).ell + m) :=
          Nat.pow_le_pow_right Nat.card_pos hell'
      _ = _ := pow_add _ _ _
  unfold effCount
  calc Nat.card S = ∑ c, Nat.card {b : S // φ b = c} := by
        rw [← Nat.card_sigma]; exact Nat.card_congr (Equiv.sigmaFiberEquiv φ).symm
    _ ≤ ∑ _c : ClassGroup0 Fq k, Nat.card Fq ^ (0 : Divisor Fq k).ell * Nat.card Fq ^ m :=
        Finset.sum_le_sum fun c _ => hfib c
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, mul_assoc]

/-- With $\mathbb F_q$ the field of constants: if there is a divisor of degree $m\ge2g-1$, then $A_m\ge q^{m-g-1}$. -/
theorem effCount_ge (hc : IsConstantField Fq k) (m : ℕ) (hm : 2 * Rep.genusInt Fq k - 1 ≤ m)
    (hdeg : ∃ a : Divisor Fq k, Divisor.deg a = m) :
    (Nat.card Fq : ℤ) ^ m ≤ (Nat.card Fq : ℤ) ^ ((Rep.genusInt Fq k).toNat + 1) * effCount Fq k m := by
  classical
  obtain ⟨a, ha⟩ := hdeg
  set g := Rep.genusInt Fq k with hg
  have hq : 2 ≤ Nat.card Fq := Finite.one_lt_card
  have e0 := weil_VI_2_thm2 (Fq := Fq) (k := k) 0
  have ec := weil_VI_2_thm2 (Fq := Fq) (k := k) (canonical Fq k)
  simp only [sub_zero, sub_self, map_zero] at e0 ec
  have hdc : Divisor.deg (canonical Fq k) = 2 * g - 2 := by omega
  have hneg : Divisor.deg (canonical Fq k - a) < 0 := by
    rw [map_sub, hdc, ha]; omega
  have h0 := Divisor.ell_eq_zero_of_deg_neg' hneg
  have hRR := weil_VI_2_thm2 (Fq := Fq) (k := k) a
  rw [h0, ha] at hRR
  -- the number of effective divisors in the class of `a`
  have hspec := effClassCount_spec_of_fd hc a (Divisor.finiteDimensional_riemannRochSpace a)
  have hfin : Finite {b : Divisor Fq k // 0 ≤ b ∧ Divisor.deg b = m} :=
    (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (m : ℤ)).to_subtype
  have hN : effClassCount a ≤ effCount Fq k m := by
    refine Nat.card_le_card_of_injective
      (fun b : {b : Divisor Fq k // 0 ≤ b ∧ b - a ∈ principalDivisors Fq k} =>
        (⟨b.1, b.2.1, ?_⟩ : {b : Divisor Fq k // 0 ≤ b ∧ Divisor.deg b = m})) ?_
    · obtain ⟨u, hu⟩ := (mem_principalDivisors_iff _).mp b.2.2
      have : b.1 = a + Divisor.div u := by rw [hu]; abel
      rw [this, map_add, Divisor.deg_div_eq_zero, ha, add_zero]
    · intro x y h
      exact Subtype.ext (congrArg (fun z => z.1) h)
  set N := effClassCount a
  set E := effCount Fq k m
  set q := Nat.card Fq
  have hell1 : 1 ≤ a.ell := by omega
  have hN1 : 1 ≤ N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0, mul_zero, zero_add] at hspec
    have : q ^ 1 ≤ q ^ a.ell := Nat.pow_le_pow_right (by omega) hell1
    rw [pow_one] at this
    omega
  have hqE : q ^ a.ell ≤ q * E := by
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [← hspec, hr]
    have := Nat.mul_le_mul_left (q - 1) hN
    have h1 : 1 ≤ E := le_trans hN1 hN
    rw [hr] at this
    simp only [Nat.add_sub_cancel] at this ⊢
    nlinarith
  have hexp : m ≤ a.ell + g.toNat := by omega
  have : q ^ m ≤ q ^ (g.toNat + 1) * E := by
    calc q ^ m ≤ q ^ (a.ell + g.toNat) := Nat.pow_le_pow_right (by omega) hexp
      _ = q ^ a.ell * q ^ g.toNat := pow_add _ _ _
      _ ≤ (q * E) * q ^ g.toNat := Nat.mul_le_mul_right _ hqE
      _ = q ^ (g.toNat + 1) * E := by rw [pow_succ]; ring
  exact_mod_cast this

theorem finite_eff_aux {k : Type*} [Field k] [Algebra Fq k] [Algebra (RatFunc Fq) k]
    [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k] (n : ℕ) :
    Finite {a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = n} :=
  (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).to_subtype

theorem deg_mapDomain_aux {k' : Type*} [Field k'] [Algebra Fq k'] [Algebra (RatFunc Fq) k']
    [IsScalarTower Fq (RatFunc Fq) k'] [FunctionField Fq k'] (f : Place Fq k → Place Fq k')
    (hf : ∀ v, (f v).degree = v.degree) (D : Divisor Fq k) :
    Divisor.deg (Finsupp.mapDomain f D : Divisor Fq k') = Divisor.deg D := by
  have : (Divisor.deg (Fq := Fq) (k := k')).comp (Finsupp.mapDomain.addMonoidHom f) =
      Divisor.deg := by
    apply Finsupp.addHom_ext
    intro v n
    simp [Divisor.deg_single, hf]
  exact DFunLike.congr_fun this D

theorem mapDomain_nonneg_aux {k' : Type*} [Field k'] [Algebra Fq k'] [Algebra (RatFunc Fq) k']
    [IsScalarTower Fq (RatFunc Fq) k'] [FunctionField Fq k'] (f : Place Fq k → Place Fq k')
    (hf : Function.Injective f) {D : Divisor Fq k} (hD : 0 ≤ D) :
    (0 : Divisor Fq k') ≤ Finsupp.mapDomain f D := by
  intro w
  by_cases hw : w ∈ Set.range f
  · obtain ⟨v, rfl⟩ := hw
    rw [Finsupp.mapDomain_apply_of_injective hf]
    exact hD v
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hw]; exact le_rfl

/-- A degree-preserving correspondence between the places of $k'$ and $n\ge2$ copies of the places of $k$ gives
$A'_m\ge\sum_{j\le m}A_jA_{m-j}$. -/
theorem effCount_split_ge {k' : Type*} [Field k'] [Algebra Fq k'] [Algebra (RatFunc Fq) k']
    [IsScalarTower Fq (RatFunc Fq) k'] [FunctionField Fq k'] {n : ℕ} (hn : 2 ≤ n)
    (e : Place Fq k' ≃ Place Fq k × Fin n) (he : ∀ w : Place Fq k', (e w).1.degree = w.degree)
    (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), effCount Fq k j * effCount Fq k (m - j) ≤ effCount Fq k' m := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi : i1 ≠ i0 := fun h => by simpa [i0, i1] using congrArg Fin.val h
  let f0 : Place Fq k → Place Fq k' := fun v => e.symm (v, i0)
  let f1 : Place Fq k → Place Fq k' := fun v => e.symm (v, i1)
  have hdeg : ∀ (i : Fin n) (v : Place Fq k), (e.symm (v, i)).degree = v.degree := by
    intro i v
    have := he (e.symm (v, i))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hf0 : Function.Injective f0 := fun x y h => by
    have := e.symm.injective h
    exact (Prod.mk.inj this).1
  have hf1 : Function.Injective f1 := fun x y h => by
    have := e.symm.injective h
    exact (Prod.mk.inj this).1
  have h01 : ∀ u v, f1 u ≠ f0 v := fun u v h => by
    have := e.symm.injective h
    exact hi (Prod.mk.inj this).2
  have h10 : ∀ u v, f0 u ≠ f1 v := fun u v h => h01 v u h.symm
  let T := Σ j : Fin (m + 1), ({a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = ((j : ℕ) : ℤ)} ×
    {a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = ((m - (j : ℕ) : ℕ) : ℤ)})
  haveI : ∀ j : Fin (m + 1), Finite ({a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = ((j : ℕ) : ℤ)} ×
    {a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = ((m - (j : ℕ) : ℕ) : ℤ)}) := fun j => by
    haveI := finite_eff_aux (Fq := Fq) (k := k) (j : ℕ)
    haveI := finite_eff_aux (Fq := Fq) (k := k) (m - (j : ℕ))
    infer_instance
  haveI := finite_eff_aux (Fq := Fq) (k := k') m
  let F : T → {a : Divisor Fq k' // 0 ≤ a ∧ Divisor.deg a = m} := fun x =>
    ⟨Finsupp.mapDomain f0 x.2.1.1 + Finsupp.mapDomain f1 x.2.2.1,
      add_nonneg (mapDomain_nonneg_aux f0 hf0 x.2.1.2.1) (mapDomain_nonneg_aux f1 hf1 x.2.2.2.1), by
        rw [map_add, deg_mapDomain_aux f0 (hdeg i0), deg_mapDomain_aux f1 (hdeg i1),
          x.2.1.2.2, x.2.2.2.2]
        have := x.1.is_lt
        push_cast [Nat.cast_sub (by omega : (x.1 : ℕ) ≤ m)]
        ring⟩
  have hev0 : ∀ (D1 D2 : Divisor Fq k) (v : Place Fq k),
      (Finsupp.mapDomain f0 D1 + Finsupp.mapDomain f1 D2) (f0 v) = D1 v := by
    intro D1 D2 v
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective hf0,
      Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨u, hu⟩; exact h01 u v hu), add_zero]
  have hev1 : ∀ (D1 D2 : Divisor Fq k) (v : Place Fq k),
      (Finsupp.mapDomain f0 D1 + Finsupp.mapDomain f1 D2) (f1 v) = D2 v := by
    intro D1 D2 v
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective hf1,
      Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨u, hu⟩; exact h10 u v hu), zero_add]
  have hF : Function.Injective F := by
    rintro ⟨j, ⟨D1, h1⟩, ⟨D2, h2⟩⟩ ⟨j', ⟨D1', h1'⟩, ⟨D2', h2'⟩⟩ hFe
    have hv := congrArg Subtype.val hFe
    simp only [F] at hv
    have e1 : D1 = D1' := by
      ext v
      rw [← hev0 D1 D2 v, hv, hev0]
    have e2 : D2 = D2' := by
      ext v
      rw [← hev1 D1 D2 v, hv, hev1]
    subst e1 e2
    have : j = j' := Fin.ext (by have := h1.2.symm.trans h1'.2; exact_mod_cast this)
    subst this
    rfl
  have hcard : Nat.card T =
      ∑ j ∈ Finset.range (m + 1), effCount Fq k j * effCount Fq k (m - j) := by
    rw [Nat.card_sigma, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.card_prod]
    rfl
  rw [← hcard]
  exact Nat.card_le_card_of_injective F hF

/-- The degrees of divisors form $\nu\mathbb Z$ with $\nu$ dividing every $\deg v$ and some divisor of degree $\nu$. -/
theorem exists_index : ∃ ν : ℕ, 0 < ν ∧ (∀ v : Place Fq k, ν ∣ v.degree) ∧
    ∃ a : Divisor Fq k, Divisor.deg a = ν := by
  classical
  haveI := Int.subgroup_cyclic (Divisor.deg (Fq := Fq) (k := k)).range
  obtain ⟨gen, hgen⟩ := IsAddCyclic.exists_generator (α := (Divisor.deg (Fq := Fq) (k := k)).range)
  obtain ⟨D, hD⟩ := gen.2
  have hv : ∀ v : Place Fq k, (gen.1) ∣ (v.degree : ℤ) := by
    intro v
    have hx : (v.degree : ℤ) ∈ (Divisor.deg (Fq := Fq) (k := k)).range :=
      ⟨Finsupp.single v 1, by simp [Divisor.deg_single]⟩
    obtain ⟨n, hn⟩ := hgen ⟨_, hx⟩
    have := congrArg Subtype.val hn
    simp at this
    exact ⟨n, by rw [← this]; ring⟩
  obtain ⟨P⟩ := Place.nonempty (Fq := Fq) (k := k)
  have ha0 : gen.1 ≠ 0 := by
    intro h0
    have := hv P
    rw [h0, zero_dvd_iff] at this
    have := P.degree_pos
    omega
  refine ⟨gen.1.natAbs, Int.natAbs_pos.mpr ha0, fun v => ?_, ?_⟩
  · have := Int.natAbs_dvd_natAbs.mpr (hv v)
    simpa using this
  · rcases Int.natAbs_eq gen.1 with h | h
    · exact ⟨D, by rw [hD]; exact h⟩
    · refine ⟨-D, ?_⟩
      rw [map_neg, hD]
      omega

/-- **F. K. Schmidt's theorem** (Weil VII.§5, Cor. 5, with $P=\emptyset$): if $\mathbb F_q$ is the field of constants,
$k$ has a divisor of degree $1$, given the constant field extension input. -/
theorem weil_VII_5_cor5 (hc : IsConstantField Fq k) (H : WeilSchmidtInput Fq k) :
    ∃ a : Divisor Fq k, Divisor.deg a = 1 := by
  classical
  obtain ⟨ν, hν0, hdv, a0, ha0⟩ := exists_index (Fq := Fq) (k := k)
  by_cases hν1 : ν = 1
  · subst hν1
    exact ⟨a0, by simpa using ha0⟩
  exfalso
  have hν2 : 2 ≤ ν := by omega
  obtain ⟨k', i1, i2, i3, i4, i5, e, he⟩ := H hc ν hν0 hdv
  obtain ⟨C, hC⟩ := effCount_le (Fq := Fq) (k := k')
  have hq : 2 ≤ Nat.card Fq := Finite.one_lt_card
  set q := Nat.card Fq with hqdef
  set g := Rep.genusInt Fq k with hg
  set G := g.toNat with hG
  set s₀ := (2 * g).toNat with hs₀
  set M := q ^ (2 * G + 2) * C with hM
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 * s₀ + M + 1 := ⟨_, rfl⟩
  have hsplit := effCount_split_ge (Fq := Fq) (k := k) (k' := k') hν2 e he (ν * t)
  have hterm : ∀ s ∈ Finset.Icc s₀ (t - s₀),
      q ^ (ν * t) ≤ q ^ (2 * G + 2) * (effCount Fq k (ν * s) * effCount Fq k (ν * t - ν * s)) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hu : ν * t - ν * s = ν * (t - s) := (mul_tsub ν t s).symm
    have hs1 : s ≤ ν * s := Nat.le_mul_of_pos_left _ hν0
    have hu1 : t - s ≤ ν * (t - s) := Nat.le_mul_of_pos_left _ hν0
    have hge : ∀ r : ℕ, s₀ ≤ r →
        (q : ℤ) ^ (ν * r) ≤ (q : ℤ) ^ (G + 1) * effCount Fq k (ν * r) := by
      intro r hr
      have hr1 : r ≤ ν * r := Nat.le_mul_of_pos_left _ hν0
      have hs0 : 2 * g ≤ (s₀ : ℤ) := by rw [hs₀]; exact Int.self_le_toNat _
      refine effCount_ge hc (ν * r) (by push_cast; omega) ⟨r • a0, ?_⟩
      rw [map_nsmul, ha0]
      simp
      ring
    have h1 := hge s hs.1
    have h2 := hge (t - s) (by omega)
    rw [← hu] at h2
    have h3 : (q : ℤ) ^ (ν * t) ≤
        (q : ℤ) ^ (2 * G + 2) * ((effCount Fq k (ν * s) : ℤ) * effCount Fq k (ν * t - ν * s)) := by
      have hle : ν * s ≤ ν * t := Nat.mul_le_mul_left _ (by omega)
      have e1 : (q : ℤ) ^ (ν * t) = (q : ℤ) ^ (ν * s) * (q : ℤ) ^ (ν * t - ν * s) := by
        rw [← pow_add]; congr 1; omega
      rw [e1]
      calc (q : ℤ) ^ (ν * s) * (q : ℤ) ^ (ν * t - ν * s)
          ≤ ((q : ℤ) ^ (G + 1) * effCount Fq k (ν * s)) *
            ((q : ℤ) ^ (G + 1) * effCount Fq k (ν * t - ν * s)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    exact_mod_cast h3
  have hsum1 : (Finset.Icc s₀ (t - s₀)).card * q ^ (ν * t) ≤
      q ^ (2 * G + 2) * ∑ s ∈ Finset.Icc s₀ (t - s₀),
        effCount Fq k (ν * s) * effCount Fq k (ν * t - ν * s) := by
    rw [Finset.mul_sum, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  have hsum2 : ∑ s ∈ Finset.Icc s₀ (t - s₀), effCount Fq k (ν * s) * effCount Fq k (ν * t - ν * s) ≤
      ∑ j ∈ Finset.range (ν * t + 1), effCount Fq k j * effCount Fq k (ν * t - j) := by
    have hinj : Function.Injective (fun s : ℕ => ν * s) := fun x y h => by
      exact Nat.eq_of_mul_eq_mul_left hν0 h
    rw [← Finset.sum_image (f := fun j => effCount Fq k j * effCount Fq k (ν * t - j))
      (g := fun s : ℕ => ν * s) (fun x _ y _ h => hinj h)]
    refine Finset.sum_le_sum_of_subset ?_
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨s, hs, rfl⟩ := hj
    rw [Finset.mem_Icc] at hs
    rw [Finset.mem_range]
    have : ν * s ≤ ν * t := Nat.mul_le_mul_left _ (by omega)
    omega
  have hQ : 0 < q ^ (ν * t) := pow_pos (by omega) _
  have hcard : (Finset.Icc s₀ (t - s₀)).card = M + 2 := by
    rw [Nat.card_Icc]; omega
  have h5 := hC (ν * t)
  have h6 : (Finset.Icc s₀ (t - s₀)).card * q ^ (ν * t) ≤ M * q ^ (ν * t) := by
    calc _ ≤ _ := hsum1
      _ ≤ q ^ (2 * G + 2) * effCount Fq k' (ν * t) :=
          Nat.mul_le_mul_left _ (hsum2.trans hsplit)
      _ ≤ q ^ (2 * G + 2) * (C * q ^ (ν * t)) := Nat.mul_le_mul_left _ h5
      _ = M * q ^ (ν * t) := by rw [hM]; ring
  rw [hcard] at h6
  nlinarith

end NumberFieldKB.WeilBNT.FF
