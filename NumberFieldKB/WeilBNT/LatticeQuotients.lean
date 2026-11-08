import NumberFieldKB.WeilBNT.KLatticesLocalGlobal

/-!
# Weil, *Basic Number Theory*, V.§3, Theorem 4 and Corollary 1, for $k$-lattices $L\supseteq M$ in $E=k^n$

$k$ is a number field (`K`), $\mathfrak r$ its ring of integers, $E=k^n$, $v$ runs over the finite places, and
$L_v$, $M_v$ are the closures of $L$, $M$ in $E_v$ (`localLattice`, by V.§2 Prop. 4). `LocalQuotients.lean` has the
case $E=k$, $L=\mathfrak r$ (ideals); this file is the general case.

* `latticeQuotHom L M`: Weil's $\lambda$, $\xi\mapsto(\lambda_v(\xi))_v$ from $L$ to $\prod_v L_v/M_v$; it is additive
  and $\mathfrak r$-semilinear (`latticeQuotHom_smul`).
* **Thm. 4** (p. 87): for $k$-lattices $L\supseteq M$, $\lambda$ has kernel $M$ and is surjective
  (`weil_V_3_thm4_lattice`), so $L/M\cong\prod_vL_v/M_v$ (`weil_V_3_thm4_lattice_equiv`).
* **Cor. 1** (p. 88): $[L:M]=\prod_v[L_v:M_v]$, almost all factors being $1$ (`weil_V_3_cor1_lattice`).

The statements do not assume $M\subseteq L$: $M$ enters as $M\cap L$ and $M_v\cap L_v$, which is Weil's case
when $L\supseteq M$.

*Proof* (Weil's): injectivity is Thm. 2 of §2 ($M=\bigcap_v(E\cap M_v)$, `globalOfLocal_localLattice`); for
surjectivity, $\prod_vM_v$ is open in $\prod_vL_v$ since $M_v=L_v$ for almost all $v$, and Prop. 4 of §2 gives an
element of $L$ in any coset of it (`exists_approx`).
-/

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/-- $M_v$, as an $r_v$-submodule of $L_v$. -/
abbrev relLocal (L M : Submodule (𝓞 K) (Fin n → K)) (v : HeightOneSpectrum (𝓞 K)) :
    Submodule (v.adicCompletionIntegers K) (localLattice L v) :=
  (localLattice M v).comap (localLattice L v).subtype

/-- $M\cap L$, as an $\mathfrak r$-submodule of $L$. -/
abbrev relGlobal (L M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) L :=
  M.comap L.subtype

theorem psiL_add (L : Submodule (𝓞 K) (Fin n → K)) (x y : L) (v : HeightOneSpectrum (𝓞 K)) :
    psiL L (x + y) v = psiL L x v + psiL L y v :=
  Subtype.ext (toLocal_add v (x : Fin n → K) (y : Fin n → K))

theorem psiL_smul (L : Submodule (𝓞 K) (Fin n → K)) (a : 𝓞 K) (x : L) (v : HeightOneSpectrum (𝓞 K)) :
    psiL L (a • x) v = algebraMap (𝓞 K) (v.adicCompletionIntegers K) a • psiL L x v :=
  Subtype.ext (toLocal_osmul v a (x : Fin n → K))

/-- Weil's $\lambda:L\to\prod_vL_v/M_v$, $\xi\mapsto(\lambda_v(\xi))_v$. -/
def latticeQuotHom (L M : Submodule (𝓞 K) (Fin n → K)) :
    L →+ ∀ v : HeightOneSpectrum (𝓞 K), localLattice L v ⧸ relLocal L M v :=
  AddMonoidHom.mk' (fun (l : L) (v : HeightOneSpectrum (𝓞 K)) =>
      (Submodule.Quotient.mk (psiL L l v) : localLattice L v ⧸ relLocal L M v)) fun x y => by
    funext v
    simp only [Pi.add_apply, psiL_add, Submodule.Quotient.mk_add]

/-- $\lambda$ is $\mathfrak r$-semilinear: $\lambda_v(a\xi)=a\,\lambda_v(\xi)$. -/
theorem latticeQuotHom_smul (L M : Submodule (𝓞 K) (Fin n → K)) (a : 𝓞 K) (x : L)
    (v : HeightOneSpectrum (𝓞 K)) :
    latticeQuotHom L M (a • x) v = algebraMap (𝓞 K) (v.adicCompletionIntegers K) a • latticeQuotHom L M x v := by
  simp only [latticeQuotHom, AddMonoidHom.mk'_apply, psiL_smul, Submodule.Quotient.mk_smul]

/-- **Weil, V.§3, Theorem 4** (p. 87), $E=k^n$: for $k$-lattices $L\supseteq M$, the map
$\lambda:L\to\prod_vL_v/M_v$ has kernel $M$ and is surjective. -/
@[kb "weil1973bnt" "Ch. V, §3, Thm. 4 (p. 87), E = k^n, k-lattices L ⊇ M"]
theorem weil_V_3_thm4_lattice {L M : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : IsKLattice K n M) :
    (latticeQuotHom L M).ker = (relGlobal L M).toAddSubgroup ∧ Function.Surjective (latticeQuotHom L M) := by
  constructor
  · ext l
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro h
      rw [← globalOfLocal_localLattice hM, mem_globalOfLocal]
      intro v
      have := congrFun h v
      simp only [latticeQuotHom, AddMonoidHom.mk'_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at this
      exact this
    · intro h
      funext v
      simp only [latticeQuotHom, AddMonoidHom.mk'_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
      exact toLocal_mem_localLattice M v ⟨_, h⟩
  · intro y
    have hrep : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : localLattice L v, Submodule.Quotient.mk e = y v :=
      fun v => Submodule.mkQ_surjective _ (y v)
    choose e he using hrep
    have hT : {v | localLattice M v ≠ localLattice L v}.Finite :=
      finite_of_localLattice_eq (Mloc := localLattice M) hL hM fun _ => rfl
    let U : ∀ w : HeightOneSpectrum (𝓞 K), Set (Fin n → w.adicCompletion K) :=
      fun w => {z | z - (e w : Fin n → w.adicCompletion K) ∈ localLattice M w}
    have hUo : ∀ w ∈ {v | localLattice M v ≠ localLattice L v}, IsOpen (U w) := fun w _ =>
      (isLocalLattice_localLattice hM w).2.preimage (continuous_id.sub continuous_const)
    have hUne : ∀ w ∈ {v | localLattice M v ≠ localLattice L v},
        ∃ z ∈ U w, z ∈ localLattice L w := fun w _ =>
      ⟨e w, by
        show (e w : Fin n → w.adicCompletion K) - (e w : Fin n → w.adicCompletion K) ∈ localLattice M w
        rw [sub_self]; exact zero_mem _, (e w).2⟩
    obtain ⟨x, hxL, hxU⟩ := exists_approx hL hT U hUo hUne
    refine ⟨⟨x, hxL⟩, funext fun w => ?_⟩
    rw [← he w]
    simp only [latticeQuotHom, AddMonoidHom.mk'_apply]
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]
    by_cases hw : localLattice M w ≠ localLattice L w
    · exact hxU w hw
    · rw [not_not.mp hw]
      exact sub_mem (toLocal_mem_localLattice L w ⟨x, hxL⟩) (e w).2

/-- **Weil, V.§3, Theorem 4**, as an isomorphism $L/M\cong\prod_vL_v/M_v$ of additive groups (it is
$\mathfrak r$-semilinear by `latticeQuotHom_smul`). -/
def weil_V_3_thm4_lattice_equiv {L M : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : IsKLattice K n M) :
    L ⧸ (relGlobal L M).toAddSubgroup ≃+ ∀ v : HeightOneSpectrum (𝓞 K), localLattice L v ⧸ relLocal L M v :=
  (QuotientAddGroup.quotientAddEquivOfEq (weil_V_3_thm4_lattice hL hM).1.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (weil_V_3_thm4_lattice hL hM).2)

theorem weil_V_3_thm4_lattice_equiv_mk {L M : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : IsKLattice K n M) (x : L) :
    weil_V_3_thm4_lattice_equiv hL hM (QuotientAddGroup.mk x) = latticeQuotHom L M x :=
  rfl

/-- **Weil, V.§3, Corollary 1 of Theorem 4** (p. 88), $E=k^n$: for $k$-lattices $L\supseteq M$,
$[L:M]=\prod_v[L_v:M_v]$, and $[L_v:M_v]=1$ for almost all $v$. -/
@[kb "weil1973bnt" "Ch. V, §3, Cor. 1 of Thm. 4 (p. 88), E = k^n, k-lattices L ⊇ M"]
theorem weil_V_3_cor1_lattice {L M : Submodule (𝓞 K) (Fin n → K)} (hL : IsKLattice K n L)
    (hM : IsKLattice K n M) :
    {v : HeightOneSpectrum (𝓞 K) | Nat.card (localLattice L v ⧸ relLocal L M v) ≠ 1}.Finite ∧
      Nat.card (L ⧸ (relGlobal L M).toAddSubgroup) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), Nat.card (localLattice L v ⧸ relLocal L M v) := by
  classical
  have hT : {v | localLattice M v ≠ localLattice L v}.Finite :=
    finite_of_localLattice_eq (Mloc := localLattice M) hL hM fun _ => rfl
  have hss : ∀ v, ¬ (localLattice M v ≠ localLattice L v) →
      Subsingleton (localLattice L v ⧸ relLocal L M v) := by
    intro v hv
    have h := not_not.mp hv
    have htop : relLocal L M v = ⊤ := by
      show (localLattice M v).comap (localLattice L v).subtype = ⊤
      rw [h]
      exact Submodule.comap_subtype_self _
    exact Submodule.Quotient.subsingleton_iff.mpr htop
  have hone : ∀ v, ¬ (localLattice M v ≠ localLattice L v) →
      Nat.card (localLattice L v ⧸ relLocal L M v) = 1 := by
    intro v hv
    have := hss v hv
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨this, inferInstance⟩
  have hsub : {v : HeightOneSpectrum (𝓞 K) | Nat.card (localLattice L v ⧸ relLocal L M v) ≠ 1} ⊆
      {v | localLattice M v ≠ localLattice L v} := fun v hv => by
    by_contra h; exact hv (hone v h)
  refine ⟨hT.subset hsub, ?_⟩
  set S := hT.toFinset with hS
  have h2 : Nat.card (∀ v : {v // v ∉ S}, localLattice L v.1 ⧸ relLocal L M v.1) = 1 := by
    have : ∀ v : {v // v ∉ S}, Subsingleton (localLattice L v.1 ⧸ relLocal L M v.1) :=
      fun v => hss v.1 fun h => v.2 (hT.mem_toFinset.mpr h)
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, inferInstance⟩
  rw [Nat.card_congr (weil_V_3_thm4_lattice_equiv hL hM).toEquiv,
    Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) _), Nat.card_prod, h2, mul_one,
    Nat.card_pi]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · exact Finset.prod_coe_sort S (fun v => Nat.card (localLattice L v ⧸ relLocal L M v))
  · intro v hv
    rw [Set.Finite.coe_toFinset]
    exact hsub hv

end NumberFieldKB.WeilBNT
